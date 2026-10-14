//! Move stackless `Constant` -> IR `Const` translator.
//!
//! Pure data transformation, no `ProgramBuilder` needed: Move
//! constants are limited to primitives plus homogeneous arrays of
//! primitives -- no struct constants exist in Move.
//!
//! ## Element-type inference for `Constant::Vector`
//!
//! Move's `Constant::Vector(elements)` doesn't carry an explicit
//! element type; the type is implicit in the bytecode's use site.
//! We infer it as follows, in priority order:
//!
//! 1. **First-element inference** -- if the vector is non-empty, the
//!    element type is read off the first translated `Const`.
//! 2. **Type-hint** -- callers that know the expected vector type
//!    (the bytecode's recorded result type for the `Load`)
//!    pass it via [`translate_constant_with_type`]; we read the
//!    element type from a `Type::Vector(inner)` hint when the vector
//!    is empty.
//! 3. **Fallback** -- if neither (1) nor (2) succeeds (empty vector,
//!    no hint), default to `UInt(8)`. Practically this only fires
//!    for synthesised empty `vector<u8>` constants the upstream
//!    optimizer emits; non-`u8` empty vectors must reach us with a
//!    type hint.
//!
//! Mirrors the legacy `translation::mod::convert_constant_inner`
//! policy at
//! `lean-backend/crates/stackless-to-intermediate/src/translation/mod.rs`.

use ethnum::U256;
use move_stackless_bytecode::stackless_bytecode::Constant;

use crate::ir::{Const, Type};

/// Translate a Move `Constant` to IR [`Const`].
///
/// For `Constant::Vector(elements)` with no first-element to infer
/// from (i.e. empty vector), the element type defaults to `UInt(8)`.
/// Callers that know the expected vector type should use
/// [`translate_constant_with_type`] instead.
pub fn translate_constant(c: &Constant) -> Const {
    translate_constant_inner(c, None)
}

/// Translate a Move `Constant` to IR [`Const`] using `expected_type`
/// to disambiguate empty vectors.
///
/// `expected_type` is consulted only when the vector is empty AND
/// `expected_type` is `Type::Vector(inner)`. In every other case
/// it's ignored -- non-empty vectors infer from the first element,
/// and non-vector constants are unambiguous.
pub fn translate_constant_with_type(c: &Constant, expected_type: &Type) -> Const {
    translate_constant_inner(c, Some(expected_type))
}

fn translate_constant_inner(c: &Constant, expected_type: Option<&Type>) -> Const {
    match c {
        Constant::Bool(b) => Const::Bool(*b),
        Constant::U8(v) => uint_const(8, U256::from(*v)),
        Constant::U16(v) => uint_const(16, U256::from(*v)),
        Constant::U32(v) => uint_const(32, U256::from(*v)),
        Constant::U64(v) => uint_const(64, U256::from(*v)),
        Constant::U128(v) => uint_const(128, U256::from(*v)),
        Constant::U256(v) => uint_const(256, *v),
        Constant::Address(addr) => Const::Address(addr.clone()),
        Constant::ByteArray(bytes) => Const::Vector {
            elem_type: Type::UInt(8),
            elems: bytes
                .iter()
                .map(|&b| uint_const(8, U256::from(b)))
                .collect(),
        },
        Constant::AddressArray(addresses) => Const::Vector {
            elem_type: Type::Address,
            elems: addresses
                .iter()
                .map(|addr| Const::Address(addr.clone()))
                .collect(),
        },
        Constant::Vector(elements) => {
            let elems: Vec<Const> = elements.iter().map(translate_constant).collect();
            let elem_type = if let Some(first) = elems.first() {
                infer_const_type(first)
            } else if let Some(Type::Vector(inner)) = expected_type {
                (**inner).clone()
            } else {
                Type::UInt(8)
            };
            Const::Vector { elem_type, elems }
        }
    }
}

fn uint_const(bits: u32, value: U256) -> Const {
    Const::UInt { bits, value }
}

/// Infer the [`Type`] from a translated [`Const`]. Used by the empty-
/// vector inference path.
fn infer_const_type(c: &Const) -> Type {
    match c {
        Const::Bool(_) => Type::Bool,
        Const::UInt { bits, .. } => Type::UInt(*bits),
        Const::Address(_) => Type::Address,
        Const::Vector { elem_type, .. } => Type::Vector(Box::new(elem_type.clone())),
        Const::Unit => Type::Unit,
        Const::Default(ty) => ty.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num::BigUint;

    // ---- Booleans -----------------------------------------------------

    #[test]
    fn bool_true_translates() {
        assert_eq!(translate_constant(&Constant::Bool(true)), Const::Bool(true));
    }

    #[test]
    fn bool_false_translates() {
        assert_eq!(
            translate_constant(&Constant::Bool(false)),
            Const::Bool(false)
        );
    }

    // ---- Unsigned integers --------------------------------------------

    #[test]
    fn u8_translates_with_8_bit_width() {
        let got = translate_constant(&Constant::U8(7));
        assert_eq!(
            got,
            Const::UInt {
                bits: 8,
                value: U256::from(7u8)
            }
        );
    }

    #[test]
    fn u16_translates_with_16_bit_width() {
        let got = translate_constant(&Constant::U16(0xCAFE));
        assert_eq!(
            got,
            Const::UInt {
                bits: 16,
                value: U256::from(0xCAFEu16)
            }
        );
    }

    #[test]
    fn u32_translates_with_32_bit_width() {
        let got = translate_constant(&Constant::U32(0xDEADBEEF));
        assert_eq!(
            got,
            Const::UInt {
                bits: 32,
                value: U256::from(0xDEADBEEFu32)
            }
        );
    }

    #[test]
    fn u64_translates_with_64_bit_width() {
        let got = translate_constant(&Constant::U64(1_234_567_890_123));
        assert_eq!(
            got,
            Const::UInt {
                bits: 64,
                value: U256::from(1_234_567_890_123u64)
            }
        );
    }

    #[test]
    fn u128_translates_with_128_bit_width() {
        let got = translate_constant(&Constant::U128(u128::MAX));
        assert_eq!(
            got,
            Const::UInt {
                bits: 128,
                value: U256::from(u128::MAX)
            }
        );
    }

    #[test]
    fn u256_max_translates_at_full_width() {
        let max = U256::MAX;
        let got = translate_constant(&Constant::U256(max));
        assert_eq!(
            got,
            Const::UInt {
                bits: 256,
                value: max
            }
        );
    }

    #[test]
    fn u8_max_round_trips() {
        let got = translate_constant(&Constant::U8(u8::MAX));
        match got {
            Const::UInt { bits: 8, value } => assert_eq!(value, U256::from(u8::MAX)),
            other => panic!("expected u8 const, got {other:?}"),
        }
    }

    // ---- Address ------------------------------------------------------

    #[test]
    fn address_clones_underlying_bigint() {
        let addr = BigUint::from(0x42u8);
        let got = translate_constant(&Constant::Address(addr.clone()));
        assert_eq!(got, Const::Address(addr));
    }

    // ---- ByteArray ----------------------------------------------------

    #[test]
    fn byte_array_translates_to_vector_of_u8() {
        let got = translate_constant(&Constant::ByteArray(vec![1, 2, 3]));
        match got {
            Const::Vector { elem_type, elems } => {
                assert_eq!(elem_type, Type::UInt(8));
                assert_eq!(elems.len(), 3);
                for (i, e) in elems.iter().enumerate() {
                    match e {
                        Const::UInt { bits: 8, value } => {
                            assert_eq!(*value, U256::from((i + 1) as u8))
                        }
                        other => panic!("expected u8 element, got {other:?}"),
                    }
                }
            }
            other => panic!("expected Vector, got {other:?}"),
        }
    }

    #[test]
    fn empty_byte_array_translates_to_empty_u8_vector() {
        let got = translate_constant(&Constant::ByteArray(vec![]));
        assert_eq!(
            got,
            Const::Vector {
                elem_type: Type::UInt(8),
                elems: vec![]
            }
        );
    }

    // ---- AddressArray -------------------------------------------------

    #[test]
    fn address_array_translates_to_vector_of_address() {
        let a = BigUint::from(1u8);
        let b = BigUint::from(2u8);
        let got = translate_constant(&Constant::AddressArray(vec![a.clone(), b.clone()]));
        assert_eq!(
            got,
            Const::Vector {
                elem_type: Type::Address,
                elems: vec![Const::Address(a), Const::Address(b)],
            }
        );
    }

    #[test]
    fn empty_address_array_translates_to_empty_address_vector() {
        let got = translate_constant(&Constant::AddressArray(vec![]));
        assert_eq!(
            got,
            Const::Vector {
                elem_type: Type::Address,
                elems: vec![]
            }
        );
    }

    // ---- Vector with element-type inference --------------------------

    #[test]
    fn nonempty_vector_infers_from_first_element() {
        let got = translate_constant(&Constant::Vector(vec![
            Constant::U64(1),
            Constant::U64(2),
            Constant::U64(3),
        ]));
        match got {
            Const::Vector { elem_type, elems } => {
                assert_eq!(elem_type, Type::UInt(64));
                assert_eq!(elems.len(), 3);
            }
            other => panic!("expected Vector, got {other:?}"),
        }
    }

    #[test]
    fn nonempty_vector_of_bools_infers_bool() {
        let got = translate_constant(&Constant::Vector(vec![
            Constant::Bool(true),
            Constant::Bool(false),
        ]));
        match got {
            Const::Vector { elem_type, elems } => {
                assert_eq!(elem_type, Type::Bool);
                assert_eq!(elems, vec![Const::Bool(true), Const::Bool(false)]);
            }
            other => panic!("expected Vector, got {other:?}"),
        }
    }

    #[test]
    fn empty_vector_with_type_hint_uses_hint() {
        let got = translate_constant_with_type(
            &Constant::Vector(vec![]),
            &Type::Vector(Box::new(Type::UInt(64))),
        );
        assert_eq!(
            got,
            Const::Vector {
                elem_type: Type::UInt(64),
                elems: vec![]
            }
        );
    }

    #[test]
    fn empty_vector_without_hint_defaults_to_u8() {
        let got = translate_constant(&Constant::Vector(vec![]));
        assert_eq!(
            got,
            Const::Vector {
                elem_type: Type::UInt(8),
                elems: vec![]
            }
        );
    }

    #[test]
    fn empty_vector_with_non_vector_hint_falls_back_to_u8() {
        // If the hint isn't Type::Vector(_), it's ignored and we
        // fall back to the default. The bytecode shouldn't produce
        // this case in practice, but the policy is: don't crash, use
        // the conservative default.
        let got = translate_constant_with_type(&Constant::Vector(vec![]), &Type::UInt(64));
        assert_eq!(
            got,
            Const::Vector {
                elem_type: Type::UInt(8),
                elems: vec![]
            }
        );
    }

    #[test]
    fn nested_vector_translates_recursively() {
        // vector<vector<u8>> = [[1, 2], [3]]
        let got = translate_constant(&Constant::Vector(vec![
            Constant::Vector(vec![Constant::U8(1), Constant::U8(2)]),
            Constant::Vector(vec![Constant::U8(3)]),
        ]));
        match got {
            Const::Vector {
                elem_type: outer_ty,
                elems,
            } => {
                // Inferred from first element: vector<u8>
                assert_eq!(outer_ty, Type::Vector(Box::new(Type::UInt(8))));
                assert_eq!(elems.len(), 2);
                for inner in &elems {
                    match inner {
                        Const::Vector { elem_type, .. } => assert_eq!(*elem_type, Type::UInt(8)),
                        other => panic!("expected inner Vector, got {other:?}"),
                    }
                }
            }
            other => panic!("expected outer Vector, got {other:?}"),
        }
    }

    // ---- Determinism --------------------------------------------------

    #[test]
    fn determinism_same_input_same_output() {
        let c = Constant::Vector(vec![Constant::U64(1), Constant::U64(2), Constant::U64(3)]);
        let r1 = translate_constant(&c);
        let r2 = translate_constant(&c);
        assert_eq!(r1, r2);
    }

    // ---- infer_const_type unit tests ---------------------------------

    #[test]
    fn infer_const_type_recognises_each_const_variant() {
        assert_eq!(infer_const_type(&Const::Bool(true)), Type::Bool);
        assert_eq!(
            infer_const_type(&Const::UInt {
                bits: 64,
                value: U256::from(1u8)
            }),
            Type::UInt(64)
        );
        assert_eq!(
            infer_const_type(&Const::Address(BigUint::from(0u8))),
            Type::Address
        );
        assert_eq!(
            infer_const_type(&Const::Vector {
                elem_type: Type::Bool,
                elems: vec![]
            }),
            Type::Vector(Box::new(Type::Bool))
        );
        assert_eq!(infer_const_type(&Const::Unit), Type::Unit);
    }
}
