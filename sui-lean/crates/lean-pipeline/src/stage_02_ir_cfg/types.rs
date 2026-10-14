//! Move type -> IR `Type` translator.
//!
//! Pure data transformation: takes a [`move_model::ty::Type`] and a
//! [`ProgramBuilder`] (for struct id allocation), returns a
//! [`crate::ir::Type`]. Used by every stage-2 sub-pass that needs
//! to lift Move-side types into IR types -- function signatures,
//! struct fields, parameter declarations, the per-bytecode op
//! translator.
//!
//! ## Design notes
//!
//! - **Signer collapses to Address.** Move's `signer` primitive is
//!   semantically equivalent to `address` for our purposes; the
//!   prelude has no separate `Signer` type. Mirrors the legacy
//!   `convert_type` policy at
//!   `lean-backend/crates/stackless-to-intermediate/src/program_builder.rs`.
//!
//! - **`MutableReference(T)` -> `Type::MutableRef { inner: T, root: T }`.**
//!   At type-translation time we don't know the borrow chain's source
//!   (that's the BorrowState pass's job). The honest convention is
//!   `root = inner` -- which also matches the function-parameter case
//!   where the parameter itself is the borrow source. Stage 3's demut
//!   pass strips the wrapper regardless of whether `root == inner`.
//!
//! - **`Datatype(mid, did, args)` -> `Type::Struct { struct_id, type_args }`.**
//!   Allocates a `StructId` via `prog.struct_id(qid)`, recursing into
//!   `args` for the type parameters. Works for both structs and enums
//!   -- our IR collapses them into one `Struct` shape with optional
//!   `variants`.
//!
//! - **Unsupported types reject with a specific error.** Spec-only
//!   types (`Num`, `Range`, `EventStore`, `Fun`, `TypeDomain`,
//!   `ResourceDomain`) and type-checking temporaries (`Var`, `Error`)
//!   produce [`Stage2Error::UnsupportedMoveType`]. We do NOT silently
//!   substitute -- if one of these appears in real bytecode, that's a
//!   pipeline bug stage 2 must surface.

use move_model::ty::{PrimitiveType, Type as MoveType};

use crate::ir::{ProgramBuilder, Type};

use super::Stage2Error;

/// Translate a Move type to an IR [`Type`].
///
/// Recursive: nested types (vectors, references, struct type args,
/// tuple elements) are translated by calling back into `translate_type`.
/// `prog` is consulted for struct id allocation; the same struct
/// referenced multiple times resolves to the same id.
pub fn translate_type(ty: &MoveType, prog: &mut ProgramBuilder) -> Result<Type, Stage2Error> {
    match ty {
        // ---- Primitives ------------------------------------------------
        MoveType::Primitive(PrimitiveType::Bool) => Ok(Type::Bool),
        MoveType::Primitive(PrimitiveType::U8) => Ok(Type::UInt(8)),
        MoveType::Primitive(PrimitiveType::U16) => Ok(Type::UInt(16)),
        MoveType::Primitive(PrimitiveType::U32) => Ok(Type::UInt(32)),
        MoveType::Primitive(PrimitiveType::U64) => Ok(Type::UInt(64)),
        MoveType::Primitive(PrimitiveType::U128) => Ok(Type::UInt(128)),
        MoveType::Primitive(PrimitiveType::U256) => Ok(Type::UInt(256)),
        MoveType::Primitive(PrimitiveType::Address | PrimitiveType::Signer) => Ok(Type::Address),

        // ---- Spec-only primitives -------------------------------------
        MoveType::Primitive(PrimitiveType::Num) => unsupported("Primitive(Num)"),
        MoveType::Primitive(PrimitiveType::Range) => unsupported("Primitive(Range)"),
        MoveType::Primitive(PrimitiveType::EventStore) => unsupported("Primitive(EventStore)"),

        // ---- Compound: vector, tuple ---------------------------------
        MoveType::Vector(inner) => Ok(Type::Vector(Box::new(translate_type(inner, prog)?))),
        MoveType::Tuple(elems) => {
            let mut out = Vec::with_capacity(elems.len());
            for t in elems {
                out.push(translate_type(t, prog)?);
            }
            Ok(Type::Tuple(out))
        }

        // ---- References: & and &mut -----------------------------------
        MoveType::Reference(is_mut, inner) => {
            let inner_ty = translate_type(inner, prog)?;
            if *is_mut {
                // `root = inner` at type-translation time. The borrow
                // tracker fills in a more specific `root` for temps
                // produced by projected borrows; here we honour the
                // convention that `&mut T` declared on a param is its
                // own borrow source, so `root` is `T`.
                Ok(Type::MutableRef {
                    inner: Box::new(inner_ty.clone()),
                    root: Box::new(inner_ty),
                })
            } else {
                Ok(Type::Reference(Box::new(inner_ty)))
            }
        }

        // ---- Struct / enum (Datatype is the unified Move shape) -------
        MoveType::Datatype(module_id, datatype_id, args) => {
            let qid = move_model::model::QualifiedId {
                module_id: *module_id,
                id: *datatype_id,
            };
            let struct_id = prog.struct_id(qid);
            let mut type_args = Vec::with_capacity(args.len());
            for a in args {
                type_args.push(translate_type(a, prog)?);
            }
            Ok(Type::Struct {
                struct_id,
                type_args,
            })
        }

        // ---- Type parameter -------------------------------------------
        MoveType::TypeParameter(idx) => Ok(Type::TypeParam(*idx)),

        // ---- Spec-only and tc-temporary variants ----------------------
        MoveType::Fun(_, _) => unsupported("Fun(_,_)"),
        MoveType::TypeDomain(_) => unsupported("TypeDomain(_)"),
        MoveType::ResourceDomain(_, _, _) => unsupported("ResourceDomain(_,_,_)"),
        MoveType::Error => unsupported("Error"),
        MoveType::Var(_) => unsupported("Var(_)"),
    }
}

fn unsupported(description: &str) -> Result<Type, Stage2Error> {
    Err(Stage2Error::UnsupportedMoveType {
        description: description.to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use move_model::model::{DatatypeId, ModuleId};
    use move_model::symbol::SymbolPool;

    fn pb() -> ProgramBuilder {
        ProgramBuilder::new()
    }

    // ---- Primitive translation ----------------------------------------

    #[test]
    fn bool_translates() {
        assert_eq!(
            translate_type(&MoveType::Primitive(PrimitiveType::Bool), &mut pb()).unwrap(),
            Type::Bool
        );
    }

    #[test]
    fn each_uint_width_translates() {
        let widths = [
            (PrimitiveType::U8, 8u32),
            (PrimitiveType::U16, 16),
            (PrimitiveType::U32, 32),
            (PrimitiveType::U64, 64),
            (PrimitiveType::U128, 128),
            (PrimitiveType::U256, 256),
        ];
        for (mp, expected_bits) in widths {
            let got = translate_type(&MoveType::Primitive(mp), &mut pb()).unwrap();
            assert_eq!(got, Type::UInt(expected_bits), "for {mp:?}");
        }
    }

    #[test]
    fn address_translates() {
        assert_eq!(
            translate_type(&MoveType::Primitive(PrimitiveType::Address), &mut pb()).unwrap(),
            Type::Address
        );
    }

    #[test]
    fn signer_collapses_to_address() {
        // Move's `signer` has no separate IR type -- the prelude
        // treats it as Address. Mirror legacy policy.
        assert_eq!(
            translate_type(&MoveType::Primitive(PrimitiveType::Signer), &mut pb()).unwrap(),
            Type::Address
        );
    }

    // ---- Compound -----------------------------------------------------

    #[test]
    fn vector_of_primitive_translates() {
        let mty = MoveType::Vector(Box::new(MoveType::Primitive(PrimitiveType::U64)));
        assert_eq!(
            translate_type(&mty, &mut pb()).unwrap(),
            Type::Vector(Box::new(Type::UInt(64)))
        );
    }

    #[test]
    fn nested_vector_translates() {
        let mty = MoveType::Vector(Box::new(MoveType::Vector(Box::new(MoveType::Primitive(
            PrimitiveType::U8,
        )))));
        assert_eq!(
            translate_type(&mty, &mut pb()).unwrap(),
            Type::Vector(Box::new(Type::Vector(Box::new(Type::UInt(8)))))
        );
    }

    #[test]
    fn tuple_translates_elementwise() {
        let mty = MoveType::Tuple(vec![
            MoveType::Primitive(PrimitiveType::Bool),
            MoveType::Primitive(PrimitiveType::U64),
        ]);
        assert_eq!(
            translate_type(&mty, &mut pb()).unwrap(),
            Type::Tuple(vec![Type::Bool, Type::UInt(64)])
        );
    }

    #[test]
    fn empty_tuple_translates_to_empty_tuple() {
        // Note: our IR has both `Type::Unit` (explicit) and
        // `Type::Tuple(vec![])`. The translator preserves the Move
        // shape -- empty tuple in stays empty tuple out. Callers that
        // want the canonical `Type::Unit` for unit returns should
        // normalize separately (see e.g. function signature lifting).
        let mty = MoveType::Tuple(vec![]);
        assert_eq!(
            translate_type(&mty, &mut pb()).unwrap(),
            Type::Tuple(vec![])
        );
    }

    // ---- References ---------------------------------------------------

    #[test]
    fn immutable_reference_translates() {
        let mty = MoveType::Reference(false, Box::new(MoveType::Primitive(PrimitiveType::U64)));
        assert_eq!(
            translate_type(&mty, &mut pb()).unwrap(),
            Type::Reference(Box::new(Type::UInt(64)))
        );
    }

    #[test]
    fn mutable_reference_translates_with_inner_equal_root() {
        let mty = MoveType::Reference(true, Box::new(MoveType::Primitive(PrimitiveType::U64)));
        let got = translate_type(&mty, &mut pb()).unwrap();
        match got {
            Type::MutableRef { inner, root } => {
                assert_eq!(*inner, Type::UInt(64));
                assert_eq!(*root, Type::UInt(64));
            }
            other => panic!("expected MutableRef, got {other:?}"),
        }
    }

    #[test]
    fn nested_mutable_reference_translates() {
        // &mut vector<u64>
        let mty = MoveType::Reference(
            true,
            Box::new(MoveType::Vector(Box::new(MoveType::Primitive(
                PrimitiveType::U64,
            )))),
        );
        let got = translate_type(&mty, &mut pb()).unwrap();
        let expected_inner = Type::Vector(Box::new(Type::UInt(64)));
        match got {
            Type::MutableRef { inner, root } => {
                assert_eq!(*inner, expected_inner);
                assert_eq!(*root, expected_inner);
            }
            other => panic!("expected MutableRef, got {other:?}"),
        }
    }

    // ---- Type parameters ---------------------------------------------

    #[test]
    fn type_parameter_preserves_index() {
        for idx in [0u16, 1, 2, 7, 42] {
            let got = translate_type(&MoveType::TypeParameter(idx), &mut pb()).unwrap();
            assert_eq!(got, Type::TypeParam(idx));
        }
    }

    // ---- Struct / Datatype --------------------------------------------

    fn datatype(pool: &SymbolPool, m: usize, name: &str, args: Vec<MoveType>) -> MoveType {
        MoveType::Datatype(ModuleId::new(m), DatatypeId::new(pool.make(name)), args)
    }

    #[test]
    fn datatype_allocates_struct_id() {
        let pool = SymbolPool::new();
        let mty = datatype(&pool, 0, "Pool", vec![]);
        let mut prog = pb();
        let got = translate_type(&mty, &mut prog).unwrap();
        let expected_id = 0; // first allocation in a fresh builder
        assert_eq!(
            got,
            Type::Struct {
                struct_id: expected_id,
                type_args: vec![],
            }
        );
        assert!(prog.program().structs.contains_key(&expected_id));
    }

    #[test]
    fn datatype_with_type_args_translates_recursively() {
        let pool = SymbolPool::new();
        // Coin<u64>
        let mty = datatype(
            &pool,
            0,
            "Coin",
            vec![MoveType::Primitive(PrimitiveType::U64)],
        );
        let mut prog = pb();
        let got = translate_type(&mty, &mut prog).unwrap();
        match got {
            Type::Struct {
                struct_id: _,
                type_args,
            } => {
                assert_eq!(type_args, vec![Type::UInt(64)]);
            }
            other => panic!("expected Struct, got {other:?}"),
        }
    }

    #[test]
    fn datatype_translation_is_idempotent_on_struct_id() {
        // Translating the same Datatype twice yields the same StructId.
        let pool = SymbolPool::new();
        let mty = datatype(&pool, 0, "Pool", vec![]);
        let mut prog = pb();
        let id1 = match translate_type(&mty, &mut prog).unwrap() {
            Type::Struct { struct_id, .. } => struct_id,
            _ => unreachable!(),
        };
        let id2 = match translate_type(&mty, &mut prog).unwrap() {
            Type::Struct { struct_id, .. } => struct_id,
            _ => unreachable!(),
        };
        assert_eq!(id1, id2);
    }

    #[test]
    fn distinct_datatypes_get_distinct_struct_ids() {
        let pool = SymbolPool::new();
        let pool_ty = datatype(&pool, 0, "Pool", vec![]);
        let vault_ty = datatype(&pool, 0, "Vault", vec![]);
        let mut prog = pb();
        let pool_id = match translate_type(&pool_ty, &mut prog).unwrap() {
            Type::Struct { struct_id, .. } => struct_id,
            _ => unreachable!(),
        };
        let vault_id = match translate_type(&vault_ty, &mut prog).unwrap() {
            Type::Struct { struct_id, .. } => struct_id,
            _ => unreachable!(),
        };
        assert_ne!(pool_id, vault_id);
    }

    // ---- Nested generics (regression for stage-2 inventory) -----------

    #[test]
    fn vector_of_tuple_with_type_param_translates() {
        // Vector<(u64, T)> -- shape stage 3 / 8 will see for dynamic
        // field decomposition.
        let mty = MoveType::Vector(Box::new(MoveType::Tuple(vec![
            MoveType::Primitive(PrimitiveType::U64),
            MoveType::TypeParameter(0),
        ])));
        let got = translate_type(&mty, &mut pb()).unwrap();
        assert_eq!(
            got,
            Type::Vector(Box::new(Type::Tuple(vec![
                Type::UInt(64),
                Type::TypeParam(0)
            ])))
        );
    }

    #[test]
    fn generic_struct_with_nested_generic_type_arg_translates() {
        // Pool<Vector<T>>
        let pool = SymbolPool::new();
        let inner_vec = MoveType::Vector(Box::new(MoveType::TypeParameter(0)));
        let mty = datatype(&pool, 0, "Pool", vec![inner_vec.clone()]);
        let mut prog = pb();
        let got = translate_type(&mty, &mut prog).unwrap();
        match got {
            Type::Struct { type_args, .. } => {
                assert_eq!(type_args.len(), 1);
                assert_eq!(type_args[0], Type::Vector(Box::new(Type::TypeParam(0))));
            }
            other => panic!("expected Struct, got {other:?}"),
        }
    }

    // ---- Unsupported types --------------------------------------------

    #[test]
    fn num_primitive_rejects_with_unsupported() {
        let err = translate_type(&MoveType::Primitive(PrimitiveType::Num), &mut pb()).unwrap_err();
        match err {
            Stage2Error::UnsupportedMoveType { description } => {
                assert!(
                    description.contains("Num"),
                    "got description: {description}"
                );
            }
            other => panic!("expected UnsupportedMoveType, got {other:?}"),
        }
    }

    #[test]
    fn range_primitive_rejects_with_unsupported() {
        assert!(matches!(
            translate_type(&MoveType::Primitive(PrimitiveType::Range), &mut pb()),
            Err(Stage2Error::UnsupportedMoveType { .. })
        ));
    }

    #[test]
    fn event_store_primitive_rejects_with_unsupported() {
        assert!(matches!(
            translate_type(&MoveType::Primitive(PrimitiveType::EventStore), &mut pb()),
            Err(Stage2Error::UnsupportedMoveType { .. })
        ));
    }

    #[test]
    fn fun_type_rejects_with_unsupported() {
        let mty = MoveType::Fun(
            vec![MoveType::Primitive(PrimitiveType::U64)],
            Box::new(MoveType::Primitive(PrimitiveType::Bool)),
        );
        assert!(matches!(
            translate_type(&mty, &mut pb()),
            Err(Stage2Error::UnsupportedMoveType { .. })
        ));
    }

    #[test]
    fn type_domain_rejects_with_unsupported() {
        let mty = MoveType::TypeDomain(Box::new(MoveType::Primitive(PrimitiveType::U64)));
        assert!(matches!(
            translate_type(&mty, &mut pb()),
            Err(Stage2Error::UnsupportedMoveType { .. })
        ));
    }

    #[test]
    fn type_check_temporaries_reject_with_unsupported() {
        assert!(matches!(
            translate_type(&MoveType::Error, &mut pb()),
            Err(Stage2Error::UnsupportedMoveType { .. })
        ));
        assert!(matches!(
            translate_type(&MoveType::Var(0), &mut pb()),
            Err(Stage2Error::UnsupportedMoveType { .. })
        ));
    }

    // ---- Determinism --------------------------------------------------

    #[test]
    fn determinism_same_input_same_output() {
        let pool = SymbolPool::new();
        let mty = MoveType::Tuple(vec![
            MoveType::Primitive(PrimitiveType::U64),
            datatype(&pool, 0, "Pool", vec![MoveType::TypeParameter(0)]),
        ]);
        let t1 = translate_type(&mty, &mut pb()).unwrap();
        let t2 = translate_type(&mty, &mut pb()).unwrap();
        assert_eq!(t1, t2);
    }
}
