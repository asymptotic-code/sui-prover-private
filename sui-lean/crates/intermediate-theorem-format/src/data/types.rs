// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Type system for TheoremIR

use crate::StructID;
use std::rc::Rc;

/// Temporary value identifier
pub type TempId = Rc<str>;

/// Theorem IR type with enriched metadata for code generation
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// Boolean - computational boolean type (rendered as Bool in Lean)
    Bool,
    /// Proposition - logical type for specifications (rendered as Prop in Lean)
    /// Used in .aborts, .requires, .ensures functions
    Prop,
    /// Unsigned integer with bit width
    UInt(u32),
    /// Address
    Address,
    /// Struct type
    /// Names are looked up via NameManager during rendering
    Struct {
        /// Unique struct ID in the TheoremProgram
        /// Used to lookup names via NameManager and struct definitions
        struct_id: StructID,
        /// Type arguments (for generics like Coin<SUI>)
        type_args: Vec<Type>,
    },
    /// Vector of elements
    Vector(Box<Type>),
    /// Reference (immutable)
    Reference(Box<Type>),
    /// Mutable reference — inner type + state type for Lean's Mutable wrapper
    MutableReference(Box<Type>, Box<Type>),
    /// Type parameter
    TypeParameter(u16),
    /// Tuple
    Tuple(Vec<Type>),
    /// Option type (for while-loop early return encoding)
    Option(Box<Type>),
    /// Synthetic intrinsic referencing `MoveAbort` from `Prelude/MoveAbort.lean`.
    /// Only used by the test-mode `.aborts` lowering, where companion functions
    /// return `Option MoveAbort`. The renderer emits the literal `MoveAbort`
    /// type name without namespace qualification.
    MoveAbort,
}

impl Type {
    /// Collect all struct IDs referenced in this type
    pub fn struct_ids(&self) -> Vec<StructID> {
        let mut ids = Vec::new();
        self.collect_struct_ids(&mut ids);
        ids
    }

    fn collect_struct_ids(&self, ids: &mut Vec<StructID>) {
        match self {
            Type::Struct {
                struct_id,
                type_args,
            } => {
                ids.push(*struct_id);
                type_args.iter().for_each(|t| t.collect_struct_ids(ids));
            }
            Type::Vector(inner)
            | Type::Reference(inner)
            | Type::MutableReference(inner, _)
            | Type::Option(inner) => {
                inner.collect_struct_ids(ids);
            }
            Type::Tuple(tys) => {
                tys.iter().for_each(|t| t.collect_struct_ids(ids));
            }
            Type::Bool
            | Type::Prop
            | Type::UInt(_)
            | Type::Address
            | Type::TypeParameter(_)
            | Type::MoveAbort => {}
        }
    }

    /// Check if this type contains MutableReference anywhere (including in tuples)
    pub fn contains_mutable_ref(&self) -> bool {
        match self {
            Type::MutableReference(_, _) => true,
            Type::Tuple(elems) => elems.iter().any(|t| t.contains_mutable_ref()),
            _ => false,
        }
    }

    /// Strip MutableReference wrappers: MutableReference(T, _) → T.
    /// Recurses into tuples so augmented return types like
    /// Tuple(MutableReference(T, S), S1) become Tuple(T, S1).
    pub fn strip_mutable_ref(self) -> Type {
        match self {
            Type::MutableReference(inner, _) => *inner,
            Type::Tuple(elems) => {
                Type::Tuple(elems.into_iter().map(|t| t.strip_mutable_ref()).collect())
            }
            other => other,
        }
    }

    /// Check if this type contains Bool anywhere (including in tuples)
    /// Bool becomes Prop in Lean, which affects Decidable instance derivation
    pub fn contains_bool(&self) -> bool {
        match self {
            Type::Bool => true,
            Type::Tuple(tys) => tys.iter().any(|t| t.contains_bool()),
            Type::Vector(inner)
            | Type::Reference(inner)
            | Type::MutableReference(inner, _)
            | Type::Option(inner) => inner.contains_bool(),
            Type::Struct { type_args, .. } => type_args.iter().any(|t| t.contains_bool()),
            Type::Prop
            | Type::UInt(_)
            | Type::Address
            | Type::TypeParameter(_)
            | Type::MoveAbort => false,
        }
    }

    /// Check if this is a Bool type
    pub fn is_bool(&self) -> bool {
        matches!(self, Type::Bool)
    }

    /// Check if this is a Prop type
    pub fn is_prop(&self) -> bool {
        matches!(self, Type::Prop)
    }

    /// Convert top-level Bool to Prop for function return types.
    /// Does NOT recurse into tuples because Prop cannot appear in
    /// a product type with Type-level values in Lean 4.
    pub fn bool_to_prop_return(&self) -> Type {
        match self {
            Type::Bool => Type::Prop,
            _ => self.clone(),
        }
    }

    /// Return the maximum TypeParameter index referenced in this type, or None if none.
    pub fn max_type_param_index(&self) -> Option<u16> {
        match self {
            Type::TypeParameter(idx) => Some(*idx),
            Type::Struct { type_args, .. } => type_args
                .iter()
                .filter_map(|t| t.max_type_param_index())
                .max(),
            Type::Vector(inner) | Type::Reference(inner) | Type::Option(inner) => {
                inner.max_type_param_index()
            }
            Type::MutableReference(inner, state) => {
                let a = inner.max_type_param_index();
                let b = state.max_type_param_index();
                a.max(b)
            }
            Type::Tuple(tys) => tys.iter().filter_map(|t| t.max_type_param_index()).max(),
            Type::Bool | Type::Prop | Type::UInt(_) | Type::Address | Type::MoveAbort => None,
        }
    }

    /// Substitute TypeParameter(idx) with the corresponding type from `substitutions`.
    /// Used when propagating types from a callee's context to the caller's context.
    pub fn substitute_type_params(&self, substitutions: &[Type]) -> Type {
        match self {
            Type::TypeParameter(idx) => {
                let idx = *idx as usize;
                if idx < substitutions.len() {
                    substitutions[idx].clone()
                } else {
                    self.clone()
                }
            }
            Type::Struct {
                struct_id,
                type_args,
            } => Type::Struct {
                struct_id: *struct_id,
                type_args: type_args
                    .iter()
                    .map(|t| t.substitute_type_params(substitutions))
                    .collect(),
            },
            Type::Vector(inner) => {
                Type::Vector(Box::new(inner.substitute_type_params(substitutions)))
            }
            Type::Reference(inner) => {
                Type::Reference(Box::new(inner.substitute_type_params(substitutions)))
            }
            Type::MutableReference(inner, state) => Type::MutableReference(
                Box::new(inner.substitute_type_params(substitutions)),
                Box::new(state.substitute_type_params(substitutions)),
            ),
            Type::Tuple(tys) => Type::Tuple(
                tys.iter()
                    .map(|t| t.substitute_type_params(substitutions))
                    .collect(),
            ),
            Type::Option(inner) => {
                Type::Option(Box::new(inner.substitute_type_params(substitutions)))
            }
            Type::Bool | Type::Prop | Type::UInt(_) | Type::Address | Type::MoveAbort => {
                self.clone()
            }
        }
    }
}
