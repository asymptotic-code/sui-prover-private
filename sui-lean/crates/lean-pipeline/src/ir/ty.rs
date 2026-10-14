//! Type system and constants.
//!
//! See `plans/lean-pipeline/ir.md` "Types" section.

use ethnum::U256;
use num::BigUint;

use super::StructId;

/// Theorem IR type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// `()` -- explicit, distinct from `Tuple(vec![])`.
    Unit,
    /// Computational `Bool`.
    Bool,
    /// Logical `Prop` (spec / aborts only).
    Prop,
    /// Unsigned integer with bit width (`u8` / `u16` / `u32` / `u64` / `u128` / `u256`).
    UInt(u32),
    Address,
    Vector(Box<Type>),
    Tuple(Vec<Type>),
    Struct {
        struct_id: StructId,
        type_args: Vec<Type>,
    },
    /// `&T`.
    Reference(Box<Type>),
    /// `&mut T` -- eliminated by stage 3. `inner` is the borrowed value's type;
    /// `root` is the type at the borrow chain's source (the ancestor struct,
    /// `UID`, etc.).
    MutableRef {
        inner: Box<Type>,
        root: Box<Type>,
    },
    TypeParam(u16),
}

/// Constant values.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Const {
    Bool(bool),
    UInt {
        bits: u32,
        value: U256,
    },
    Address(BigUint),
    Vector {
        elem_type: Type,
        elems: Vec<Const>,
    },
    /// Constant unit. Mirrors `Expr::Unit` for use inside `Const::Vector` etc.
    Unit,
    /// A type-correct DEFAULT value (`Inhabited.default`) of the given
    /// type. Used to initialize a type-known loop-carried SSA value that
    /// has no pre-loop binding. Renders as `(default : T)`; generated
    /// structs derive `Inhabited`.
    Default(Type),
}
