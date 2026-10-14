//! Operator enums.
//!
//! See `plans/lean-pipeline/ir.md` "Operators" section.

use super::expr::Expr;

/// Binary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    // Arithmetic
    /// Checked unsigned addition (Move semantics; LLVM `add nuw`).
    Add,
    /// Checked unsigned subtraction (Move semantics; LLVM `sub nuw`).
    Sub,
    /// Checked unsigned multiplication (Move semantics; LLVM `mul nuw`).
    Mul,
    /// Modular fixed-width addition (plain LLVM `add`).
    WrappingAdd,
    /// Modular fixed-width subtraction (plain LLVM `sub`).
    WrappingSub,
    /// Modular fixed-width multiplication (plain LLVM `mul`).
    WrappingMul,
    /// Checked signed fixed-width addition (LLVM `add nsw`).
    SAdd,
    /// Checked signed fixed-width subtraction (LLVM `sub nsw`).
    SSub,
    /// Checked signed fixed-width multiplication (LLVM `mul nsw`).
    SMul,
    /// Unsigned division.
    Div,
    /// Unsigned remainder.
    Mod,
    /// Signed two's-complement division, truncating toward zero.
    SDiv,
    /// Signed two's-complement remainder (sign follows the dividend).
    SMod,
    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    /// Move's logical right shift. Kept distinct to preserve existing IR.
    Shr,
    /// LLVM logical right shift.
    LShr,
    /// LLVM arithmetic right shift.
    AShr,
    // Logical
    And,
    Or,
    // Comparison
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    // Signed two's-complement comparison
    SLt,
    SLe,
    SGt,
    SGe,
}

impl BinOp {
    /// True when this op can abort at runtime on bounded integer operands
    /// (overflow / div-by-zero / shift width). Used by stage 9.
    pub fn can_abort_on_uint(self) -> bool {
        matches!(
            self,
            BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::SAdd
                | BinOp::SSub
                | BinOp::SMul
                | BinOp::Div
                | BinOp::Mod
                | BinOp::SDiv
                | BinOp::SMod
                | BinOp::Shl
                | BinOp::Shr
                | BinOp::LShr
                | BinOp::AShr
        )
    }
}

/// Unary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    Not,
    BitNot,
    /// Cast to unsigned integer with the given bit width.
    Cast(u32),
}

/// Bit-level operations.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BitOp {
    /// Extract bits `[high:low]` from `operand`.
    Extract {
        high: u32,
        low: u32,
        operand: Box<Expr>,
    },
    /// Concatenate two bitvectors.
    Concat { high: Box<Expr>, low: Box<Expr> },
    /// Zero-extend by `bits`.
    ZeroExtend { bits: u32, operand: Box<Expr> },
    /// Sign-extend by `bits`.
    SignExtend { bits: u32, operand: Box<Expr> },
}
