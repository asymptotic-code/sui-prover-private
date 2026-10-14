//! Shared fixtures for stage 10 tests.

use crate::ir::expr::{Block, BlockTail, Expr};
use crate::ir::function::{Function, FunctionKind, Param, Signature};
use crate::ir::ops::BinOp;
use crate::ir::ty::Type;
use crate::ir::{FunId, Module, Program, VarId};

pub fn vid(s: &str) -> VarId {
    s.into()
}

pub fn module() -> Module {
    Module {
        name: "m".to_string(),
        package_name: "p".to_string(),
        address: String::new(),
        required_imports: Vec::new(),
        is_native: false,
    }
}

pub fn param(name: &str, ty: Type) -> Param {
    Param {
        name: name.to_string(),
        var: VarId::from(name),
        ty,
    }
}

pub fn func(name: &str, params: Vec<Param>, ret: Type, body: Block) -> Function {
    Function {
        module: 0,
        name: name.to_string(),
        signature: Signature {
            type_params: Vec::new(),
            params,
            return_type: ret,
        },
        body,
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    }
}

pub fn program_with(funcs: Vec<(FunId, Function)>) -> Program {
    let mut p = Program::default();
    p.modules.insert(0, module());
    for (id, f) in funcs {
        p.functions.insert(id, f);
    }
    p
}

/// A function `add_u64(a: u64, b: u64): u64 = a + b`.
pub fn fn_add_u64() -> Function {
    func(
        "add_u64",
        vec![param("a", Type::UInt(64)), param("b", Type::UInt(64))],
        Type::UInt(64),
        Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(Expr::Var(vid("a"))),
                rhs: Box::new(Expr::Var(vid("b"))),
            }),
        },
    )
}

/// A function `lt_u64(a: u64, b: u64): bool = a < b`.
pub fn fn_lt_u64() -> Function {
    func(
        "lt_u64",
        vec![param("a", Type::UInt(64)), param("b", Type::UInt(64))],
        Type::Bool,
        Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::BinOp {
                op: BinOp::Lt,
                lhs: Box::new(Expr::Var(vid("a"))),
                rhs: Box::new(Expr::Var(vid("b"))),
            }),
        },
    )
}

/// `cast_to_u8(x: u64): u8 = (x as u8)`.
pub fn fn_cast_u64_to_u8() -> Function {
    use crate::ir::ops::UnOp;
    func(
        "cast_to_u8",
        vec![param("x", Type::UInt(64))],
        Type::UInt(8),
        Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::UnOp {
                op: UnOp::Cast(8),
                operand: Box::new(Expr::Var(vid("x"))),
            }),
        },
    )
}
