//! Shared fixture helpers for stage-6 tests.
//!
//! Minimal `Program` / `Function` builders via direct struct literals
//! -- no `ProgramBuilder` (avoids forcing Move-model qualified-id
//! allocation we don't need at this layer).
//!
//! Stage 6 fixtures construct hand-built post-stage-4 IR. SSA
//! invariants (one binding per name) hold by construction in tests
//! that need them; the fixture helpers do not enforce SSA.

#![allow(dead_code)]

use crate::ir::{
    BinOp, Block, BlockTail, Const, Effects, Expr, FunId, Function, FunctionKind, ModId, Module,
    Param, Program, Signature, Stmt, Type, VarId,
};

pub fn var(name: &str) -> Expr {
    Expr::Var(VarId::from(name))
}

pub fn vid(name: &str) -> VarId {
    VarId::from(name)
}

pub fn u64_const(value: u64) -> Expr {
    use ethnum::U256;
    Expr::Const(Const::UInt {
        bits: 64,
        value: U256::from(value),
    })
}

pub fn bool_const(b: bool) -> Expr {
    Expr::Const(Const::Bool(b))
}

pub fn let_stmt(name: &str, value: Expr) -> Stmt {
    Stmt::Let {
        pattern: vec![Some(VarId::from(name))],
        value,
    }
}

pub fn let_tuple(names: &[&str], value: Expr) -> Stmt {
    Stmt::Let {
        pattern: names.iter().map(|n| Some(VarId::from(*n))).collect(),
        value,
    }
}

pub fn eval_stmt(e: Expr) -> Stmt {
    Stmt::Eval(e)
}

pub fn block_value(stmts: Vec<Stmt>, tail: Expr) -> Block {
    Block {
        stmts,
        tail: BlockTail::Value(tail),
    }
}

pub fn block_break(stmts: Vec<Stmt>, level: u32, value: Expr) -> Block {
    Block {
        stmts,
        tail: BlockTail::Break {
            level,
            value: Box::new(value),
        },
    }
}

pub fn block_continue(stmts: Vec<Stmt>, level: u32, value: Expr) -> Block {
    Block {
        stmts,
        tail: BlockTail::Continue {
            level,
            value: Box::new(value),
        },
    }
}

pub fn block_return(stmts: Vec<Stmt>, value: Expr) -> Block {
    Block {
        stmts,
        tail: BlockTail::Return(Box::new(value)),
    }
}

pub fn block_abort(stmts: Vec<Stmt>, code: Expr) -> Block {
    Block {
        stmts,
        tail: BlockTail::Abort {
            code: Box::new(code),
        },
    }
}

pub fn add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::BinOp {
        op: BinOp::Add,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

pub fn eq(lhs: Expr, rhs: Expr) -> Expr {
    Expr::BinOp {
        op: BinOp::Eq,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

pub fn lt(lhs: Expr, rhs: Expr) -> Expr {
    Expr::BinOp {
        op: BinOp::Lt,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

pub fn tuple(elems: Vec<Expr>) -> Expr {
    Expr::Tuple(elems)
}

pub fn call(fun: FunId, args: Vec<Expr>) -> Expr {
    Expr::Call {
        fun,
        type_args: Vec::new(),
        args,
    }
}

pub fn if_expr(cond: Expr, then_b: Block, else_b: Block) -> Expr {
    Expr::If {
        cond: Box::new(cond),
        then_branch: Box::new(then_b),
        else_branch: Box::new(else_b),
    }
}

/// Build an `Expr::While` with no iter_locals (stages 1-4 shape).
pub fn while_expr(header: Block, cond: Expr, body: Block) -> Expr {
    Expr::While {
        header: Box::new(header),
        cond: Box::new(cond),
        body: Box::new(body),
        iter_locals: Vec::new(),
        header_exit_locals: Vec::new(),
        live_out: vec![],
    }
}

/// Build an `Expr::While` with the given `iter_locals` (post-stage-5 shape).
pub fn while_with_iter_locals(
    header: Block,
    cond: Expr,
    body: Block,
    iter_locals: Vec<(VarId, Expr)>,
) -> Expr {
    Expr::While {
        header: Box::new(header),
        cond: Box::new(cond),
        body: Box::new(body),
        iter_locals,
        header_exit_locals: Vec::new(),
        live_out: vec![],
    }
}

/// Register a `Function` with the given [`Effects`] and a no-op
/// body. Useful when a fixture's body calls `FunId` whose body is
/// irrelevant; only effects and signature presence matters.
pub fn stub_callee(name: &str, effects: Effects, return_type: Type) -> Function {
    Function {
        module: 0,
        name: name.to_string(),
        signature: Signature {
            type_params: Vec::new(),
            params: Vec::new(),
            return_type,
        },
        body: Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::Unit),
        },
        kind: FunctionKind::Source,
        effects,
        explicit_pure: false,
    }
}

pub fn empty_program() -> Program {
    let mut p = Program::default();
    p.modules.insert(
        0 as ModId,
        Module {
            name: "m".to_string(),
            package_name: "p".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        },
    );
    p
}

/// Build a `Program` with a list of `(FunId, Function)` entries.
/// Mirrors the stage-4 fixture helper.
pub fn program_with(funcs: Vec<(FunId, Function)>) -> Program {
    let mut p = empty_program();
    for (id, f) in funcs {
        p.functions.insert(id, f);
    }
    p
}

/// Build a `Param`.
pub fn param(name: &str, ty: Type) -> Param {
    Param {
        name: name.to_string(),
        var: VarId::from(name),
        ty,
    }
}
