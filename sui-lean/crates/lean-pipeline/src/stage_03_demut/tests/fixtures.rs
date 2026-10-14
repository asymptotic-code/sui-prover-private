//! Shared fixture helpers for stage-3 tests.
//!
//! Builds minimal `Program` / `Function` shapes via direct struct
//! literals -- the full `ProgramBuilder` would force allocating
//! Move-model qualified ids we don't need at this layer. Mirrors the
//! pattern used by `stage_02_ir_cfg::effects::tests`.

use crate::ir::{
    Block, BlockTail, Expr, FunId, Function, FunctionKind, ModId, Module, Param, Program,
    Signature, Stmt, Type, VarId,
};

pub fn module() -> Module {
    Module {
        name: "m".to_string(),
        package_name: "p".to_string(),
        address: String::new(),
        required_imports: Vec::new(),
        is_native: false,
    }
}

pub fn mut_ref(inner: Type, root: Type) -> Type {
    Type::MutableRef {
        inner: Box::new(inner),
        root: Box::new(root),
    }
}

pub fn param(name: &str, ty: Type) -> Param {
    Param {
        name: name.to_string(),
        var: VarId::from(name),
        ty,
    }
}

pub fn empty_body() -> Block {
    Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(Expr::Unit),
    }
}

pub fn body_returning(tail: Expr) -> Block {
    Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(tail),
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct FuncOpts {
    pub native: bool,
    pub module: ModId,
}

pub fn func(name: &str, sig: Signature, body: Block, opts: FuncOpts) -> Function {
    Function {
        module: opts.module,
        name: name.to_string(),
        signature: sig,
        body,
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    }
}

pub fn sig(params: Vec<Param>, return_type: Type) -> Signature {
    Signature {
        type_params: Vec::new(),
        params,
        return_type,
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

/// `Stmt::Eval(call(callee, []))` -- a side-effecting call to `callee`
/// with no args. Useful for building call-graph fixtures.
pub fn call_stmt(callee: FunId) -> Stmt {
    Stmt::Eval(Expr::Call {
        fun: callee,
        type_args: Vec::new(),
        args: Vec::new(),
    })
}

/// Body that contains a single `Stmt::Eval(Call(callee))` and returns
/// `Unit`. Drops the call's value.
pub fn body_calling(callees: &[FunId]) -> Block {
    let stmts: Vec<Stmt> = callees.iter().copied().map(call_stmt).collect();
    Block {
        stmts,
        tail: BlockTail::Value(Expr::Unit),
    }
}
