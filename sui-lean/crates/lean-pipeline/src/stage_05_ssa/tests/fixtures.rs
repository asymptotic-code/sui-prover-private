//! Shared fixture helpers for stage-5 (SSA) tests.
//!
//! Mirrors `stage_03_mut_to_let::tests::fixtures` in shape. Builds
//! minimal `Program` / `Function` shapes via direct struct literals.

use crate::ir::{
    Block, BlockTail, Expr, Function, FunctionKind, ModId, Module, Param, Program, Signature, Stmt,
    Type, VarId,
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

pub fn param(name: &str, ty: Type) -> Param {
    Param {
        name: name.to_string(),
        var: VarId::from(name),
        ty,
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

pub fn program_with(funcs: Vec<(usize, Function)>) -> Program {
    let mut p = Program::default();
    p.modules.insert(0, module());
    for (id, f) in funcs {
        p.functions.insert(id, f);
    }
    p
}

pub fn lit_u64(n: u64) -> Expr {
    Expr::Const(crate::ir::Const::UInt {
        bits: 64,
        value: ethnum::U256::from(n),
    })
}

pub fn body(stmts: Vec<Stmt>, tail: Expr) -> Block {
    Block {
        stmts,
        tail: BlockTail::Value(tail),
    }
}

pub fn one_fn_program(stmts: Vec<Stmt>, tail: Expr, params: Vec<Param>, ret: Type) -> Program {
    let f = func(
        "f",
        sig(params, ret),
        body(stmts, tail),
        FuncOpts::default(),
    );
    program_with(vec![(0, f)])
}

#[allow(dead_code)]
pub fn body_of(program: &Program) -> &Block {
    &program.functions[&0].body
}
