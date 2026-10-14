//! Shared fixture helpers for stage-4 (effects) tests.
//!
//! Mirrors `stage_03_mut_to_let::tests::fixtures` in shape.

use crate::ir::{
    Block, BlockTail, Effects, Expr, FunId, Function, FunctionKind, ModId, Module, Param, Program,
    Signature, Stmt, Type, VarId,
};

pub fn module() -> Module {
    Module {
        name: "m".to_string(),
        package_name: "MyProject".to_string(),
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

#[derive(Debug, Clone, Copy)]
pub struct FuncOpts {
    pub native: bool,
    pub module: ModId,
    pub effects: Effects,
}

impl Default for FuncOpts {
    fn default() -> Self {
        Self {
            native: false,
            module: 0,
            effects: Effects::CONSERVATIVE,
        }
    }
}

pub fn func(name: &str, sig: Signature, body: Block, opts: FuncOpts) -> Function {
    Function {
        module: opts.module,
        name: name.to_string(),
        signature: sig,
        body,
        kind: FunctionKind::Source,
        effects: opts.effects,
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

pub fn body(stmts: Vec<Stmt>, tail: Expr) -> Block {
    Block {
        stmts,
        tail: BlockTail::Value(tail),
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

pub fn lit_u64(n: u64) -> Expr {
    Expr::Const(crate::ir::Const::UInt {
        bits: 64,
        value: ethnum::U256::from(n),
    })
}

pub fn body_of(program: &Program, fid: FunId) -> &Block {
    &program.functions[&fid].body
}

/// Build a native Impure declaration (e.g., a stand-in for
/// `event::emit` in tests). Stage 4's call-site augmentation
/// adds the world slot when the callee resolves to a
/// `CalleeRef::Native(_)`.
pub fn native_impure(name: &str, params: Vec<Param>, ret: Type) -> crate::ir::NativeDecl {
    crate::ir::NativeDecl {
        module: 0,
        name: name.to_string(),
        signature: sig(params, ret),
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
        is_framework: true,
        spec_target: None,
        user_native: None,
    }
}

/// Build a native declaration with an explicit [`Effects`] value.
pub fn native_with_effects(
    name: &str,
    params: Vec<Param>,
    ret: Type,
    effects: crate::ir::Effects,
) -> crate::ir::NativeDecl {
    crate::ir::NativeDecl {
        module: 0,
        name: name.to_string(),
        signature: sig(params, ret),
        effects,
        explicit_pure: false,
        is_framework: true,
        spec_target: None,
        user_native: None,
    }
}

/// Build a [`Program`] with the given translated functions and native
/// declarations. Mirrors [`program_with`] but supports natives.
pub fn program_with_natives(
    funcs: Vec<(FunId, Function)>,
    natives: Vec<(FunId, crate::ir::NativeDecl)>,
) -> Program {
    let mut p = Program::default();
    p.modules.insert(0, module());
    for (id, f) in funcs {
        p.functions.insert(id, f);
    }
    for (id, d) in natives {
        p.natives.decls.insert(id, d);
    }
    p
}
