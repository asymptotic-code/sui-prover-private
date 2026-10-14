//! Shared fixture helpers for render tests. Mirrors the shape of the
//! stage-3 tests' fixtures module (`stage_03_mut_to_let::tests::fixtures`)
//! to keep the crate uniform.

use ethnum::U256;

use crate::ir::{
    BinOp, Block, BlockTail, Const, Expr, Field, FunId, Function, FunctionKind, ModId, Module,
    Param, Program, Signature, Stmt, Struct, StructId, Type, VarId,
};

pub fn module(name: &str) -> Module {
    Module {
        name: name.to_string(),
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

pub fn sig(params: Vec<Param>, return_type: Type) -> Signature {
    Signature {
        type_params: Vec::new(),
        params,
        return_type,
    }
}

pub fn func(name: &str, sig: Signature, body: Block, module_id: ModId) -> Function {
    Function {
        module: module_id,
        name: name.to_string(),
        signature: sig,
        body,
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    }
}

pub fn empty_program() -> Program {
    let mut p = Program::default();
    p.modules.insert(0, module("m"));
    p
}

pub fn add_function(prog: &mut Program, id: FunId, f: Function) {
    prog.functions.insert(id, f);
}

pub fn add_struct(prog: &mut Program, id: StructId, s: Struct) {
    prog.structs.insert(id, s);
}

pub fn body(stmts: Vec<Stmt>, tail: Expr) -> Block {
    Block {
        stmts,
        tail: BlockTail::Value(tail),
    }
}

pub fn var(name: &str) -> Expr {
    Expr::Var(VarId::from(name))
}

pub fn lit_u64(n: u64) -> Expr {
    Expr::Const(Const::UInt {
        bits: 64,
        value: U256::from(n),
    })
}

pub fn lit_u256(n: u128) -> Expr {
    Expr::Const(Const::UInt {
        bits: 256,
        value: U256::from(n),
    })
}

pub fn add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::BinOp {
        op: BinOp::Add,
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
    }
}

pub fn let_(name: &str, value: Expr) -> Stmt {
    Stmt::Let {
        pattern: vec![Some(VarId::from(name))],
        value,
    }
}

pub fn simple_struct(module_id: ModId, name: &str, fields: Vec<(&str, Type)>) -> Struct {
    Struct {
        module_id,
        name: name.to_string(),
        qualified_name: format!("p::m::{}", name),
        type_params: Vec::new(),
        fields: fields
            .into_iter()
            .map(|(fname, fty)| Field {
                name: fname.to_string(),
                field_type: fty,
            })
            .collect(),
        variants: None,
        is_native: false,
    }
}

pub fn native(
    name: &str,
    signature: Signature,
    module_id: ModId,
    effects: crate::ir::Effects,
    is_framework: bool,
) -> crate::ir::NativeDecl {
    crate::ir::NativeDecl {
        module: module_id,
        name: name.to_string(),
        signature,
        effects,
        explicit_pure: false,
        is_framework,
        spec_target: None,
        user_native: None,
    }
}

pub fn add_native(prog: &mut Program, id: FunId, d: crate::ir::NativeDecl) {
    prog.natives.decls.insert(id, d);
}
