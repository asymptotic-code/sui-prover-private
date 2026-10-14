//! Shared fixture helpers for stage-3 (mut-to-let) tests.
//!
//! Builds minimal `Program` / `Function` shapes via direct struct
//! literals.

use crate::ir::{
    Block, BlockTail, BorrowEdge, BorrowNode, Expr, Field, FunId, Function, FunctionKind, ModId,
    Module, Param, Program, Signature, Stmt, Struct, StructId, Type, VarId,
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

#[allow(dead_code)]
pub fn empty_body() -> Block {
    Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(Expr::Unit),
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
    // Register stub structs for the StructIds the fixtures reference.
    for sid in [7usize, 11usize] {
        p.structs.insert(
            sid,
            Struct {
                module_id: 0,
                name: format!("S{}", sid),
                qualified_name: format!("p::m::S{}", sid),
                type_params: Vec::new(),
                fields: vec![
                    Field {
                        name: "f0".into(),
                        field_type: Type::UInt(64),
                    },
                    Field {
                        name: "f1".into(),
                        field_type: Type::UInt(64),
                    },
                    Field {
                        name: "f2".into(),
                        field_type: Type::UInt(64),
                    },
                ],
                variants: None,
                is_native: false,
            },
        );
    }
    p
}

// ---------------------------------------------------------------------------
// Construction helpers
// ---------------------------------------------------------------------------

pub fn lit_u64(n: u64) -> Expr {
    Expr::Const(crate::ir::Const::UInt {
        bits: 64,
        value: ethnum::U256::from(n),
    })
}

pub fn let_borrow_loc(name: &str, root: &str) -> Stmt {
    Stmt::Let {
        pattern: vec![Some(VarId::from(name))],
        value: Expr::BorrowLoc(VarId::from(root)),
    }
}

pub fn let_borrow_field(name: &str, struct_id: StructId, field_index: usize, base: Expr) -> Stmt {
    Stmt::Let {
        pattern: vec![Some(VarId::from(name))],
        value: Expr::Borrow {
            step: crate::ir::path::PathStep::Field {
                struct_id: struct_id,
                field_index: field_index,
            },
            base: Box::new(base),
        },
    }
}

pub fn eval_write_ref(r: &str, value: Expr) -> Stmt {
    Stmt::Eval(Expr::WriteRef {
        reference: Box::new(Expr::Var(VarId::from(r))),
        value: Box::new(value),
    })
}

pub fn eval_write_back(node: BorrowNode, edge: BorrowEdge, child: &str) -> Stmt {
    Stmt::Eval(Expr::WriteBack {
        node,
        edge,
        child: VarId::from(child),
        world: None,
    })
}

pub fn body(stmts: Vec<Stmt>, tail: Expr) -> Block {
    Block {
        stmts,
        tail: BlockTail::Value(tail),
    }
}

// ---------------------------------------------------------------------------
// Single-fn-program builders
// ---------------------------------------------------------------------------

pub fn one_fn_program(stmts: Vec<Stmt>, tail: Expr, params: Vec<Param>, ret: Type) -> Program {
    let f = func(
        "f",
        sig(params, ret),
        body(stmts, tail),
        FuncOpts::default(),
    );
    program_with(vec![(0, f)])
}

pub fn body_of(program: &Program) -> &Block {
    &program.functions[&0].body
}
