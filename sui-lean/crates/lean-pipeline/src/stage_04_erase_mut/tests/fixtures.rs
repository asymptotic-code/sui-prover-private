//! Shared fixture helpers for stage-4 tests.
//!
//! Mirrors `stage_03_demut::tests::fixtures`. Builds minimal
//! `Program` / `Function` shapes via direct struct literals -- no
//! `ProgramBuilder` (avoids forcing Move-model qualified-id
//! allocation we don't need at this layer).

use crate::ir::{
    Block, BlockTail, BorrowEdge, Expr, Field, FunId, Function, FunctionKind, ModId, Module, Param,
    Program, Signature, Stmt, Struct, StructId, Type, VarId,
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

/// Register a stub native function with the given id. Useful when a
/// test fixture's body calls a placeholder `FunId` we don't want to
/// fully define.
pub fn register_native_stub(p: &mut Program, id: FunId) {
    let f = func(
        &format!("native_{}", id),
        Signature {
            type_params: Vec::new(),
            params: Vec::new(),
            return_type: Type::Unit,
        },
        empty_body(),
        FuncOpts {
            native: true,
            module: 0,
        },
    );
    p.functions.insert(id, f);
}

pub fn program_with(funcs: Vec<(FunId, Function)>) -> Program {
    let mut p = Program::default();
    p.modules.insert(0, module());
    for (id, f) in funcs {
        p.functions.insert(id, f);
    }
    // Register stub natives for the canonical "placeholder" callee
    // ids the fixtures use.
    register_native_stub(&mut p, 99);
    // Register stub structs for the StructIds the fixtures reference.
    // The validator rejects any `Expr::Field` / `Expr::Pack` whose
    // struct id is not in `Program::structs`. Tests use a small
    // hand-picked set; we register both with enough fields that
    // any field-index in the tests resolves.
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
// Borrow-chain construction helpers
// ---------------------------------------------------------------------------

/// `BorrowEdge::StructField { struct_id, field_index }`.
pub fn field_edge(struct_id: StructId, field_index: usize) -> BorrowEdge {
    BorrowEdge::StructField {
        struct_id,
        field_index,
    }
}

/// `BorrowEdge::EnumField { struct_id, variant, field_index }`.
pub fn enum_field_edge(struct_id: StructId, variant: usize, field_index: usize) -> BorrowEdge {
    BorrowEdge::EnumField {
        struct_id,
        variant,
        field_index,
    }
}

/// `Stmt::Let { pattern: [name], value: Expr::BorrowLoc(root) }`.
/// Mirrors stage 2's lifting of `Operation::BorrowLoc`.
pub fn let_borrow_loc(name: &str, root: &str) -> Stmt {
    Stmt::Let {
        pattern: vec![Some(VarId::from(name))],
        value: Expr::BorrowLoc(VarId::from(root)),
    }
}

/// `Stmt::Let { pattern: [name], value: Expr::BorrowField { ..base } }`.
/// Mirrors stage 2's lifting of `Operation::BorrowField`. `base` is
/// the source temp's value (typically `Var(prev_temp)`).
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

/// `Stmt::Let { pattern: [name], value: Expr::ReadRef(Var(r)) }`.
pub fn let_read_ref(name: &str, r: &str) -> Stmt {
    Stmt::Let {
        pattern: vec![Some(VarId::from(name))],
        value: Expr::ReadRef(Box::new(Expr::Var(VarId::from(r)))),
    }
}

/// Build a `Block` whose body is a single function returning
/// `tail`. Mostly used to wrap a tail with stmts in tests.
pub fn body(stmts: Vec<Stmt>, tail: Expr) -> Block {
    Block {
        stmts,
        tail: BlockTail::Value(tail),
    }
}
