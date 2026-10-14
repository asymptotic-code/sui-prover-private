//! Rewrite 3 -- strip residual `Type::MutableRef` from non-pattern-4b
//! signatures and from all `Type`s reachable through function bodies
//! (`Call::type_args`, `Pack::type_args`, `Quantifier::binder_type`).
//!
//! Stage 3 already stripped `Type::MutableRef` from parameter types
//! during signature demotion. This pass cleans up:
//!
//! 1. **Return types** -- for every non-native, non-pattern-4b
//!    function whose return type is `Type::MutableRef { inner, .. }`,
//!    replace it with `*inner`. Pattern-4b sub-field-mutref-returning
//!    functions keep the mutref return (detected via the same
//!    tail-shape recogniser stage 3 uses).
//! 2. **Body type slots** -- walk every expression and strip
//!    `Type::MutableRef` from each `Vec<Type>` in `Call::type_args` /
//!    `Pack::type_args` and from `Quantifier::binder_type`. These
//!    should be impossible after stage 3 in well-formed input, but
//!    the strip is uniform: test once and trust it.
//!
//! The `Type` walker is recursive: `Type::Vector(Box<Type>)`,
//! `Type::Tuple(Vec<Type>)`, `Type::Reference(Box<Type>)`, and
//! `Type::Struct { type_args, .. }` may all contain a nested
//! `MutableRef`.

use crate::ir::{Block, BlockTail, Expr, FunId, Function, MatchArm, Program, Stmt, Type};

/// Strip residual `Type::MutableRef`s from every non-native function
/// in `program`. Pattern-4b functions keep their return-type mutref.
pub fn strip_mutable_ref_types(program: &mut Program) {
    let funcs: Vec<FunId> = program.functions.iter().map(|(id, _)| *id).collect();
    for fid in funcs {
        let func = program.functions.get_mut(&fid).unwrap();
        strip_function(func);
    }
}

fn strip_function(func: &mut Function) {
    let is_4b = is_pattern_4b(func);

    // Strip param types (defensive -- stage 3 already did this).
    for param in func.signature.params.iter_mut() {
        param.ty = strip_type(std::mem::replace(&mut param.ty, Type::Unit));
    }

    // Return type: strip unless pattern 4b.
    if !is_4b {
        func.signature.return_type = strip_type(std::mem::replace(
            &mut func.signature.return_type,
            Type::Unit,
        ));
    }

    // Body: strip type slots inside expressions.
    strip_block(&mut func.body);
}

/// Pattern 4b: function returns `Type::MutableRef<_>` and its body's
/// tail is a `BorrowLoc` / `BorrowField` chain (NOT a `Var(p)` of a
/// param -- that's pattern 4a, already demoted to plain T by stage 3).
fn is_pattern_4b(func: &Function) -> bool {
    if !matches!(func.signature.return_type, Type::MutableRef { .. }) {
        return false;
    }
    matches!(
        &func.body.tail,
        BlockTail::Value(Expr::BorrowLoc(_))
            | BlockTail::Value(Expr::Borrow {
                step: crate::ir::path::PathStep::Field { .. },
                ..
            })
    )
}

// ---------------------------------------------------------------------------
// Type stripping
// ---------------------------------------------------------------------------

/// Recursively replace every `Type::MutableRef { inner, .. }` with its
/// `inner`. Walks `Vector`, `Tuple`, `Reference`, and
/// `Struct::type_args`.
fn strip_type(ty: Type) -> Type {
    match ty {
        Type::MutableRef { inner, .. } => strip_type(*inner),
        Type::Vector(inner) => Type::Vector(Box::new(strip_type(*inner))),
        Type::Tuple(items) => Type::Tuple(items.into_iter().map(strip_type).collect()),
        Type::Reference(inner) => Type::Reference(Box::new(strip_type(*inner))),
        Type::Struct {
            struct_id,
            type_args,
        } => Type::Struct {
            struct_id,
            type_args: type_args.into_iter().map(strip_type).collect(),
        },
        other => other,
    }
}

// ---------------------------------------------------------------------------
// Body / expr / type-slot traversal
// ---------------------------------------------------------------------------

fn strip_block(block: &mut Block) {
    for stmt in block.stmts.iter_mut() {
        match stmt {
            Stmt::Let { value, .. } => strip_expr(value),
            Stmt::Eval(e) => strip_expr(e),
        }
    }
    strip_tail(&mut block.tail);
}

fn strip_tail(tail: &mut BlockTail) {
    match tail {
        BlockTail::Value(e) => strip_expr(e),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => strip_expr(value),
        BlockTail::Abort { code } => strip_expr(code),
    }
}

fn strip_expr(expr: &mut Expr) {
    match expr {
        Expr::Borrow { step, base } => {
            if let crate::ir::path::PathStep::MapKey {
                key_type,
                value_type,
                ..
            } = step
            {
                *key_type = strip_type(std::mem::replace(key_type, Type::Unit));
                *value_type = strip_type(std::mem::replace(value_type, Type::Unit));
            }
            for __pe in step.exprs_mut() {
                strip_expr(__pe);
            }
            strip_expr(base);
        }
        Expr::Update { step, base, value } => {
            if let crate::ir::path::PathStep::MapKey {
                key_type,
                value_type,
                ..
            } = step
            {
                *key_type = strip_type(std::mem::replace(key_type, Type::Unit));
                *value_type = strip_type(std::mem::replace(value_type, Type::Unit));
            }
            for __pe in step.exprs_mut() {
                strip_expr(__pe);
            }
            strip_expr(base);
            strip_expr(value);
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. } => {}
        Expr::BinOp { lhs, rhs, .. } => {
            strip_expr(lhs);
            strip_expr(rhs);
        }
        Expr::UnOp { operand, .. } => strip_expr(operand),
        Expr::BitOp(op) => strip_bitop(op),
        Expr::Call {
            type_args, args, ..
        } => {
            *type_args = type_args.drain(..).map(strip_type).collect();
            for a in args.iter_mut() {
                strip_expr(a);
            }
        }
        Expr::Tuple(items) => {
            for a in items.iter_mut() {
                strip_expr(a);
            }
        }
        Expr::Pack {
            type_args, fields, ..
        } => {
            *type_args = type_args.drain(..).map(strip_type).collect();
            for a in fields.iter_mut() {
                strip_expr(a);
            }
        }
        Expr::Unpack { value, .. } => strip_expr(value),
        Expr::Field { base, .. } => strip_expr(base),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            strip_expr(cond);
            strip_block(then_branch);
            strip_block(else_branch);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            strip_expr(selector);
            for MatchArm { body, .. } in cases.iter_mut() {
                strip_block(body);
            }
        }
        Expr::While {
            header, cond, body, ..
        } => {
            strip_block(header);
            strip_expr(cond);
            strip_block(body);
        }
        Expr::ReadRef(inner) | Expr::ToProp(inner) | Expr::ToBool(inner) => strip_expr(inner),
        Expr::WriteRef { reference, value } => {
            strip_expr(reference);
            strip_expr(value);
        }
        Expr::Quantifier {
            binder_type, body, ..
        } => {
            *binder_type = strip_type(std::mem::replace(binder_type, Type::Unit));
            strip_block(body);
        }
        Expr::IsParent { .. } => {}
        Expr::LabeledBlock { body, .. } => strip_block(body),
    }
}

fn strip_bitop(op: &mut crate::ir::BitOp) {
    use crate::ir::BitOp::*;
    match op {
        Extract { operand, .. } | ZeroExtend { operand, .. } | SignExtend { operand, .. } => {
            strip_expr(operand);
        }
        Concat { high, low } => {
            strip_expr(high);
            strip_expr(low);
        }
    }
}
