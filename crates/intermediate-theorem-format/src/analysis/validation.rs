// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! IR Validation — checks that the IR is well-formed before rendering.
//!
//! This module validates:
//! 1. All variables are defined before use
//! 2. Return types are consistent (body type matches signature)
//! 3. Tuple patterns match tuple values
//! 4. Function calls have correct arity

use crate::data::functions::Function;
use crate::data::types::{TempId, Type};
use crate::data::variables::VariableRegistry;
use crate::{IRNode, Program};
use std::collections::BTreeSet;

/// Validation error with context
#[derive(Debug, Clone)]
pub struct ValidationError {
    pub function_name: String,
    pub message: String,
    pub location: Option<String>,
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(loc) = &self.location {
            write!(
                f,
                "In {}: {} (at {})",
                self.function_name, self.message, loc
            )
        } else {
            write!(f, "In {}: {}", self.function_name, self.message)
        }
    }
}

/// Validation context. Tracks in-scope variable NAMES (for defined-before-use
/// checks) separately from the TYPE-aware registry the caller threads for
/// `infer_type`. The registry is scope-sensitive — extend it via
/// `vars.register` at binding sites and clone+restore across branches.
struct ValidationCtx<'a> {
    function_name: String,
    program: &'a Program,
    errors: Vec<ValidationError>,
    scope: BTreeSet<TempId>,
}

impl<'a> ValidationCtx<'a> {
    fn new(function_name: String, program: &'a Program) -> Self {
        Self {
            function_name,
            program,
            errors: Vec::new(),
            scope: BTreeSet::new(),
        }
    }

    fn error(&mut self, message: String) {
        self.errors.push(ValidationError {
            function_name: self.function_name.clone(),
            message,
            location: None,
        });
    }

    #[allow(dead_code)]
    fn error_at(&mut self, message: String, location: String) {
        self.errors.push(ValidationError {
            function_name: self.function_name.clone(),
            message,
            location: Some(location),
        });
    }

    fn with_scope<F, R>(&mut self, new_vars: &[TempId], f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let old_scope = self.scope.clone();
        self.scope.extend(new_vars.iter().cloned());
        let result = f(self);
        self.scope = old_scope;
        result
    }
}

/// Check if a function body represents an always-aborting function.
/// These functions don't need return type checking because they never return.
fn is_abort_only_body(node: &IRNode) -> bool {
    match node {
        // Inhabited is used as a placeholder for unreachable code after abort
        IRNode::Inhabited => true,
        // Empty tuple is sometimes used for functions that only abort
        IRNode::Tuple(elems) if elems.is_empty() => true,
        // Let binding that ends in abort-only body
        IRNode::Let { body, .. } => is_abort_only_body(body),
        _ => false,
    }
}

/// Validate a single function
pub fn validate_function(func: &Function, program: &Program) -> Vec<ValidationError> {
    let mut registry = func.param_registry(program);
    let mut ctx = ValidationCtx::new(func.name.clone(), program);

    // Add parameters to scope
    for param in &func.signature.parameters {
        ctx.scope.insert(param.ssa_value.clone());
    }
    // Proof parameters (e.g. `hinv`, `hpre`) are real binders appended after the
    // value params; bring them into scope so references in the body resolve.
    for pp in &func.signature.proof_params {
        ctx.scope.insert(pp.name.as_str().into());
    }

    // Validate the body
    validate_node(&func.body, &mut ctx, &mut registry);

    if std::env::var("DEBUG_DUMP_IR").is_ok() {
        let want = std::env::var("DEBUG_DUMP_IR").unwrap_or_default();
        if want == "all" || func.name == want {
            eprintln!(
                "\nIR_DUMP_ID id=??? name='{}' mod={} return={:?}",
                func.name, func.module_id, func.signature.return_type
            );
            eprintln!(
                "params: {:?}",
                func.signature
                    .parameters
                    .iter()
                    .map(|p| (&p.name, &p.ssa_value, &p.param_type))
                    .collect::<Vec<_>>()
            );
            eprintln!("body:\n{:#?}", func.body);
        }
    }

    // Check return type consistency (skip for native functions and abort-only functions)
    if !func.is_native && !is_abort_only_body(&func.body) {
        let body_type = infer_type(&func.body, &ctx, &registry);
        if let Some(bt) = body_type {
            if !types_compatible(&bt, &func.signature.return_type) {
                ctx.error(format!(
                    "Return type mismatch: body has type {:?}, signature declares {:?}",
                    bt, func.signature.return_type
                ));
            }
        }
    }

    ctx.errors
}

/// Validate all functions in a program
pub fn validate_program(program: &Program) -> Vec<ValidationError> {
    let mut errors = Vec::new();

    for (id, func) in program.functions.iter() {
        if std::env::var("DEBUG_DUMP_IDS").is_ok()
            && (func.name.contains("next_with_context") || func.name.contains("end_transaction"))
        {
            eprintln!("FUNC_ID {} -> name='{}'", id, func.name);
        }
        errors.extend(validate_function(func, program));
    }

    errors
}

/// Validate an IR node. `reg` is a scope-sensitive registry maintained by the
/// walk; callers extend it at Let/Quantifier/Match bindings (cloning for
/// branch-local extensions and dropping back to the parent scope on return).
fn validate_node(node: &IRNode, ctx: &mut ValidationCtx, reg: &mut VariableRegistry) {
    match node {
        IRNode::Var(name) => {
            // `_` is a wildcard; `sorry` is the proof placeholder the
            // loop-invariant entry cascade threads for non-terminal callers
            // (renders as Lean `sorry`, not a bound variable).
            if !ctx.scope.contains(name) && name.as_ref() != "_" && name.as_ref() != "sorry" {
                ctx.error(format!("Undefined variable: {}", name));
            }
        }

        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // Validate the value first, in the OUTER scope.
            validate_node(value, ctx, reg);

            // Check pattern matches value structure for tuples.
            if let IRNode::Tuple(elems) = value.as_ref() {
                if pattern.len() != elems.len() && !pattern.is_empty() {
                    ctx.error(format!(
                        "Pattern has {} elements but value is a tuple with {} elements",
                        pattern.len(),
                        elems.len()
                    ));
                }
            }

            // Extend the type registry with the new pattern and recurse into body.
            let mut inner = reg.clone();
            inner.add_node(node);
            ctx.with_scope(pattern, |ctx| {
                validate_node(body, ctx, &mut inner);
            });
        }

        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            validate_node(cond, ctx, reg);
            validate_node(then_branch, ctx, reg);
            validate_node(else_branch, ctx, reg);
        }

        IRNode::Match { scrutinee, cases } => {
            validate_node(scrutinee, ctx, reg);
            let scrutinee_ty = match scrutinee.get_type(reg) {
                Type::Reference(inner) => *inner,
                Type::MutableReference(val, _) => *val,
                other => other,
            };
            for (tag, bindings, body) in cases {
                let mut inner = reg.clone();
                if let Type::Struct {
                    struct_id,
                    type_args,
                } = &scrutinee_ty
                {
                    let s = reg.program().structs.get(*struct_id);
                    if let Some(variants) = s.variants.as_ref() {
                        if let Some(variant) = variants.iter().find(|v| v.tag == *tag) {
                            for (name, field) in bindings.iter().zip(variant.fields.iter()) {
                                let ty = field.field_type.clone().substitute_type_params(type_args);
                                inner.register(name.clone(), ty);
                            }
                        }
                    }
                }
                ctx.with_scope(bindings, |ctx| {
                    validate_node(body, ctx, &mut inner);
                });
            }
        }

        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => {
            validate_node(scrutinee, ctx, reg);
            // Give the binding a placeholder type so look-ups inside `some_branch`
            // don't fault. Validation only checks name-level scope; `infer_type`
            // will return None for anything uninferable here.
            let mut inner = reg.clone();
            inner.register(binding.clone(), Type::TypeParameter(0));
            ctx.with_scope(&[binding.clone()], |ctx| {
                validate_node(some_branch, ctx, &mut inner);
            });
            validate_node(none_branch, ctx, reg);
        }

        IRNode::Call {
            function,
            args,
            type_args: _,
        } => {
            // Validate all arguments.
            for arg in args {
                validate_node(arg, ctx, reg);
            }

            // Check function exists and arity matches. Skip native functions —
            // their parameter lists are stubs (the real signatures live in Lean),
            // so an arity check here is meaningless.
            if let Some(callee) = ctx.program.functions.try_get(function) {
                if !callee.is_native {
                    // Arity is value params + injected proof params (`hinv`/`hpre`),
                    // matching the binders the renderer emits and the args call
                    // sites thread.
                    let expected_arity = callee.signature.arity();
                    if args.len() != expected_arity {
                        ctx.error(format!(
                            "Function {} expects {} arguments but got {}",
                            callee.name,
                            expected_arity,
                            args.len()
                        ));
                    }
                }
            }
            // Note: function might not exist yet (mutual recursion), that's OK.
        }

        IRNode::Tuple(elems) => {
            for elem in elems {
                validate_node(elem, ctx, reg);
            }
        }

        IRNode::BinOp { lhs, rhs, .. } => {
            validate_node(lhs, ctx, reg);
            validate_node(rhs, ctx, reg);
        }

        IRNode::UnOp { operand, .. } => {
            validate_node(operand, ctx, reg);
        }

        IRNode::BitOp(bitop) => {
            use crate::BitOp;
            match bitop {
                BitOp::Extract { operand, .. } => {
                    validate_node(operand, ctx, reg);
                }
                BitOp::Concat { high, low } => {
                    validate_node(high, ctx, reg);
                    validate_node(low, ctx, reg);
                }
                BitOp::ZeroExtend { operand, .. } | BitOp::SignExtend { operand, .. } => {
                    validate_node(operand, ctx, reg);
                }
            }
        }

        IRNode::Field { base, .. } => {
            validate_node(base, ctx, reg);
        }

        IRNode::Pack { fields, .. } => {
            for field in fields {
                validate_node(field, ctx, reg);
            }
        }

        IRNode::Unpack { value, .. } => {
            validate_node(value, ctx, reg);
        }

        IRNode::UpdateField { base, value, .. } => {
            validate_node(base, ctx, reg);
            validate_node(value, ctx, reg);
        }

        IRNode::UpdateVec { base, index, value } => {
            validate_node(base, ctx, reg);
            validate_node(index, ctx, reg);
            validate_node(value, ctx, reg);
        }

        IRNode::MutableBorrow {
            val_expr,
            reconstruct_expr,
            reconstruct_param,
            state_type,
            ..
        } => {
            validate_node(val_expr, ctx, reg);
            // reconstruct_expr uses reconstruct_param as a bound variable.
            let mut inner = reg.clone();
            inner.register(reconstruct_param.clone(), state_type.clone());
            ctx.with_scope(&[reconstruct_param.clone()], |ctx| {
                validate_node(reconstruct_expr, ctx, &mut inner);
            });
        }

        IRNode::ReadRef(inner) => {
            validate_node(inner, ctx, reg);
        }

        IRNode::WriteRef { reference, value } => {
            validate_node(reference, ctx, reg);
            validate_node(value, ctx, reg);
        }

        IRNode::Quantifier {
            callback,
            lambda_param,
            lambda_type,
            collection,
            range,
            ..
        } => {
            let mut inner = reg.clone();
            inner.register(lambda_param.clone(), lambda_type.clone());
            ctx.with_scope(&[lambda_param.clone()], |ctx| {
                validate_node(callback, ctx, &mut inner);
            });
            if let Some(coll) = collection {
                validate_node(coll, ctx, reg);
            }
            if let Some((lo, hi)) = range {
                validate_node(lo, ctx, reg);
                validate_node(hi, ctx, reg);
            }
        }

        IRNode::ToProp(inner) | IRNode::ToBool(inner) => {
            validate_node(inner, ctx, reg);
        }

        IRNode::OptionSome(inner) => {
            validate_node(inner, ctx, reg);
        }

        IRNode::WriteBack { child, parent, .. } => {
            if !ctx.scope.contains(child) && child.as_ref() != "_" {
                ctx.error(format!("WriteBack child undefined: {}", child));
            }
            if !ctx.scope.contains(parent) && parent.as_ref() != "_" {
                ctx.error(format!("WriteBack parent undefined: {}", parent));
            }
        }

        IRNode::MutableCompose { inner, outer } => {
            if !ctx.scope.contains(inner) && inner.as_ref() != "_" {
                ctx.error(format!("MutableCompose inner undefined: {}", inner));
            }
            if !ctx.scope.contains(outer) && outer.as_ref() != "_" {
                ctx.error(format!("MutableCompose outer undefined: {}", outer));
            }
        }

        IRNode::Abort { code } => {
            if let Some(code) = code {
                validate_node(code, ctx, reg);
            }
        }

        IRNode::MoveAbortValue { code, .. } => {
            validate_node(code, ctx, reg);
        }

        IRNode::ArithOverflowCheck { lhs, rhs, .. } => {
            validate_node(lhs, ctx, reg);
            validate_node(rhs, ctx, reg);
        }

        // Terminal nodes - no validation needed.
        IRNode::Const(_) | IRNode::Inhabited | IRNode::OptionNone => {}
    }
}

/// Infer the type of an IR node (simplified - returns None if unknown).
/// `reg` tracks in-scope variable types at the current walk position.
fn infer_type(node: &IRNode, ctx: &ValidationCtx, reg: &VariableRegistry) -> Option<Type> {
    match node {
        IRNode::Tuple(elems) => {
            if elems.is_empty() {
                Some(Type::Tuple(vec![]))
            } else {
                let elem_types: Option<Vec<Type>> =
                    elems.iter().map(|e| infer_type(e, ctx, reg)).collect();
                elem_types.map(Type::Tuple)
            }
        }

        IRNode::Const(c) => Some(match c {
            crate::Const::Bool(_) => Type::Bool,
            crate::Const::UInt { bits, .. } => Type::UInt(*bits as u32),
            crate::Const::Address(_) => Type::Address,
            crate::Const::Vector { elem_type, .. } => Type::Vector(Box::new(elem_type.clone())),
        }),

        IRNode::Var(name) => {
            if reg.contains(name) {
                Some(reg.get_type(name).clone())
            } else {
                None
            }
        }

        IRNode::Let { body, .. } => {
            // Extend the registry with the Let's pattern for the body.
            let mut inner = reg.clone();
            inner.add_node(node);
            infer_type(body, ctx, &inner)
        }

        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => {
            let then_type = infer_type(then_branch, ctx, reg);
            let else_type = infer_type(else_branch, ctx, reg);
            then_type.or(else_type)
        }

        IRNode::Call { function, .. } => ctx
            .program
            .functions
            .try_get(function)
            .map(|f| f.signature.return_type.clone()),

        IRNode::BinOp { op, .. } => {
            use crate::BinOp;
            match op {
                BinOp::Eq
                | BinOp::Neq
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::And
                | BinOp::Or => Some(Type::Bool),
                _ => None,
            }
        }

        IRNode::UnOp { op, .. } => {
            use crate::UnOp;
            match op {
                UnOp::Not => Some(Type::Bool),
                UnOp::BitNot => None,
                UnOp::Cast(bits) => Some(Type::UInt(*bits as u32)),
            }
        }

        IRNode::ReadRef(inner) => {
            if let Some(Type::MutableReference(val_type, _)) = infer_type(inner, ctx, reg) {
                Some(*val_type)
            } else {
                None
            }
        }

        _ => None,
    }
}

/// Check if two types are compatible (simplified check)
fn types_compatible(actual: &Type, expected: &Type) -> bool {
    match (actual, expected) {
        // Unit types
        (Type::Tuple(a), Type::Tuple(b)) if a.is_empty() && b.is_empty() => true,

        // Same simple types
        (Type::Bool, Type::Bool) | (Type::Prop, Type::Prop) | (Type::Address, Type::Address) => {
            true
        }

        // UInt - check bit width
        (Type::UInt(a), Type::UInt(b)) => a == b,

        // Type parameters are always compatible (we can't check them statically)
        (Type::TypeParameter(_), _) | (_, Type::TypeParameter(_)) => true,

        // Tuples - check element-wise
        (Type::Tuple(a), Type::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| types_compatible(x, y))
        }

        // Structs
        (Type::Struct { struct_id: id1, .. }, Type::Struct { struct_id: id2, .. }) => id1 == id2,

        // MutableReference - check inner types
        (Type::MutableReference(v1, _), Type::MutableReference(v2, _)) => types_compatible(v1, v2),

        // Vector
        (Type::Vector(e1), Type::Vector(e2)) => types_compatible(e1, e2),

        // Option
        (Type::Option(e1), Type::Option(e2)) => types_compatible(e1, e2),

        // Reference
        (Type::Reference(e1), Type::Reference(e2)) => types_compatible(e1, e2),

        // For everything else, be permissive
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_types_compatible() {
        assert!(types_compatible(&Type::Bool, &Type::Bool));
        assert!(types_compatible(&Type::UInt(64), &Type::UInt(64)));
        assert!(types_compatible(&Type::Tuple(vec![]), &Type::Tuple(vec![])));
        // UInt width mismatches are caught by the explicit UInt arm.
        assert!(!types_compatible(&Type::UInt(32), &Type::UInt(64)));
        // Cross-category pairs (Bool/UInt, etc.) intentionally fall
        // through to the permissive default. Validation is non-fatal,
        // and the rendered code carries the actual types — we don't
        // want spurious warnings on unhandled pairings.
        assert!(types_compatible(&Type::Bool, &Type::UInt(64)));
    }
}
