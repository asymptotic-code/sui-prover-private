//! Base IR validator.
//!
//! See `plans/lean-pipeline/ir.md` "Validator invariants" and
//! `plans/lean-pipeline/testing-strategy.md` "Validator architecture".
//!
//! This module owns the always-on, stage-agnostic IR well-formedness
//! checks. Each pipeline stage adds its own postcondition wrapper that
//! calls `validate_program` first and then runs stage-specific checks
//! on top.
//!
//! Every pipeline stage's `run()` is expected to call its own
//! `postcondition::check` at the end (gated behind
//! `cfg(debug_assertions)` so production builds aren't slowed by
//! validation).

use std::collections::{BTreeMap, BTreeSet};

use super::analysis::scope::{walk_typed_block, TypedScope, TypedScopeVisitor};
use super::analysis::type_of::{type_of, TypeOfError};
use super::expr::{Block, BlockTail, Expr, MatchArm, Stmt};
use super::function::Function;
use super::ops::BitOp;
use super::path::PathStep;
use super::program::{GlobalDefinition, Program, StaticValue};
use super::quant::QuantDomain;
use super::{FunId, GlobalId, ModId, StructId, Type, VarId};

/// A validation error with enough context to point at the offending site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidationError {
    pub function: Option<FunId>,
    pub kind: ValidationErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationErrorKind {
    /// `Stmt::Let { pattern, .. }` where every position is `None`
    /// (or the pattern itself is empty). Use `Stmt::Eval` for
    /// side-effect-only statements.
    AllWildcardLet,
    /// A `Var(name)` was referenced but no enclosing binder defines it.
    UnboundVariable(VarId),
    /// `Tuple` pattern length doesn't match `Tuple` value arity.
    TuplePatternArityMismatch { pattern: usize, value: usize },
    /// `MatchArm::bindings` length doesn't match the variant's field count.
    MatchArmArityMismatch {
        variant: usize,
        bindings: usize,
        fields: usize,
    },
    /// An enum tag is missing or unresolved, or a plain struct carries one.
    InvalidVariantTag {
        struct_id: StructId,
        variant: Option<usize>,
    },
    /// The same name appears more than once in one match-arm pattern.
    DuplicateMatchArmBinding { variant: usize, binding: VarId },
    /// `Pack { fields }` length doesn't match the struct/variant's field count.
    PackArityMismatch {
        struct_id: StructId,
        variant: Option<usize>,
        provided: usize,
        expected: usize,
    },
    /// `Call::fun` doesn't resolve to any registered `Function`.
    UnknownFunctionId(FunId),
    /// A global reference or function-global side-table entry does not
    /// resolve in `Program::globals`.
    UnknownGlobalId(GlobalId),
    /// A writeback targets a readonly global.
    ImmutableGlobalWrite(GlobalId),
    /// `WriteRef` may not update through an immutable reference -- the
    /// shape a readonly C global's `BorrowGlobal` produces. A value-typed
    /// operand is NOT a violation: `stage_04_ghost` lowers
    /// `*ghost::borrow_mut<K, V>() = e` onto the threaded ghost var,
    /// which carries the ghost's value type.
    WriteRefThroughImmutableReference { actual: Type },
    /// `Program::function_globals` must list globals in strictly increasing
    /// `GlobalId` order.
    FunctionGlobalsOutOfOrder { previous: GlobalId, next: GlobalId },
    /// The same global appears more than once for one function.
    DuplicateFunctionGlobal(GlobalId),
    /// Two global bindings claim the same hidden parameter.
    DuplicateFunctionGlobalParam(usize),
    /// A threaded-global side-table entry has no matching hidden parameter.
    MissingFunctionGlobalParam {
        global: GlobalId,
        parameter_index: usize,
    },
    /// A hidden global parameter's type does not match its declaration's
    /// readonly/mutable threading type.
    FunctionGlobalParamTypeMismatch {
        global: GlobalId,
        expected: Type,
        actual: Type,
    },
    /// `Type::Struct { struct_id, .. }` (or any IR node referencing one)
    /// points at an unregistered struct.
    UnknownStructId(StructId),
    /// A global's struct application has the wrong number of type arguments.
    GlobalStructTypeArgumentArityMismatch {
        global: GlobalId,
        struct_id: StructId,
        expected: usize,
        actual: usize,
    },
    /// Global declarations are closed types and therefore cannot refer to a
    /// function-local type parameter.
    GlobalTypeParameter { global: GlobalId, index: u16 },
    /// Stored global values are pointer-free computational data. Reference,
    /// mutable-reference, and proposition types are not valid storage types.
    InvalidGlobalStorageType {
        global: GlobalId,
        kind: &'static str,
    },
    /// A defined global's closed startup value has a different shape or
    /// scalar type than its declaration.
    GlobalInitializerTypeMismatch {
        global: GlobalId,
        expected: Type,
        actual: &'static str,
    },
    /// A scalar startup value is not representable at its declared bit width.
    /// Reject it instead of relying on Lean's modular `OfNat` fallback.
    GlobalInitializerScalarOutOfRange { global: GlobalId, bits: u32 },
    /// A tuple, vector-backed explicit aggregate, or struct initializer has
    /// the wrong number of children for its declared type.
    GlobalInitializerArityMismatch {
        global: GlobalId,
        aggregate: &'static str,
        expected: usize,
        actual: usize,
    },
    /// A struct initializer explicitly names a different known declaration
    /// from the one in the global's expected type.
    GlobalInitializerStructMismatch {
        global: GlobalId,
        expected: StructId,
        actual: StructId,
    },
    /// `Function::module` (or any IR node referencing a module) points at
    /// an unregistered module.
    UnknownModuleId(ModId),
    /// `Quantifier::body`'s tail is not `BlockTail::Value(_)`. Quantifier
    /// bodies are pure logical predicates -- jumps inside the body are
    /// nonsensical.
    QuantifierBodyMustBeValue,
    /// `BlockTail::Break { level }` (or `Continue`) referenced a level
    /// deeper than the enclosing `While` nesting.
    JumpLevelOutOfBounds { level: u32, depth: u32 },
    /// `BlockTail::ReturnFromBlock { level }` referenced a level deeper
    /// than the enclosing `LabeledBlock` nesting.
    LabeledReturnLevelOutOfBounds { level: u32, depth: u32 },
    /// `Expr::While::header.tail` is not `BlockTail::Value(Expr::Unit)`.
    /// The header is meant for cond-computation side effects only;
    /// it never produces a value. See `plans/lean-pipeline/ir.md`
    /// decision-log §17.
    WhileHeaderTailMustBeValueUnit,
    /// `Expr::While::header_exit_locals` does not have one entry per
    /// `iter_locals` slot. The two vectors are positionally parallel: entry
    /// `i` of `header_exit_locals` is the SSA name carrying slot `i`'s value
    /// after the per-iteration `header` has run.
    ///
    /// This is checkable at EVERY stage, not just after stage 5: stages 1-4
    /// emit both vectors empty (equal arity, trivially) and stage 5 derives
    /// both from the same `loop_state`, so equal arity is a whole-pipeline
    /// invariant rather than a stage-5-only postcondition. Enforcing it here
    /// catches a bad producer at the stage boundary that made it, instead of
    /// deep inside stage 7's loop extraction where the same defect surfaces
    /// as `Stage7Error::HeaderExitArityMismatch`.
    HeaderExitArityMismatch {
        iter_locals: usize,
        header_exit_locals: usize,
    },
}

/// Run all base validation checks on the program.
pub fn validate_program(program: &Program) -> Result<(), ValidationError> {
    validate_global_declarations(program)?;

    validate_function_globals(program)?;

    for (&id, func) in &program.functions {
        validate_function(program, id, func)?;
    }
    Ok(())
}

/// Validate the closed, pointer-free value schema of every external global.
/// Kept separate so the renderer can fail before entering its infallible type
/// printer even when called directly on frontend-built IR.
pub(crate) fn validate_global_declarations(program: &Program) -> Result<(), ValidationError> {
    for (&global_id, global) in &program.globals {
        if !program.modules.contains_key(&global.module_id) {
            return Err(ValidationError {
                function: None,
                kind: ValidationErrorKind::UnknownModuleId(global.module_id),
            });
        }
        validate_global_type(program, global_id, &global.ty)?;
        if let GlobalDefinition::Defined { startup_value } = &global.definition {
            validate_static_value(program, global_id, &global.ty, startup_value)?;
        }
    }
    Ok(())
}

fn validate_static_value(
    program: &Program,
    global: GlobalId,
    expected: &Type,
    value: &StaticValue,
) -> Result<(), ValidationError> {
    let mismatch = || ValidationError {
        function: None,
        kind: ValidationErrorKind::GlobalInitializerTypeMismatch {
            global,
            expected: expected.clone(),
            actual: static_value_kind(value),
        },
    };

    match value {
        StaticValue::Unit if matches!(expected, Type::Unit) => Ok(()),
        StaticValue::Bool(_) if matches!(expected, Type::Bool) => Ok(()),
        StaticValue::UInt { bits, value } if matches!(expected, Type::UInt(expected_bits) if bits == expected_bits) =>
        {
            if *bits < 256 && *value >= (ethnum::U256::ONE << *bits) {
                return Err(ValidationError {
                    function: None,
                    kind: ValidationErrorKind::GlobalInitializerScalarOutOfRange {
                        global,
                        bits: *bits,
                    },
                });
            }
            Ok(())
        }
        StaticValue::Address(value) if matches!(expected, Type::Address) => {
            if value.bits() > 256 {
                return Err(ValidationError {
                    function: None,
                    kind: ValidationErrorKind::GlobalInitializerScalarOutOfRange {
                        global,
                        bits: 256,
                    },
                });
            }
            Ok(())
        }
        StaticValue::Vector(elements) => {
            let Type::Vector(element_type) = expected else {
                return Err(mismatch());
            };
            for element in elements {
                validate_static_value(program, global, element_type, element)?;
            }
            Ok(())
        }
        StaticValue::Repeat { value, .. } => {
            let Type::Vector(element_type) = expected else {
                return Err(mismatch());
            };
            validate_static_value(program, global, element_type, value)
        }
        StaticValue::Tuple(elements) => {
            let Type::Tuple(element_types) = expected else {
                return Err(mismatch());
            };
            if elements.len() != element_types.len() {
                return Err(ValidationError {
                    function: None,
                    kind: ValidationErrorKind::GlobalInitializerArityMismatch {
                        global,
                        aggregate: "Tuple",
                        expected: element_types.len(),
                        actual: elements.len(),
                    },
                });
            }
            for (element, element_type) in elements.iter().zip(element_types) {
                validate_static_value(program, global, element_type, element)?;
            }
            Ok(())
        }
        StaticValue::Struct {
            struct_id,
            variant,
            fields,
        } => {
            // Validate the ID carried by the value independently of the
            // expected type. This prevents a mismatched or unknown ID from
            // being hidden behind a generic shape error.
            let value_declaration = program.structs.get(struct_id).ok_or(ValidationError {
                function: None,
                kind: ValidationErrorKind::UnknownStructId(*struct_id),
            })?;
            if !program.modules.contains_key(&value_declaration.module_id) {
                return Err(ValidationError {
                    function: None,
                    kind: ValidationErrorKind::UnknownModuleId(value_declaration.module_id),
                });
            }

            let Type::Struct {
                struct_id: expected_struct,
                type_args,
            } = expected
            else {
                return Err(mismatch());
            };
            if struct_id != expected_struct {
                return Err(ValidationError {
                    function: None,
                    kind: ValidationErrorKind::GlobalInitializerStructMismatch {
                        global,
                        expected: *expected_struct,
                        actual: *struct_id,
                    },
                });
            }

            let declaration = &program.structs[expected_struct];
            let field_declarations = match (&declaration.variants, variant) {
                (None, None) => &declaration.fields,
                (Some(variants), Some(tag)) => {
                    &variants
                        .iter()
                        .find(|candidate| candidate.tag == *tag)
                        .ok_or(ValidationError {
                            function: None,
                            kind: ValidationErrorKind::InvalidVariantTag {
                                struct_id: *struct_id,
                                variant: Some(*tag),
                            },
                        })?
                        .fields
                }
                _ => {
                    return Err(ValidationError {
                        function: None,
                        kind: ValidationErrorKind::InvalidVariantTag {
                            struct_id: *struct_id,
                            variant: *variant,
                        },
                    });
                }
            };
            if fields.len() != field_declarations.len() {
                return Err(ValidationError {
                    function: None,
                    kind: ValidationErrorKind::GlobalInitializerArityMismatch {
                        global,
                        aggregate: "Struct",
                        expected: field_declarations.len(),
                        actual: fields.len(),
                    },
                });
            }
            for (field, declaration) in fields.iter().zip(field_declarations) {
                let field_type = instantiate_global_field_type(&declaration.field_type, type_args)
                    .map_err(|index| ValidationError {
                        function: None,
                        kind: ValidationErrorKind::GlobalTypeParameter { global, index },
                    })?;
                validate_static_value(program, global, &field_type, field)?;
            }
            Ok(())
        }
        _ => Err(mismatch()),
    }
}

fn static_value_kind(value: &StaticValue) -> &'static str {
    match value {
        StaticValue::Unit => "Unit",
        StaticValue::Bool(_) => "Bool",
        StaticValue::UInt { .. } => "UInt",
        StaticValue::Address(_) => "Address",
        StaticValue::Vector(_) => "Vector",
        StaticValue::Repeat { .. } => "Repeat",
        StaticValue::Tuple(_) => "Tuple",
        StaticValue::Struct { .. } => "Struct",
    }
}

fn validate_global_type(
    program: &Program,
    global: GlobalId,
    ty: &Type,
) -> Result<(), ValidationError> {
    validate_global_type_inner(program, global, ty, &mut BTreeSet::new())
}

fn validate_global_type_inner(
    program: &Program,
    global: GlobalId,
    ty: &Type,
    visiting_structs: &mut BTreeSet<StructId>,
) -> Result<(), ValidationError> {
    match ty {
        Type::Struct {
            struct_id,
            type_args,
        } => {
            let declaration = program.structs.get(struct_id).ok_or(ValidationError {
                function: None,
                kind: ValidationErrorKind::UnknownStructId(*struct_id),
            })?;
            if !program.modules.contains_key(&declaration.module_id) {
                return Err(ValidationError {
                    function: None,
                    kind: ValidationErrorKind::UnknownModuleId(declaration.module_id),
                });
            }
            if type_args.len() != declaration.type_params.len() {
                return Err(ValidationError {
                    function: None,
                    kind: ValidationErrorKind::GlobalStructTypeArgumentArityMismatch {
                        global,
                        struct_id: *struct_id,
                        expected: declaration.type_params.len(),
                        actual: type_args.len(),
                    },
                });
            }
            for type_arg in type_args {
                validate_global_type_inner(program, global, type_arg, visiting_structs)?;
            }

            // A struct-valued global is pointer-free only when its complete
            // stored field closure is pointer-free. A StructId guard is
            // sufficient for recursive declarations: every actual type
            // argument is checked before the guard, and the declaration's
            // field shape was already visited on this recursion path.
            if !visiting_structs.insert(*struct_id) {
                return Ok(());
            }
            for field_type in
                declaration
                    .fields
                    .iter()
                    .map(|field| &field.field_type)
                    .chain(
                        declaration.variants.iter().flatten().flat_map(|variant| {
                            variant.fields.iter().map(|field| &field.field_type)
                        }),
                    )
            {
                let instantiated =
                    instantiate_global_field_type(field_type, type_args).map_err(|index| {
                        ValidationError {
                            function: None,
                            kind: ValidationErrorKind::GlobalTypeParameter { global, index },
                        }
                    })?;
                validate_global_type_inner(program, global, &instantiated, visiting_structs)?;
            }
            visiting_structs.remove(struct_id);
        }
        Type::Vector(inner) => {
            validate_global_type_inner(program, global, inner, visiting_structs)?;
        }
        Type::Tuple(items) => {
            for item in items {
                validate_global_type_inner(program, global, item, visiting_structs)?;
            }
        }
        Type::TypeParam(index) => {
            return Err(ValidationError {
                function: None,
                kind: ValidationErrorKind::GlobalTypeParameter {
                    global,
                    index: *index,
                },
            });
        }
        Type::Reference(_) => {
            return Err(ValidationError {
                function: None,
                kind: ValidationErrorKind::InvalidGlobalStorageType {
                    global,
                    kind: "Reference",
                },
            });
        }
        Type::MutableRef { .. } => {
            return Err(ValidationError {
                function: None,
                kind: ValidationErrorKind::InvalidGlobalStorageType {
                    global,
                    kind: "MutableRef",
                },
            });
        }
        Type::Prop => {
            return Err(ValidationError {
                function: None,
                kind: ValidationErrorKind::InvalidGlobalStorageType {
                    global,
                    kind: "Prop",
                },
            });
        }
        Type::Unit | Type::Bool | Type::UInt(_) | Type::Address => {}
    }
    Ok(())
}

pub(crate) fn instantiate_global_field_type(ty: &Type, type_args: &[Type]) -> Result<Type, u16> {
    Ok(match ty {
        Type::TypeParam(index) => type_args.get(*index as usize).cloned().ok_or(*index)?,
        Type::Vector(inner) => {
            Type::Vector(Box::new(instantiate_global_field_type(inner, type_args)?))
        }
        Type::Tuple(items) => Type::Tuple(
            items
                .iter()
                .map(|item| instantiate_global_field_type(item, type_args))
                .collect::<Result<_, _>>()?,
        ),
        Type::Struct {
            struct_id,
            type_args: nested_args,
        } => Type::Struct {
            struct_id: *struct_id,
            type_args: nested_args
                .iter()
                .map(|arg| instantiate_global_field_type(arg, type_args))
                .collect::<Result<_, _>>()?,
        },
        Type::Reference(inner) => {
            Type::Reference(Box::new(instantiate_global_field_type(inner, type_args)?))
        }
        Type::MutableRef { inner, root } => Type::MutableRef {
            inner: Box::new(instantiate_global_field_type(inner, type_args)?),
            root: Box::new(instantiate_global_field_type(root, type_args)?),
        },
        Type::Unit => Type::Unit,
        Type::Bool => Type::Bool,
        Type::Prop => Type::Prop,
        Type::UInt(width) => Type::UInt(*width),
        Type::Address => Type::Address,
    })
}

fn validate_function_globals(program: &Program) -> Result<(), ValidationError> {
    for (&fid, bindings) in &program.function_globals {
        let func = program.functions.get(&fid).ok_or(ValidationError {
            function: Some(fid),
            kind: ValidationErrorKind::UnknownFunctionId(fid),
        })?;

        for pair in bindings.windows(2) {
            if pair[0].global == pair[1].global {
                return Err(ValidationError {
                    function: Some(fid),
                    kind: ValidationErrorKind::DuplicateFunctionGlobal(pair[0].global),
                });
            }
            if pair[0].global > pair[1].global {
                return Err(ValidationError {
                    function: Some(fid),
                    kind: ValidationErrorKind::FunctionGlobalsOutOfOrder {
                        previous: pair[0].global,
                        next: pair[1].global,
                    },
                });
            }
        }

        let mut bound_vars = BTreeSet::new();
        for binding in bindings {
            if !bound_vars.insert(binding.parameter_index) {
                return Err(ValidationError {
                    function: Some(fid),
                    kind: ValidationErrorKind::DuplicateFunctionGlobalParam(
                        binding.parameter_index,
                    ),
                });
            }
            let Some(global) = program.globals.get(&binding.global) else {
                return Err(ValidationError {
                    function: Some(fid),
                    kind: ValidationErrorKind::UnknownGlobalId(binding.global),
                });
            };
            let Some(param) = func.signature.params.get(binding.parameter_index) else {
                return Err(ValidationError {
                    function: Some(fid),
                    kind: ValidationErrorKind::MissingFunctionGlobalParam {
                        global: binding.global,
                        parameter_index: binding.parameter_index,
                    },
                });
            };
            let expected = global.threaded_param_type();
            if param.ty != expected {
                return Err(ValidationError {
                    function: Some(fid),
                    kind: ValidationErrorKind::FunctionGlobalParamTypeMismatch {
                        global: binding.global,
                        expected,
                        actual: param.ty.clone(),
                    },
                });
            }
        }
    }
    Ok(())
}

fn validate_function(program: &Program, id: FunId, func: &Function) -> Result<(), ValidationError> {
    if !program.modules.contains_key(&func.module) {
        return Err(ValidationError {
            function: Some(id),
            kind: ValidationErrorKind::UnknownModuleId(func.module),
        });
    }

    if block_exceeds_inline_validation_depth(&func.body) {
        return validate_deep_function_body(program, id, func);
    }

    validate_function_body(program, id, func)
}

fn validate_function_body(
    program: &Program,
    id: FunId,
    func: &Function,
) -> Result<(), ValidationError> {
    let mut scope: BTreeSet<VarId> = func
        .signature
        .params
        .iter()
        .map(|p| p.var.clone())
        .collect();

    let ctx = Ctx {
        program,
        function: id,
        loop_depth: 0,
        label_depth: 0,
    };
    ctx.check_block(&func.body, &mut scope)?;
    validate_write_refs(program, id, func)
}

// The validator mirrors lexical scope directly, so its recursive call depth is
// proportional to IR nesting. Most functions are shallow and should stay on
// the caller's stack. Generated control-flow helpers can legitimately contain
// hundreds of nested Match/Block nodes, though, especially after abort
// defunctionalization. Detect those with an iterative walk and validate just
// that function on a bounded, explicitly sized stack. This preserves every
// structural and typed validation check; it only makes their stack budget
// independent of the thread which invoked the pipeline.
const INLINE_VALIDATION_DEPTH: usize = 128;
const DEEP_VALIDATION_STACK_BYTES: usize = 64 * 1024 * 1024;

fn validate_deep_function_body(
    program: &Program,
    id: FunId,
    func: &Function,
) -> Result<(), ValidationError> {
    // The iterative precheck already established that this function is deep,
    // so grow unconditionally. `maybe_grow` would inspect only the stack
    // remaining *before* validation and could leave an ordinary 8 MiB caller
    // stack in place even though the upcoming recursive walk needs more.
    stacker::grow(DEEP_VALIDATION_STACK_BYTES, || {
        validate_function_body(program, id, func)
    })
}

enum ValidationDepthNode<'a> {
    Block(&'a Block),
    Expr(&'a Expr),
}

fn block_exceeds_inline_validation_depth(block: &Block) -> bool {
    let mut pending = vec![(ValidationDepthNode::Block(block), 1usize)];
    while let Some((node, depth)) = pending.pop() {
        if depth > INLINE_VALIDATION_DEPTH {
            return true;
        }
        let child_depth = depth + 1;
        match node {
            ValidationDepthNode::Block(block) => {
                for stmt in &block.stmts {
                    let expr = match stmt {
                        Stmt::Let { value, .. } | Stmt::Eval(value) => value,
                    };
                    pending.push((ValidationDepthNode::Expr(expr), child_depth));
                }
                let tail_expr = match &block.tail {
                    BlockTail::Value(expr) => expr,
                    BlockTail::Break { value: expr, .. }
                    | BlockTail::Continue { value: expr, .. }
                    | BlockTail::Return(expr)
                    | BlockTail::ReturnFromBlock { value: expr, .. } => expr.as_ref(),
                    BlockTail::Abort { code } => code.as_ref(),
                };
                pending.push((ValidationDepthNode::Expr(tail_expr), child_depth));
            }
            ValidationDepthNode::Expr(expr) => match expr {
                Expr::Var(_)
                | Expr::Const(_)
                | Expr::Unit
                | Expr::BorrowLoc(_)
                | Expr::BorrowGlobal(_)
                | Expr::WriteBack { .. }
                | Expr::IsParent { .. } => {}
                Expr::BinOp { lhs, rhs, .. } => {
                    pending.push((ValidationDepthNode::Expr(lhs), child_depth));
                    pending.push((ValidationDepthNode::Expr(rhs), child_depth));
                }
                Expr::UnOp { operand, .. }
                | Expr::Unpack { value: operand, .. }
                | Expr::Field { base: operand, .. }
                | Expr::ReadRef(operand)
                | Expr::ToProp(operand)
                | Expr::ToBool(operand) => {
                    pending.push((ValidationDepthNode::Expr(operand), child_depth));
                }
                Expr::BitOp(op) => match op {
                    BitOp::Extract { operand, .. }
                    | BitOp::ZeroExtend { operand, .. }
                    | BitOp::SignExtend { operand, .. } => {
                        pending.push((ValidationDepthNode::Expr(operand), child_depth));
                    }
                    BitOp::Concat { high, low } => {
                        pending.push((ValidationDepthNode::Expr(high), child_depth));
                        pending.push((ValidationDepthNode::Expr(low), child_depth));
                    }
                },
                Expr::Call { args, .. } | Expr::Tuple(args) => {
                    for arg in args {
                        pending.push((ValidationDepthNode::Expr(arg), child_depth));
                    }
                }
                Expr::Pack { fields, .. } => {
                    for field in fields {
                        pending.push((ValidationDepthNode::Expr(field), child_depth));
                    }
                }
                Expr::If {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    pending.push((ValidationDepthNode::Expr(cond), child_depth));
                    pending.push((ValidationDepthNode::Block(then_branch), child_depth));
                    pending.push((ValidationDepthNode::Block(else_branch), child_depth));
                }
                Expr::Match {
                    selector, cases, ..
                } => {
                    pending.push((ValidationDepthNode::Expr(selector), child_depth));
                    for case in cases {
                        pending.push((ValidationDepthNode::Block(&case.body), child_depth));
                    }
                }
                Expr::While {
                    header,
                    cond,
                    body,
                    iter_locals,
                    ..
                } => {
                    pending.push((ValidationDepthNode::Block(header), child_depth));
                    pending.push((ValidationDepthNode::Expr(cond), child_depth));
                    pending.push((ValidationDepthNode::Block(body), child_depth));
                    for (_, init) in iter_locals {
                        pending.push((ValidationDepthNode::Expr(init), child_depth));
                    }
                }
                Expr::Borrow { step, base } => {
                    for operand in step.exprs() {
                        pending.push((ValidationDepthNode::Expr(operand), child_depth));
                    }
                    pending.push((ValidationDepthNode::Expr(base), child_depth));
                }
                Expr::Update { step, base, value } => {
                    for operand in step.exprs() {
                        pending.push((ValidationDepthNode::Expr(operand), child_depth));
                    }
                    pending.push((ValidationDepthNode::Expr(base), child_depth));
                    pending.push((ValidationDepthNode::Expr(value), child_depth));
                }
                Expr::WriteRef { reference, value } => {
                    pending.push((ValidationDepthNode::Expr(reference), child_depth));
                    pending.push((ValidationDepthNode::Expr(value), child_depth));
                }
                Expr::LabeledBlock { body, .. } => {
                    pending.push((ValidationDepthNode::Block(body), child_depth));
                }
                Expr::Quantifier { domain, body, .. } => {
                    match domain {
                        QuantDomain::Unbounded => {}
                        QuantDomain::Range { start, end } => {
                            pending.push((ValidationDepthNode::Expr(start), child_depth));
                            pending.push((ValidationDepthNode::Expr(end), child_depth));
                        }
                        QuantDomain::Collection(collection) => {
                            pending.push((ValidationDepthNode::Expr(collection), child_depth));
                        }
                        QuantDomain::VecRange { vec, start, end } => {
                            pending.push((ValidationDepthNode::Expr(vec), child_depth));
                            pending.push((ValidationDepthNode::Expr(start), child_depth));
                            pending.push((ValidationDepthNode::Expr(end), child_depth));
                        }
                    }
                    pending.push((ValidationDepthNode::Block(body), child_depth));
                }
            },
        }
    }
    false
}

/// Validate `WriteRef` at every site whose operand types can be recovered at
/// this stage: the operand may be a `MutableRef` or a plain value, but never
/// an immutable `Reference`. The base validator intentionally remains tolerant
/// of unrelated pre-SSA type-inference gaps: the typed walker may stop on one
/// of those, but any concrete `WriteRef` violation observed before that point
/// is still reported. The later `IrTypeInferenceSucceeds` invariant checks the
/// complete post-SSA program using the same [`type_of`] rule.
fn validate_write_refs(
    program: &Program,
    function: FunId,
    func: &Function,
) -> Result<(), ValidationError> {
    struct Validator<'a> {
        program: &'a Program,
        violation: Option<ValidationErrorKind>,
    }

    impl TypedScopeVisitor for Validator<'_> {
        type Error = TypeOfError;

        fn visit_expr(&mut self, expr: &Expr, scope: &TypedScope) -> Result<(), Self::Error> {
            if self.violation.is_some() {
                return Ok(());
            }
            let Expr::WriteRef { reference, .. } = expr else {
                return Ok(());
            };
            let Ok(reference_ty) = type_of(reference, scope, self.program) else {
                return Ok(());
            };
            if let Type::Reference(_) = reference_ty {
                self.violation = Some(ValidationErrorKind::WriteRefThroughImmutableReference {
                    actual: reference_ty,
                });
            }
            Ok(())
        }
    }

    let scope: BTreeMap<VarId, Type> = func
        .signature
        .params
        .iter()
        .map(|param| (param.var.clone(), param.ty.clone()))
        .collect();
    let mut validator = Validator {
        program,
        violation: None,
    };
    // Structural validation above remains authoritative for pre-SSA scope.
    // Ignore an unrelated inference failure here, but never a violation the
    // visitor already observed.
    let _ = walk_typed_block(&mut validator, &func.body, scope, program);
    match validator.violation {
        Some(kind) => Err(ValidationError {
            function: Some(function),
            kind,
        }),
        None => Ok(()),
    }
}

struct Ctx<'a> {
    program: &'a Program,
    function: FunId,
    loop_depth: u32,
    label_depth: u32,
}

impl<'a> Ctx<'a> {
    fn err(&self, kind: ValidationErrorKind) -> ValidationError {
        ValidationError {
            function: Some(self.function),
            kind,
        }
    }

    fn enter_loop(&self) -> Self {
        Ctx {
            program: self.program,
            function: self.function,
            loop_depth: self.loop_depth + 1,
            label_depth: self.label_depth,
        }
    }

    fn enter_label(&self) -> Self {
        Ctx {
            program: self.program,
            function: self.function,
            loop_depth: self.loop_depth,
            label_depth: self.label_depth + 1,
        }
    }

    fn check_block(
        &self,
        block: &Block,
        scope: &mut BTreeSet<VarId>,
    ) -> Result<(), ValidationError> {
        for stmt in &block.stmts {
            self.check_stmt(stmt, scope)?;
        }
        self.check_tail(&block.tail, scope)
    }

    fn check_stmt(&self, stmt: &Stmt, scope: &mut BTreeSet<VarId>) -> Result<(), ValidationError> {
        match stmt {
            Stmt::Let { pattern, value } => {
                if pattern.is_empty() || pattern.iter().all(|p| p.is_none()) {
                    return Err(self.err(ValidationErrorKind::AllWildcardLet));
                }
                self.check_expr(value, scope)?;
                if pattern.len() > 1 {
                    if let Expr::Tuple(elems) = value {
                        if elems.len() != pattern.len() {
                            return Err(self.err(ValidationErrorKind::TuplePatternArityMismatch {
                                pattern: pattern.len(),
                                value: elems.len(),
                            }));
                        }
                    }
                }
                for slot in pattern {
                    if let Some(v) = slot {
                        scope.insert(v.clone());
                    }
                }
                Ok(())
            }
            Stmt::Eval(e) => self.check_expr(e, scope),
        }
    }

    fn check_tail(
        &self,
        tail: &BlockTail,
        scope: &mut BTreeSet<VarId>,
    ) -> Result<(), ValidationError> {
        match tail {
            BlockTail::Value(e) => self.check_expr(e, scope),
            BlockTail::Break { level, value } | BlockTail::Continue { level, value } => {
                if *level >= self.loop_depth {
                    return Err(self.err(ValidationErrorKind::JumpLevelOutOfBounds {
                        level: *level,
                        depth: self.loop_depth,
                    }));
                }
                self.check_expr(value, scope)
            }
            BlockTail::Return(value) => self.check_expr(value, scope),
            BlockTail::ReturnFromBlock { level, value } => {
                if *level >= self.label_depth {
                    return Err(
                        self.err(ValidationErrorKind::LabeledReturnLevelOutOfBounds {
                            level: *level,
                            depth: self.label_depth,
                        }),
                    );
                }
                self.check_expr(value, scope)
            }
            BlockTail::Abort { code } => self.check_expr(code, scope),
        }
    }

    fn check_expr(&self, expr: &Expr, scope: &mut BTreeSet<VarId>) -> Result<(), ValidationError> {
        match expr {
            Expr::Var(v) => {
                if !scope.contains(v) {
                    return Err(self.err(ValidationErrorKind::UnboundVariable(v.clone())));
                }
                Ok(())
            }
            Expr::Const(_) | Expr::Unit => Ok(()),
            Expr::BorrowGlobal(global) => {
                if !self.program.globals.contains_key(global) {
                    return Err(self.err(ValidationErrorKind::UnknownGlobalId(*global)));
                }
                Ok(())
            }

            Expr::BinOp { lhs, rhs, .. } => {
                self.check_expr(lhs, scope)?;
                self.check_expr(rhs, scope)
            }
            Expr::UnOp { operand, .. } => self.check_expr(operand, scope),
            Expr::BitOp(op) => self.check_bit_op(op, scope),

            Expr::Call { fun, args, .. } => {
                if self.program.lookup_callee(*fun).is_none() {
                    return Err(self.err(ValidationErrorKind::UnknownFunctionId(*fun)));
                }
                for a in args {
                    self.check_expr(a, scope)?;
                }
                Ok(())
            }
            Expr::Tuple(elems) => {
                for e in elems {
                    self.check_expr(e, scope)?;
                }
                Ok(())
            }

            Expr::Pack {
                struct_id,
                variant,
                fields,
                ..
            } => {
                let s =
                    self.program.structs.get(struct_id).ok_or_else(|| {
                        self.err(ValidationErrorKind::UnknownStructId(*struct_id))
                    })?;
                let expected = self.selected_fields(*struct_id, s, *variant)?.len();
                if expected != fields.len() {
                    return Err(self.err(ValidationErrorKind::PackArityMismatch {
                        struct_id: *struct_id,
                        variant: *variant,
                        provided: fields.len(),
                        expected,
                    }));
                }
                for f in fields {
                    self.check_expr(f, scope)?;
                }
                Ok(())
            }
            Expr::Unpack {
                struct_id,
                variant,
                value,
            } => {
                let structure =
                    self.program.structs.get(struct_id).ok_or_else(|| {
                        self.err(ValidationErrorKind::UnknownStructId(*struct_id))
                    })?;
                self.selected_fields(*struct_id, structure, *variant)?;
                self.check_expr(value, scope)
            }
            Expr::Field {
                struct_id, base, ..
            } => {
                if !self.program.structs.contains_key(struct_id) {
                    return Err(self.err(ValidationErrorKind::UnknownStructId(*struct_id)));
                }
                self.check_expr(base, scope)
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.check_expr(cond, scope)?;
                self.check_block(then_branch, &mut scope.clone())?;
                self.check_block(else_branch, &mut scope.clone())
            }
            Expr::Match {
                struct_id,
                selector,
                cases,
            } => {
                let matched_struct =
                    self.program.structs.get(struct_id).ok_or_else(|| {
                        self.err(ValidationErrorKind::UnknownStructId(*struct_id))
                    })?;
                self.check_expr(selector, scope)?;
                for arm in cases {
                    let field_count = self
                        .selected_fields(*struct_id, matched_struct, Some(arm.variant))?
                        .len();
                    self.check_match_arm(field_count, arm, scope)?;
                }
                Ok(())
            }
            Expr::LabeledBlock { body, .. } => {
                // A labeled block in EVAL/sequencing position introduces its
                // result binding into the ENCLOSING scope: pre-stage-7,
                // `eval labeled_block { ..loop..; let $t = v }` is followed by
                // a use of `$t` outside the block (stage 7 later extracts the
                // block into a helper and rebinds `let $t = <helper>(..)`). So
                // thread the OUTER `scope` through rather than a throwaway
                // clone -- otherwise the escaping binding looks unbound at the
                // post-block use (e.g. `ascii::try_string`'s `$t2`). Bindings
                // made INSIDE a nested loop body still don't escape (the While
                // arm scopes those in its own cloned scope).
                let inner = self.enter_label();
                inner.check_block(body, scope)
            }

            Expr::While {
                header,
                cond,
                body,
                iter_locals,
                header_exit_locals,
                live_out: _,
            } => {
                // Header runs every iteration before cond is checked
                // and produces no value -- enforce the unit-tail
                // invariant here so consumers don't have to.
                if !matches!(&header.tail, BlockTail::Value(Expr::Unit)) {
                    return Err(self.err(ValidationErrorKind::WhileHeaderTailMustBeValueUnit));
                }
                // `header_exit_locals` is positionally parallel to
                // `iter_locals` (see the field doc on `Expr::While`). Stages
                // 1-4 leave both empty and stage 5 fills both from one
                // `loop_state`, so equal arity holds at every stage boundary
                // -- checking it here reports the producer that broke it
                // rather than letting stage 7's `extract_while` discover it
                // at the point of use.
                if header_exit_locals.len() != iter_locals.len() {
                    return Err(self.err(ValidationErrorKind::HeaderExitArityMismatch {
                        iter_locals: iter_locals.len(),
                        header_exit_locals: header_exit_locals.len(),
                    }));
                }
                // Each (binder, init) pair: walk `init` in the OUTER
                // scope (it runs once at loop entry, before the
                // binder is introduced). Then add the binder to
                // header_scope.
                let mut header_scope = scope.clone();
                for (binder, init) in iter_locals {
                    self.check_expr(init, scope)?;
                    header_scope.insert(binder.clone());
                }
                // The header runs every iteration as part of THIS loop, so a
                // `continue[0]` / `break[0]` inside it targets this loop --
                // check it (and the cond) at the incremented loop depth, same
                // as the body. Checking the header with the OUTER depth made a
                // header-position `continue[0]` (e.g. `oracle::binary_search`'s
                // search step) look like a jump out of a non-existent loop ->
                // spurious JumpLevelOutOfBounds{0,0}.
                let inner = self.enter_loop();
                inner.check_block(header, &mut header_scope)?;
                inner.check_expr(cond, &mut header_scope)?;
                inner.check_block(body, &mut header_scope.clone())
            }

            Expr::BorrowLoc(v) => {
                if !scope.contains(v) {
                    return Err(self.err(ValidationErrorKind::UnboundVariable(v.clone())));
                }
                Ok(())
            }
            Expr::ReadRef(inner) => self.check_expr(inner, scope),
            Expr::WriteRef { reference, value } => {
                self.check_expr(reference, scope)?;
                self.check_expr(value, scope)
            }
            Expr::WriteBack {
                node, child, world, ..
            } => {
                if !scope.contains(child) {
                    return Err(self.err(ValidationErrorKind::UnboundVariable(child.clone())));
                }
                self.check_borrow_node(node, scope)?;
                if let Some(world) = world {
                    if !scope.contains(world) {
                        return Err(self.err(ValidationErrorKind::UnboundVariable(world.clone())));
                    }
                }
                Ok(())
            }
            Expr::IsParent { node, child, .. } => {
                if !scope.contains(child) {
                    return Err(self.err(ValidationErrorKind::UnboundVariable(child.clone())));
                }
                self.check_borrow_node(node, scope)
            }
            Expr::Borrow { step, base } => {
                self.check_path_step(step, scope)?;
                self.check_expr(base, scope)
            }
            Expr::Update { step, base, value } => {
                self.check_path_step(step, scope)?;
                self.check_expr(base, scope)?;
                self.check_expr(value, scope)
            }

            Expr::ToProp(inner) | Expr::ToBool(inner) => self.check_expr(inner, scope),

            Expr::Quantifier {
                binder,
                domain,
                body,
                ..
            } => {
                match domain {
                    QuantDomain::Unbounded => {}
                    QuantDomain::Range { start, end } => {
                        self.check_expr(start, scope)?;
                        self.check_expr(end, scope)?;
                    }
                    QuantDomain::Collection(c) => self.check_expr(c, scope)?,
                    QuantDomain::VecRange { vec, start, end } => {
                        self.check_expr(vec, scope)?;
                        self.check_expr(start, scope)?;
                        self.check_expr(end, scope)?;
                    }
                }
                if !matches!(body.tail, BlockTail::Value(_)) {
                    return Err(self.err(ValidationErrorKind::QuantifierBodyMustBeValue));
                }
                let mut inner = scope.clone();
                inner.insert(binder.clone());
                self.check_block(body, &mut inner)
            }
        }
    }

    fn check_match_arm(
        &self,
        field_count: usize,
        arm: &MatchArm,
        scope: &BTreeSet<VarId>,
    ) -> Result<(), ValidationError> {
        if arm.bindings.len() != field_count {
            return Err(self.err(ValidationErrorKind::MatchArmArityMismatch {
                variant: arm.variant,
                bindings: arm.bindings.len(),
                fields: field_count,
            }));
        }
        let mut inner = scope.clone();
        let mut arm_bindings = BTreeSet::new();
        for v in &arm.bindings {
            if !arm_bindings.insert(v.clone()) {
                return Err(self.err(ValidationErrorKind::DuplicateMatchArmBinding {
                    variant: arm.variant,
                    binding: v.clone(),
                }));
            }
            inner.insert(v.clone());
        }
        self.check_block(&arm.body, &mut inner)
    }

    fn selected_fields<'b>(
        &self,
        struct_id: StructId,
        structure: &'b super::program::Struct,
        variant: Option<usize>,
    ) -> Result<&'b [super::program::Field], ValidationError> {
        match (&structure.variants, variant) {
            (None, None) => Ok(&structure.fields),
            (Some(_), Some(tag)) => structure
                .variant_by_tag(tag)
                .map(|variant| variant.fields.as_slice())
                .ok_or_else(|| {
                    self.err(ValidationErrorKind::InvalidVariantTag { struct_id, variant })
                }),
            _ => Err(self.err(ValidationErrorKind::InvalidVariantTag { struct_id, variant })),
        }
    }

    fn check_borrow_node(
        &self,
        node: &super::borrow::BorrowNode,
        scope: &BTreeSet<VarId>,
    ) -> Result<(), ValidationError> {
        match node {
            super::borrow::BorrowNode::LocalRoot(v) | super::borrow::BorrowNode::Reference(v) => {
                if !scope.contains(v) {
                    return Err(self.err(ValidationErrorKind::UnboundVariable(v.clone())));
                }
                Ok(())
            }
            super::borrow::BorrowNode::GlobalRoot(global) => {
                let decl = self
                    .program
                    .globals
                    .get(global)
                    .ok_or_else(|| self.err(ValidationErrorKind::UnknownGlobalId(*global)))?;
                if !decl.mutable {
                    return Err(self.err(ValidationErrorKind::ImmutableGlobalWrite(*global)));
                }
                Ok(())
            }
            super::borrow::BorrowNode::SpecGlobalRoot { .. } => Ok(()),
        }
    }

    fn check_bit_op(&self, op: &BitOp, scope: &mut BTreeSet<VarId>) -> Result<(), ValidationError> {
        match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => self.check_expr(operand, scope),
            BitOp::Concat { high, low } => {
                self.check_expr(high, scope)?;
                self.check_expr(low, scope)
            }
        }
    }

    fn check_path_step(
        &self,
        step: &PathStep,
        scope: &mut BTreeSet<VarId>,
    ) -> Result<(), ValidationError> {
        for expr in step.exprs() {
            self.check_expr(expr, scope)?;
        }
        if let PathStep::MapKey {
            df_value: Some(value),
            ..
        } = step
        {
            if !scope.contains(value) {
                return Err(self.err(ValidationErrorKind::UnboundVariable(value.clone())));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::builder::*;
    use super::super::expr::{BlockTail, Stmt};
    use super::super::function::{Function, FunctionKind, Param, Signature};
    use super::super::ops::BitOp;
    use super::super::program::{
        Field, FunctionGlobalBinding, Global, Module, Program, Struct, Variant,
    };
    use super::super::ty::Type;
    use super::*;

    fn empty_module() -> (Program, super::ModId) {
        let mut p = Program::default();
        let mid = 0;
        p.modules.insert(
            mid,
            Module {
                name: "m".to_string(),
                package_name: "test".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        (p, mid)
    }

    fn add_fn(p: &mut Program, mid: super::ModId, body: Block) -> super::FunId {
        let id = p.functions.len();
        p.functions.insert(
            id,
            Function {
                module: mid,
                name: format!("f{id}"),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: Type::Unit,
                },
                body,
                kind: FunctionKind::Source,
                effects: crate::ir::Effects::default(),
                explicit_pure: false,
            },
        );
        id
    }

    fn add_fn_with_param(
        p: &mut Program,
        mid: super::ModId,
        param: &str,
        body: Block,
    ) -> super::FunId {
        let id = p.functions.len();
        p.functions.insert(
            id,
            Function {
                module: mid,
                name: format!("f{id}"),
                signature: Signature {
                    type_params: Vec::new(),
                    params: vec![Param {
                        name: param.to_string(),
                        var: param.into(),
                        ty: Type::UInt(64),
                    }],
                    return_type: Type::Unit,
                },
                body,
                kind: FunctionKind::Source,
                effects: crate::ir::Effects::default(),
                explicit_pure: false,
            },
        );
        id
    }

    #[test]
    fn empty_program_validates() {
        let p = Program::default();
        assert!(validate_program(&p).is_ok());
    }

    #[test]
    fn function_with_unit_body_validates() {
        let (mut p, mid) = empty_module();
        add_fn(&mut p, mid, just(unit()));
        assert!(validate_program(&p).is_ok());
    }

    #[test]
    fn unbound_var_in_tail_rejects() {
        let (mut p, mid) = empty_module();
        add_fn(&mut p, mid, just(var("missing")));
        let err = validate_program(&p).unwrap_err();
        assert!(matches!(err.kind, ValidationErrorKind::UnboundVariable(_)));
    }

    #[test]
    fn deep_validation_has_a_bounded_stack_and_preserves_errors() {
        // Run from a deliberately small caller stack. The iterative depth
        // precheck must select the bounded auxiliary stack before either the
        // structural validator or typed WriteRef walk recurse through this
        // generated-style expression. Build and forget the programs inside
        // the thread so recursive Box destruction is not part of this test.
        let result = std::thread::Builder::new()
            .name("deep-ir-validator-test".to_string())
            .stack_size(128 * 1024)
            .spawn(|| {
                fn nested(mut leaf: Expr) -> Expr {
                    for _ in 0..1024 {
                        leaf = Expr::ToBool(Box::new(leaf));
                    }
                    leaf
                }

                let (mut valid, mid) = empty_module();
                add_fn(&mut valid, mid, just(nested(Expr::Unit)));
                let accepts_valid = validate_program(&valid).is_ok();
                std::mem::forget(valid);

                let (mut invalid, mid) = empty_module();
                add_fn(
                    &mut invalid,
                    mid,
                    just(nested(Expr::Var(VarId::from("missing")))),
                );
                let preserves_error = matches!(
                    validate_program(&invalid),
                    Err(ValidationError {
                        kind: ValidationErrorKind::UnboundVariable(ref var),
                        ..
                    }) if var.as_ref() == "missing"
                );
                std::mem::forget(invalid);

                (accepts_valid, preserves_error)
            })
            .expect("failed to spawn small-stack validator test")
            .join()
            .expect("small-stack validator test panicked");

        assert_eq!(result, (true, true));
    }

    #[test]
    fn validation_depth_precheck_has_an_exact_inline_boundary() {
        fn nested(mut expression: Expr, wrappers: usize) -> Expr {
            for _ in 0..wrappers {
                expression = Expr::ToBool(Box::new(expression));
            }
            expression
        }

        // Block depth 1 + tail-expression depth 1 + N wrappers.
        let at_boundary = just(nested(Expr::Unit, INLINE_VALIDATION_DEPTH - 2));
        let over_boundary = just(nested(Expr::Unit, INLINE_VALIDATION_DEPTH - 1));
        assert!(!block_exceeds_inline_validation_depth(&at_boundary));
        assert!(block_exceeds_inline_validation_depth(&over_boundary));
    }

    #[test]
    fn empty_or_all_wildcard_let_pattern_rejects() {
        let (mut p, mid) = empty_module();
        let mut b = just(unit());
        b.stmts.push(Stmt::Let {
            pattern: Vec::new(),
            value: lit_u64(0),
        });
        add_fn(&mut p, mid, b);
        let err = validate_program(&p).unwrap_err();
        assert_eq!(err.kind, ValidationErrorKind::AllWildcardLet);
    }

    #[test]
    fn let_with_param_in_scope_validates() {
        let (mut p, mid) = empty_module();
        let body = block(vec![let_stmt(&["y"], var("x"))], tail_value(var("y")));
        add_fn_with_param(&mut p, mid, "x", body);
        assert!(validate_program(&p).is_ok());
    }

    #[test]
    fn match_arm_binding_arity_uses_variant_tag() {
        let (mut p, mid) = empty_module();
        p.structs.insert(
            7,
            Struct {
                module_id: mid,
                name: "E".to_string(),
                qualified_name: "test::m::E".to_string(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: Some(vec![
                    Variant {
                        name: "Pair".to_string(),
                        tag: 1,
                        fields: vec![
                            Field {
                                name: "left".to_string(),
                                field_type: Type::UInt(64),
                            },
                            Field {
                                name: "right".to_string(),
                                field_type: Type::UInt(64),
                            },
                        ],
                    },
                    Variant {
                        name: "Empty".to_string(),
                        tag: 0,
                        fields: Vec::new(),
                    },
                ]),
                is_native: false,
            },
        );
        let fid = add_fn(
            &mut p,
            mid,
            just(match_expr(7, unit(), vec![match_arm(0, &[], just(unit()))])),
        );
        assert!(validate_program(&p).is_ok());

        p.functions.get_mut(&fid).unwrap().body = just(match_expr(
            7,
            unit(),
            vec![match_arm(1, &["only_one"], just(unit()))],
        ));
        let err = validate_program(&p).unwrap_err();
        assert_eq!(
            err.kind,
            ValidationErrorKind::MatchArmArityMismatch {
                variant: 1,
                bindings: 1,
                fields: 2,
            }
        );
    }

    #[test]
    fn pack_arity_uses_non_dense_variant_tag() {
        let (mut p, mid) = empty_module();
        p.structs.insert(
            7,
            Struct {
                module_id: mid,
                name: "E".to_string(),
                qualified_name: "test::m::E".to_string(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: Some(vec![Variant {
                    name: "Value".to_string(),
                    tag: 9,
                    fields: vec![Field {
                        name: "value".to_string(),
                        field_type: Type::UInt(64),
                    }],
                }]),
                is_native: false,
            },
        );
        add_fn(
            &mut p,
            mid,
            just(Expr::Pack {
                struct_id: 7,
                type_args: Vec::new(),
                variant: Some(9),
                fields: vec![lit_u64(1)],
            }),
        );

        assert!(validate_program(&p).is_ok());
    }

    #[test]
    fn unknown_variant_tag_rejects_even_when_arity_is_zero() {
        let (mut p, mid) = empty_module();
        p.structs.insert(
            7,
            Struct {
                module_id: mid,
                name: "E".to_string(),
                qualified_name: "test::m::E".to_string(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: Some(vec![Variant {
                    name: "Empty".to_string(),
                    tag: 1,
                    fields: Vec::new(),
                }]),
                is_native: false,
            },
        );
        add_fn(
            &mut p,
            mid,
            just(Expr::Pack {
                struct_id: 7,
                type_args: Vec::new(),
                variant: Some(9),
                fields: Vec::new(),
            }),
        );

        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::InvalidVariantTag {
                struct_id: 7,
                variant: Some(9),
            }
        );
    }

    #[test]
    fn match_rejects_unknown_variant_tag() {
        let (mut p, mid) = empty_module();
        p.structs.insert(
            7,
            Struct {
                module_id: mid,
                name: "E".to_string(),
                qualified_name: "test::m::E".to_string(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: Some(vec![Variant {
                    name: "Empty".to_string(),
                    tag: 1,
                    fields: Vec::new(),
                }]),
                is_native: false,
            },
        );
        add_fn(
            &mut p,
            mid,
            just(match_expr(7, unit(), vec![match_arm(9, &[], just(unit()))])),
        );

        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::InvalidVariantTag {
                struct_id: 7,
                variant: Some(9),
            }
        );
    }

    #[test]
    fn match_rejects_duplicate_payload_binding() {
        let (mut p, mid) = empty_module();
        p.structs.insert(
            7,
            Struct {
                module_id: mid,
                name: "E".to_string(),
                qualified_name: "test::m::E".to_string(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: Some(vec![Variant {
                    name: "Pair".to_string(),
                    tag: 1,
                    fields: vec![
                        Field {
                            name: "left".to_string(),
                            field_type: Type::UInt(64),
                        },
                        Field {
                            name: "right".to_string(),
                            field_type: Type::UInt(64),
                        },
                    ],
                }]),
                is_native: false,
            },
        );
        add_fn(
            &mut p,
            mid,
            just(match_expr(
                7,
                unit(),
                vec![match_arm(1, &["same", "same"], just(unit()))],
            )),
        );

        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::DuplicateMatchArmBinding {
                variant: 1,
                binding: "same".into(),
            }
        );
    }

    #[test]
    fn break_outside_while_rejects() {
        let (mut p, mid) = empty_module();
        let body = Block {
            stmts: Vec::new(),
            tail: BlockTail::Break {
                level: 0,
                value: Box::new(unit()),
            },
        };
        add_fn(&mut p, mid, body);
        let err = validate_program(&p).unwrap_err();
        assert!(matches!(
            err.kind,
            ValidationErrorKind::JumpLevelOutOfBounds { level: 0, depth: 0 }
        ));
    }

    #[test]
    fn unknown_function_id_in_call_rejects() {
        let (mut p, mid) = empty_module();
        add_fn(&mut p, mid, just(call(99, vec![])));
        let err = validate_program(&p).unwrap_err();
        assert!(matches!(
            err.kind,
            ValidationErrorKind::UnknownFunctionId(99)
        ));
    }

    #[test]
    fn unbound_vars_in_bitop_operands_reject() {
        let ops = vec![
            BitOp::Extract {
                high: 7,
                low: 0,
                operand: Box::new(var("missing")),
            },
            BitOp::Concat {
                high: Box::new(lit_u64(0)),
                low: Box::new(var("missing")),
            },
            BitOp::Concat {
                high: Box::new(var("missing")),
                low: Box::new(lit_u64(0)),
            },
            BitOp::ZeroExtend {
                bits: 8,
                operand: Box::new(var("missing")),
            },
            BitOp::SignExtend {
                bits: 8,
                operand: Box::new(var("missing")),
            },
        ];
        for op in ops {
            let (mut p, mid) = empty_module();
            add_fn(&mut p, mid, just(Expr::BitOp(op)));
            let err = validate_program(&p).unwrap_err();
            assert!(matches!(
                err.kind,
                ValidationErrorKind::UnboundVariable(ref var) if var == &VarId::from("missing")
            ));
        }
    }

    #[test]
    fn unbound_writeback_world_rejects() {
        let (mut p, mid) = empty_module();
        let body = block(
            vec![
                let_stmt(&["root"], lit_u64(0)),
                let_stmt(&["child"], lit_u64(0)),
            ],
            tail_value(write_back("root", "child", Some("missing_world"))),
        );
        add_fn(&mut p, mid, body);
        let err = validate_program(&p).unwrap_err();
        assert!(matches!(
            err.kind,
            ValidationErrorKind::UnboundVariable(ref var)
                if var == &VarId::from("missing_world")
        ));
    }

    #[test]
    fn unbound_map_key_df_value_rejects() {
        let (mut p, mid) = empty_module();
        let body = block(
            vec![let_stmt(&["base"], lit_bool(true))],
            tail_value(map_key_borrow_df(
                var("base"),
                lit_bool(true),
                "missing_df_value",
            )),
        );
        add_fn(&mut p, mid, body);
        let err = validate_program(&p).unwrap_err();
        assert!(matches!(
            err.kind,
            ValidationErrorKind::UnboundVariable(ref var)
                if var == &VarId::from("missing_df_value")
        ));
    }

    #[test]
    fn unbound_map_key_df_value_in_update_rejects() {
        let (mut p, mid) = empty_module();
        let update = Expr::Update {
            step: PathStep::MapKey {
                key: Box::new(lit_bool(true)),
                key_type: Type::Bool,
                value_type: Type::Bool,
                df_value: Some(VarId::from("missing_df_value")),
            },
            base: Box::new(var("base")),
            value: Box::new(lit_bool(false)),
        };
        let body = block(
            vec![let_stmt(&["base"], lit_bool(true))],
            tail_value(update),
        );
        add_fn(&mut p, mid, body);
        let err = validate_program(&p).unwrap_err();
        assert!(matches!(
            err.kind,
            ValidationErrorKind::UnboundVariable(ref var)
                if var == &VarId::from("missing_df_value")
        ));
    }

    #[test]
    fn return_from_block_outside_labeled_block_rejects() {
        let (mut p, mid) = empty_module();
        add_fn(
            &mut p,
            mid,
            Block {
                stmts: Vec::new(),
                tail: BlockTail::ReturnFromBlock {
                    level: 0,
                    value: Box::new(unit()),
                },
            },
        );
        let err = validate_program(&p).unwrap_err();
        assert_eq!(
            err.kind,
            ValidationErrorKind::LabeledReturnLevelOutOfBounds { level: 0, depth: 0 }
        );
    }

    #[test]
    fn return_from_innermost_labeled_block_validates() {
        let (mut p, mid) = empty_module();
        let labeled_body = Block {
            stmts: Vec::new(),
            tail: BlockTail::ReturnFromBlock {
                level: 0,
                value: Box::new(unit()),
            },
        };
        add_fn(&mut p, mid, just(labeled_block(labeled_body, Type::Unit)));
        assert!(validate_program(&p).is_ok());
    }

    #[test]
    fn nested_labeled_block_return_depth_is_checked() {
        let nested_program = |level| {
            let (mut p, mid) = empty_module();
            let inner = Block {
                stmts: Vec::new(),
                tail: BlockTail::ReturnFromBlock {
                    level,
                    value: Box::new(unit()),
                },
            };
            let outer = just(labeled_block(inner, Type::Unit));
            add_fn(&mut p, mid, just(labeled_block(outer, Type::Unit)));
            p
        };

        assert!(validate_program(&nested_program(1)).is_ok());
        let err = validate_program(&nested_program(2)).unwrap_err();
        assert_eq!(
            err.kind,
            ValidationErrorKind::LabeledReturnLevelOutOfBounds { level: 2, depth: 2 }
        );
    }

    // ---- Expr::While: header-tail invariant ---------------------------

    fn while_block(header: Block, cond: Expr, body: Block) -> Block {
        Block {
            stmts: vec![Stmt::Eval(while_expr(header, cond, body))],
            tail: BlockTail::Value(Expr::Unit),
        }
    }

    #[test]
    fn while_with_value_unit_header_tail_passes() {
        let (mut p, mid) = empty_module();
        let body = while_block(
            // header.tail = Value(Unit) -- correct
            block(vec![], tail_value(unit())),
            lit_bool(true),
            // body has a Continue {0} tail back to the loop
            block(vec![], tail_continue(0, unit())),
        );
        add_fn(&mut p, mid, body);
        assert!(validate_program(&p).is_ok());
    }

    #[test]
    fn while_with_non_unit_header_tail_rejects() {
        // header.tail = Value(<bool>) -- not Unit
        let (mut p, mid) = empty_module();
        let body = while_block(
            block(vec![], tail_value(lit_bool(true))),
            lit_bool(true),
            block(vec![], tail_continue(0, unit())),
        );
        add_fn(&mut p, mid, body);
        let err = validate_program(&p).unwrap_err();
        assert!(matches!(
            err.kind,
            ValidationErrorKind::WhileHeaderTailMustBeValueUnit
        ));
    }

    #[test]
    fn while_with_break_or_continue_header_tail_rejects() {
        // The header is not inside the loop's scope frame, but the
        // validator still rejects non-Value(Unit) tails on it. (A
        // Break tail in a header would also fail the loop-depth
        // check, so this test pins both layers.)
        let (mut p, mid) = empty_module();
        let body = while_block(
            block(vec![], tail_break(0, unit())),
            lit_bool(true),
            block(vec![], tail_continue(0, unit())),
        );
        add_fn(&mut p, mid, body);
        // The non-Unit tail check fires before the loop-depth check.
        let err = validate_program(&p).unwrap_err();
        assert!(matches!(
            err.kind,
            ValidationErrorKind::WhileHeaderTailMustBeValueUnit
        ));
    }

    #[test]
    fn while_header_can_introduce_bindings_visible_to_cond() {
        // `let x = true; while (x) { continue }` -- header binds x,
        // cond reads x, body is well-formed.
        let (mut p, mid) = empty_module();
        let header = block(vec![let_stmt(&["x"], lit_bool(true))], tail_value(unit()));
        let body = while_block(header, var("x"), block(vec![], tail_continue(0, unit())));
        add_fn(&mut p, mid, body);
        assert!(validate_program(&p).is_ok());
    }

    /// One loop-carried slot, `header_exit_locals` of the given length.
    /// `header_exit_locals` is positionally parallel to `iter_locals`, so
    /// any length but 1 is the stale-producer shape stage 7 cannot lower.
    fn while_with_header_exit_arity(exits: Vec<VarId>) -> Block {
        Block {
            stmts: vec![Stmt::Eval(Expr::While {
                header: Box::new(block(vec![], tail_value(unit()))),
                cond: Box::new(lit_bool(true)),
                body: Box::new(block(vec![], tail_continue(0, var("i")))),
                iter_locals: vec![("i".into(), lit_u64(0))],
                header_exit_locals: exits,
                live_out: Vec::new(),
            })],
            tail: BlockTail::Value(Expr::Unit),
        }
    }

    #[test]
    fn while_header_exit_locals_shorter_than_iter_locals_rejects() {
        // The stage-5 output shape with a stale (stages-1-4) empty
        // `header_exit_locals`. Stage 7's cond-false edge builds the
        // `LoopAfter` call from `header_exit_locals`, so this would emit a
        // zero-arg call to a one-param helper -- Lean rejects the render.
        // The validator names the offending function so a 4000-function
        // package does not need a bisect to find it.
        let (mut p, mid) = empty_module();
        let fid = add_fn(&mut p, mid, while_with_header_exit_arity(Vec::new()));
        let err = validate_program(&p).unwrap_err();
        assert_eq!(err.function, Some(fid));
        assert_eq!(
            err.kind,
            ValidationErrorKind::HeaderExitArityMismatch {
                iter_locals: 1,
                header_exit_locals: 0,
            }
        );
    }

    #[test]
    fn while_header_exit_locals_longer_than_iter_locals_rejects() {
        // The other direction: a surplus entry would misalign every
        // carried slot at the exit edge rather than drop the last one.
        let (mut p, mid) = empty_module();
        let fid = add_fn(
            &mut p,
            mid,
            while_with_header_exit_arity(vec!["i".into(), "j".into()]),
        );
        let err = validate_program(&p).unwrap_err();
        assert_eq!(err.function, Some(fid));
        assert_eq!(
            err.kind,
            ValidationErrorKind::HeaderExitArityMismatch {
                iter_locals: 1,
                header_exit_locals: 2,
            }
        );
    }

    #[test]
    fn while_header_exit_locals_matching_iter_locals_is_accepted() {
        // The conforming stage-5 shape: one post-header name per carried
        // slot. Pins that the check is an arity check and nothing more --
        // it must not reject the shape stage 5 actually emits.
        let (mut p, mid) = empty_module();
        add_fn(&mut p, mid, while_with_header_exit_arity(vec!["i".into()]));
        assert!(validate_program(&p).is_ok());
    }

    #[test]
    fn while_builder_emits_a_conforming_header_exit_arity() {
        // `while_with_locals` documents itself as building "the stage-5+
        // shape", so its default must satisfy the stage-5 postcondition.
        // It used to hardcode an empty `header_exit_locals`, which no
        // amount of correct calling could fix.
        let (mut p, mid) = empty_module();
        let while_e = while_with_locals(
            vec![("i", lit_u64(0))],
            block(vec![], tail_value(unit())),
            lit_bool(true),
            block(vec![], tail_continue(0, var("i"))),
        );
        let Expr::While {
            iter_locals,
            header_exit_locals,
            ..
        } = &while_e
        else {
            panic!("expected While");
        };
        assert_eq!(header_exit_locals.len(), iter_locals.len());
        add_fn(
            &mut p,
            mid,
            Block {
                stmts: vec![Stmt::Eval(while_e)],
                tail: BlockTail::Value(Expr::Unit),
            },
        );
        assert!(validate_program(&p).is_ok());
    }

    fn add_test_global(p: &mut Program, id: GlobalId, mutable: bool) {
        p.globals.insert(
            id,
            Global {
                module_id: 0,
                name: format!("g{id}"),
                ty: Type::UInt(32),
                mutable,
                definition: crate::ir::GlobalDefinition::BoundarySupplied,
            },
        );
    }

    #[test]
    fn function_globals_validate_order_and_stable_parameter_identity() {
        let (mut p, mid) = empty_module();
        add_test_global(&mut p, 0, true);
        add_test_global(&mut p, 1, false);
        let fid = add_fn(&mut p, mid, just(unit()));
        p.functions.get_mut(&fid).unwrap().signature.params.extend([
            Param {
                name: "g0".into(),
                var: "g0".into(),
                ty: p.globals[&0].threaded_param_type(),
            },
            Param {
                name: "g1".into(),
                var: "g1".into(),
                ty: p.globals[&1].threaded_param_type(),
            },
        ]);
        let bindings = vec![
            FunctionGlobalBinding {
                global: 0,
                parameter_index: 0,
            },
            FunctionGlobalBinding {
                global: 1,
                parameter_index: 1,
            },
        ];
        p.function_globals.insert(fid, bindings.clone());
        assert!(validate_program(&p).is_ok());

        // World/ghost and helper parameters may be appended after the global
        // parameters. Binding identity, not suffix position, is authoritative.
        p.functions
            .get_mut(&fid)
            .unwrap()
            .signature
            .params
            .push(Param {
                name: "later_suffix".into(),
                var: "later_suffix".into(),
                ty: Type::Unit,
            });
        assert!(validate_program(&p).is_ok());

        p.function_globals
            .insert(fid, vec![bindings[1].clone(), bindings[0].clone()]);
        assert!(matches!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::FunctionGlobalsOutOfOrder {
                previous: 1,
                next: 0
            }
        ));

        p.function_globals
            .insert(fid, vec![bindings[0].clone(), bindings[0].clone()]);
        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::DuplicateFunctionGlobal(0)
        );

        p.function_globals.insert(fid, bindings);
        p.functions
            .get_mut(&fid)
            .unwrap()
            .signature
            .params
            .iter_mut()
            .find(|param| param.var.as_ref() == "g1")
            .unwrap()
            .ty = Type::Unit;
        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::FunctionGlobalParamTypeMismatch {
                global: 1,
                expected: Type::Reference(Box::new(Type::UInt(32))),
                actual: Type::Unit,
            }
        );
    }

    #[test]
    fn global_types_are_closed_and_recursively_resolved() {
        let (mut p, _) = empty_module();
        p.globals.insert(
            7,
            Global {
                module_id: 0,
                name: "dangling".into(),
                ty: Type::Vector(Box::new(Type::Tuple(vec![Type::Struct {
                    struct_id: 999,
                    type_args: vec![],
                }]))),
                mutable: false,
                definition: crate::ir::GlobalDefinition::BoundarySupplied,
            },
        );
        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::UnknownStructId(999)
        );

        p.structs.insert(
            999,
            Struct {
                module_id: 0,
                name: "Box".into(),
                qualified_name: "m::Box".into(),
                type_params: vec!["T".into()],
                fields: vec![],
                variants: None,
                is_native: false,
            },
        );
        p.structs.get_mut(&999).unwrap().module_id = 77;
        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::UnknownModuleId(77)
        );
        p.structs.get_mut(&999).unwrap().module_id = 0;
        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::GlobalStructTypeArgumentArityMismatch {
                global: 7,
                struct_id: 999,
                expected: 1,
                actual: 0,
            }
        );

        p.globals.get_mut(&7).unwrap().ty = Type::Struct {
            struct_id: 999,
            type_args: vec![Type::TypeParam(3)],
        };
        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::GlobalTypeParameter {
                global: 7,
                index: 3,
            }
        );

        p.globals.get_mut(&7).unwrap().ty =
            Type::Vector(Box::new(Type::Reference(Box::new(Type::UInt(8)))));
        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::InvalidGlobalStorageType {
                global: 7,
                kind: "Reference",
            }
        );

        p.globals.get_mut(&7).unwrap().ty = Type::Struct {
            struct_id: 999,
            type_args: vec![Type::UInt(8)],
        };
        p.structs.get_mut(&999).unwrap().fields.push(Field {
            name: "foreign_pointer".into(),
            field_type: Type::Reference(Box::new(Type::TypeParam(0))),
        });
        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::InvalidGlobalStorageType {
                global: 7,
                kind: "Reference",
            },
            "generic struct fields must be instantiated and checked recursively"
        );
    }

    #[test]
    fn immutable_global_root_is_rejected() {
        let (mut p, mid) = empty_module();
        add_test_global(&mut p, 1, false);
        let fid = add_fn(
            &mut p,
            mid,
            just(Expr::WriteBack {
                node: super::super::BorrowNode::GlobalRoot(1),
                edge: super::super::BorrowEdge::Direct,
                child: "child".into(),
                world: None,
            }),
        );
        p.functions
            .get_mut(&fid)
            .unwrap()
            .signature
            .params
            .push(Param {
                name: "child".into(),
                var: "child".into(),
                ty: Type::UInt(32),
            });
        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::ImmutableGlobalWrite(1)
        );
    }

    #[test]
    fn write_ref_of_readonly_global_is_rejected() {
        let (mut p, mid) = empty_module();
        add_test_global(&mut p, 1, false);
        let body = Block {
            stmts: vec![Stmt::Eval(Expr::WriteRef {
                reference: Box::new(Expr::BorrowGlobal(1)),
                value: Box::new(lit_uint(32, 7u8.into())),
            })],
            tail: BlockTail::Value(unit()),
        };
        add_fn(&mut p, mid, body);

        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::WriteRefThroughImmutableReference {
                actual: Type::Reference(Box::new(Type::UInt(32))),
            }
        );
    }

    #[test]
    fn write_ref_through_readonly_global_alias_is_rejected() {
        let (mut p, mid) = empty_module();
        add_test_global(&mut p, 1, false);
        let body = Block {
            stmts: vec![
                Stmt::Let {
                    pattern: vec![Some("global_ref".into())],
                    value: Expr::BorrowGlobal(1),
                },
                Stmt::Eval(Expr::WriteRef {
                    reference: Box::new(var("global_ref")),
                    value: Box::new(lit_uint(32, 7u8.into())),
                }),
            ],
            tail: BlockTail::Value(unit()),
        };
        add_fn(&mut p, mid, body);

        assert_eq!(
            validate_program(&p).unwrap_err().kind,
            ValidationErrorKind::WriteRefThroughImmutableReference {
                actual: Type::Reference(Box::new(Type::UInt(32))),
            }
        );
    }

    /// The shape `stage_04_ghost` leaves behind for
    /// `*ghost::borrow_mut<K, V>() = e`: the borrow is rewritten to the
    /// threaded ghost var (typed `V`) and the `*r := e` is deliberately
    /// left in place. A rule demanding a `MutableRef` operand rejects it.
    #[test]
    fn write_ref_through_a_value_typed_operand_validates() {
        let (mut p, mid) = empty_module();
        let body = Block {
            stmts: vec![
                Stmt::Let {
                    pattern: vec![Some("ghost_alias".into())],
                    value: var("__ghost_m__Marker"),
                },
                Stmt::Eval(Expr::WriteRef {
                    reference: Box::new(var("ghost_alias")),
                    value: Box::new(lit_bool(false)),
                }),
            ],
            tail: BlockTail::Value(unit()),
        };
        let fid = add_fn(&mut p, mid, body);
        p.functions
            .get_mut(&fid)
            .unwrap()
            .signature
            .params
            .push(Param {
                name: "__ghost_m__Marker".into(),
                var: "__ghost_m__Marker".into(),
                ty: Type::Bool,
            });

        assert!(validate_program(&p).is_ok());
    }

    #[test]
    fn write_ref_through_mutable_global_alias_validates() {
        let (mut p, mid) = empty_module();
        add_test_global(&mut p, 1, true);
        let body = Block {
            stmts: vec![
                Stmt::Let {
                    pattern: vec![Some("global_ref".into())],
                    value: Expr::BorrowGlobal(1),
                },
                Stmt::Eval(Expr::WriteRef {
                    reference: Box::new(var("global_ref")),
                    value: Box::new(lit_uint(32, 7u8.into())),
                }),
            ],
            tail: BlockTail::Value(unit()),
        };
        add_fn(&mut p, mid, body);

        assert!(validate_program(&p).is_ok());
    }
}
