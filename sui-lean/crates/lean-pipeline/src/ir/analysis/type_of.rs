//! Partial type inference on `Expr`.
//!
//! Given a per-function scope (`BTreeMap<VarId, Type>`) plus the
//! enclosing `Program` (for function return types and struct field
//! types), recover the type of an arbitrary `Expr`.
//!
//! Used by stage 7 (loop extraction) to size `LoopBody` /
//! `LoopAfter` helper signatures from `iter_locals`' init
//! expressions, since the IR doesn't carry types on
//! `Stmt::Let` patterns or `Expr::While::iter_locals` binders.
//!
//! ## Coverage
//!
//! Common cases handled:
//!
//! - Atoms: `Var`, `Const`, `Unit`.
//! - Compound: `BinOp` (arithmetic / bitwise / shift preserve
//!   operand type; comparison + logical return `Bool`),
//!   `UnOp::Cast(N)` -> `UInt(N)`, `UnOp::Not` -> `Bool`,
//!   `UnOp::BitNot` -> operand type, `BitOp` (extract / extend
//!   widths), `Tuple` -> tuple of element types, `Call` with
//!   type-arg substitution into the callee's return type.
//! - Struct / enum: `Pack` -> `Struct { struct_id, type_args }`,
//!   `Field` / `UpdateField` -> field type substituted.
//! - Branching: `If` / `Match` use a Value-tail arm's type.
//! - `Quantifier`: `Forall` / `Exists` / `Any` / `All` -> `Bool`;
//!   `Count` -> `UInt(64)`. The remaining kinds match the
//!   source-level macro return types in `prover::vector_iter`
//!   (see `packages/prover/sources/vector.move`), NOT the lambda
//!   body's value type:
//!     - `SumMap` -> `Integer` (`std::integer::Integer`). Matches
//!       `end_sum_map_lambda<T>(): Integer` -- the lambda's `$U`
//!       return is discarded by `let _ = $f(x);` in the macro.
//!     - `FindIndex` -> `Option<u64>` (matches
//!       `end_find_index_lambda(): Option<u64>`).
//!     - `Map` -> `vector<body_ty>` (the lambda return type IS the
//!       element type, matches `end_map_lambda<T>(): &vector<T>`).
//!     - `Filter` -> `vector<element_ty>` where `element_ty` is
//!       `binder_type` with any outer `&`/`&mut` stripped (matches
//!       `end_filter_lambda<T>(): &vector<T>` -- vector is over
//!       the INPUT element type, not the lambda's `bool` body).
//!     - `Find` -> `Option<element_ty>` (matches
//!       `end_find_lambda<T>(): &Option<T>`).
//!     - `FindIndices` -> `vector<u64>` (matches
//!       `end_find_indices_lambda(): &vector<u64>`).
//!
//!   `SumMap`/`FindIndex`/`Find` require resolving
//!   `MoveStdlib::integer::Integer` and `MoveStdlib::option::Option`
//!   from `program.structs`. If such a quantifier exists the macro
//!   must have been translated, which means the framework struct is
//!   registered -- so the lookup should always succeed in practice.
//!   The fallback (body type / `Vector(body_ty)`) is retained for
//!   synthetic test fixtures that construct `Quantifier` exprs
//!   without populating the framework structs.
//! - Global references: `BorrowGlobal(g)` -> the declaration's threaded
//!   parameter type (`MutableRef` for writable globals, `Reference` for
//!   readonly globals).
//! - Mutable references: `BorrowLoc(v)` -> `MutableRef { inner:
//!   type-of-v, root: type-of-v }`, peeling a leading immutable
//!   `Reference` off `type-of-v` first (an erased `&T` value is
//!   borrowed as `&mut T`, not `&mut &T`); `BorrowField` -> `MutableRef`
//!   with field type as inner; `ReadRef` -> dereference;
//!   `WriteRef` (value position) rejects an immutable `Reference` and
//!   otherwise returns its operand's type (the in-place rebind);
//!   `WriteBack` (value position) -> type of the rebound node var.
//! - Coercions: `ToProp` -> `Prop`, `ToBool` -> `Bool`.
//! - `While` -> `Tuple([iter_locals binder types])`. Recursive on
//!   the init expressions.
//!
//! ## Errors
//!
//! - `UnboundVar(v)` -- `v` not in scope.
//! - `UnknownFunction(fid)` -- `Call::fun` doesn't resolve.
//! - `UnknownGlobal(gid)` -- `BorrowGlobal` / `GlobalRoot` doesn't resolve.
//! - `UnknownStruct(sid)` -- `Pack` / `Field` / etc.' struct id
//!   doesn't resolve.
//! - `FieldOutOfRange { sid, idx }` -- field index past struct's
//!   field count.
//! - `MalformedAccess { reason }` -- e.g. `ReadRef` of a
//!   non-reference type, `Field` of a non-struct.
//! - `Unsupported { what }` -- rare cases listed above.
//!
//! Errors are descriptive, not actionable -- callers typically
//! propagate them up as a stage-level error.

use std::collections::BTreeMap;

use crate::ir::borrow::BorrowNode;
use crate::ir::expr::{Block, BlockTail, Expr, MatchArm, Stmt};
use crate::ir::ops::{BinOp, BitOp, UnOp};
use crate::ir::quant::QuantifierKind;
use crate::ir::ty::{Const, Type};
use crate::ir::{FunId, GlobalId, Program, StructId, VarId};

/// Errors produced by [`type_of`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeOfError {
    UnboundVar(VarId),
    UnknownFunction(FunId),
    UnknownGlobal(GlobalId),
    ImmutableGlobalWrite(GlobalId),
    UnknownStruct(StructId),
    FieldOutOfRange {
        struct_id: StructId,
        field_index: usize,
    },
    UnknownVariantTag {
        struct_id: StructId,
        variant: usize,
    },
    MalformedAccess {
        reason: String,
    },
    Unsupported {
        what: String,
    },
}

/// Infer the type of `e` in `scope` against `program`.
pub fn type_of(
    e: &Expr,
    scope: &BTreeMap<VarId, Type>,
    program: &Program,
) -> Result<Type, TypeOfError> {
    match e {
        // ---- Atoms ----
        Expr::Var(v) => scope
            .get(v)
            .cloned()
            .ok_or_else(|| TypeOfError::UnboundVar(v.clone())),
        Expr::Const(c) => Ok(type_of_const(c)),
        Expr::Unit => Ok(Type::Unit),

        // ---- Compound ----
        Expr::BinOp { op, lhs, rhs } => {
            let lt = type_of(lhs, scope, program)?;
            let _rt = type_of(rhs, scope, program)?;
            Ok(type_of_binop(*op, lt))
        }
        Expr::UnOp { op, operand } => match op {
            UnOp::Cast(n) => Ok(Type::UInt(*n)),
            UnOp::Not => Ok(Type::Bool),
            UnOp::BitNot => type_of(operand, scope, program),
        },
        Expr::BitOp(op) => type_of_bitop(op, scope, program),

        Expr::Call { fun, type_args, .. } => {
            let return_type = program
                .lookup_callee(*fun)
                .ok_or(TypeOfError::UnknownFunction(*fun))?
                .signature()
                .return_type
                .clone();
            Ok(substitute_type_params(&return_type, type_args))
        }

        Expr::Tuple(elems) => {
            let mut types = Vec::with_capacity(elems.len());
            for e in elems {
                types.push(type_of(e, scope, program)?);
            }
            Ok(Type::Tuple(types))
        }

        // ---- Struct / enum ----
        Expr::Pack {
            struct_id,
            type_args,
            ..
        } => Ok(Type::Struct {
            struct_id: *struct_id,
            type_args: type_args.clone(),
        }),
        Expr::Unpack {
            struct_id,
            variant,
            value,
        } => {
            // Unpack returns a Tuple of the struct's field types
            // (substituted with the `value`'s type-args). For enum
            // variants we'd substitute against the variant's fields,
            // but we need the type-args from the value's Struct type
            // (variant ignored at the type level since enum tag-erasure
            // is render-time concern).
            let v_ty = type_of(value, scope, program)?;
            let type_args = match &v_ty {
                Type::Struct { type_args, .. } => type_args.clone(),
                Type::Reference(inner) | Type::MutableRef { inner, .. } => match inner.as_ref() {
                    Type::Struct { type_args, .. } => type_args.clone(),
                    _ => {
                        return Err(TypeOfError::MalformedAccess {
                            reason: format!("Unpack of non-struct type {v_ty:?}"),
                        });
                    }
                },
                _ => {
                    return Err(TypeOfError::MalformedAccess {
                        reason: format!("Unpack of non-struct type {v_ty:?}"),
                    });
                }
            };
            let s = program
                .structs
                .get(struct_id)
                .ok_or(TypeOfError::UnknownStruct(*struct_id))?;
            // Plain struct: tuple of field types. Enum: leave to
            // caller to specialise per variant -- here we just take
            // the variant's fields if `variant` is set, else the
            // struct's.
            let fields = if let Some(variants) = &s.variants {
                if variants.is_empty() {
                    return Err(TypeOfError::MalformedAccess {
                        reason: format!("Unpack of empty-variant enum {struct_id}"),
                    });
                }
                // Use the MATCHED variant's fields. An enum `Unpack`
                // carries the variant tag the enclosing `Match`
                // selected; using variant 0 unconditionally mistypes
                // every non-first variant's payload -- e.g. cetus-dlmm
                // `BlockEntity::POSITION(ID)` (v1) was typed as the v0
                // `USER(address)` payload, so the extracted continuation
                // applied `id_to_address` to an `Address`.
                let tag = variant.ok_or_else(|| TypeOfError::MalformedAccess {
                    reason: format!("Unpack of enum {struct_id} is missing a variant tag"),
                })?;
                match s.variant_by_tag(tag) {
                    Some(v) => &v.fields,
                    None => {
                        return Err(TypeOfError::MalformedAccess {
                            reason: format!(
                                "Unpack variant tag {tag} does not resolve for enum {struct_id}"
                            ),
                        });
                    }
                }
            } else {
                &s.fields
            };
            let types: Vec<Type> = fields
                .iter()
                .map(|f| substitute_type_params(&f.field_type, &type_args))
                .collect();
            if types.len() == 1 {
                Ok(types.into_iter().next().unwrap())
            } else {
                Ok(Type::Tuple(types))
            }
        }
        Expr::Field {
            struct_id,
            field_index,
            base,
        } => {
            let base_ty = type_of(base, scope, program)?;
            let type_args = base_struct_type_args(&base_ty, *struct_id)?;
            field_type(program, *struct_id, *field_index, &type_args)
        }

        // ---- Branching ----
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            // Pick whichever arm has a Value tail. If neither does
            // (both terminate), we can't infer a value type;
            // conservatively return Unit (caller would have already
            // detected unreachability).
            block_value_type(then_branch, scope, program)
                .or_else(|_| block_value_type(else_branch, scope, program))
                .or(Ok(Type::Unit))
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            let selector_type = type_of(selector, scope, program)?;
            let type_args = base_struct_type_args(&selector_type, *struct_id)?;
            let structure = program
                .structs
                .get(struct_id)
                .ok_or(TypeOfError::UnknownStruct(*struct_id))?;
            if structure.variants.is_none() {
                return Err(TypeOfError::MalformedAccess {
                    reason: format!("Match on non-enum Struct(id={struct_id})"),
                });
            }
            // Pick the first Value-tailed arm; same convention as If.
            for arm in cases {
                let variant = structure.variant_by_tag(arm.variant).ok_or(
                    TypeOfError::UnknownVariantTag {
                        struct_id: *struct_id,
                        variant: arm.variant,
                    },
                )?;
                if let Ok(t) =
                    match_arm_value_type(arm, &variant.fields, &type_args, scope, program)
                {
                    return Ok(t);
                }
            }
            Ok(Type::Unit)
        }

        // ---- Labeled scope ----
        Expr::LabeledBlock { result_ty, .. } => Ok(result_ty.clone()),

        // ---- Loops -- the value of an Expr::While is the loop_state
        // tuple, which we recover from iter_locals' init types.
        Expr::While {
            iter_locals,
            header,
            live_out,
            ..
        } => {
            let mut elems = Vec::with_capacity(iter_locals.len() + live_out.len());
            let mut iter_local_types = BTreeMap::new();
            for (binder, init) in iter_locals {
                let ty = type_of(init, scope, program)?;
                elems.push(ty.clone());
                iter_local_types.insert(binder.clone(), ty);
            }
            // Live-out vars are bound inside the loop header and
            // escape the loop as extra trailing tuple elements (see
            // stage 5's `live_out`). Recover their types by folding
            // the header's `let`s in a scope seeded with the
            // iter-local binders (which the header references), then
            // looking up each in-loop name. Empty `live_out`
            // (ordinary loops) skips this and preserves prior
            // behavior exactly.
            if !live_out.is_empty() {
                let mut hdr_scope: BTreeMap<VarId, Type> = scope.clone();
                for (binder, init) in iter_locals {
                    let ty = type_of(init, scope, program)?;
                    hdr_scope.insert(binder.clone(), ty);
                }
                for s in &header.stmts {
                    if let Stmt::Let { pattern, value } = s {
                        let val_ty = type_of(value, &hdr_scope, program)?;
                        bind_pattern(pattern, &val_ty, &mut hdr_scope)?;
                    }
                }
                for (in_loop_name, destination) in live_out {
                    let ty = hdr_scope.get(in_loop_name).cloned().ok_or_else(|| {
                        TypeOfError::MalformedAccess {
                            reason: format!(
                                "live-out var {in_loop_name:?} not bound in While header"
                            ),
                        }
                    })?;
                    if let Some(slot_ty) = iter_local_types.get(destination) {
                        if &ty != slot_ty {
                            return Err(TypeOfError::MalformedAccess {
                                reason: format!(
                                    "loop exit override {in_loop_name:?} has type {ty:?}, expected carried slot {destination:?} type {slot_ty:?}"
                                ),
                            });
                        }
                    } else {
                        elems.push(ty);
                    }
                }
            }
            Ok(if elems.is_empty() {
                Type::Unit
            } else if elems.len() == 1 {
                elems.into_iter().next().unwrap()
            } else {
                Type::Tuple(elems)
            })
        }

        // ---- Mutable references ----
        Expr::BorrowGlobal(global) => {
            let global = program
                .globals
                .get(global)
                .ok_or(TypeOfError::UnknownGlobal(*global))?;
            Ok(global.threaded_param_type())
        }
        Expr::BorrowLoc(v) => {
            let slot = scope
                .get(v)
                .cloned()
                .ok_or_else(|| TypeOfError::UnboundVar(v.clone()))?;
            // An immutable `&T` is erased to a plain value of type `T`
            // in this value-style IR (`render/ty.rs` renders
            // `Reference(t)` as `t`). Upstream's EliminateImmRefs stores
            // an immutable-ref-returning call's result straight into a
            // value local with no `ReadRef`
            // (`$t2 := network_pubkey_bytes(..)`), so a `BorrowLoc` of
            // that slot mutably borrows the underlying VALUE -- `&mut T`,
            // never a `&mut &T`. Peel a leading immutable `Reference` so
            // the result is `MutableRef { inner: T }` (which the VecIndex
            // / field arms accept), not the un-representable
            // `MutableRef { inner: Reference(T) }` that would trip
            // downstream projections (sui-system
            // `metadata_invalid_equal_both_pubkey_next_epoch`:
            // `*(*validator.network_pubkey_bytes()).borrow_mut(0)`).
            let inner = match slot {
                Type::Reference(pointee) => *pointee,
                other => other,
            };
            Ok(Type::MutableRef {
                inner: Box::new(inner.clone()),
                root: Box::new(inner),
            })
        }
        Expr::ReadRef(inner) => {
            let t = type_of(inner, scope, program)?;
            // Honor the IR's always-Tuple invariant: a Call to a
            // mut-augmented function whose original return was `()`
            // produces a 1-tuple `Tuple([MutableRef])`. Callers
            // consuming the result with a single binder or directly
            // through `ReadRef(Call(...))` treat the 1-tuple as
            // implicitly unwrapped. Mirror that here.
            let t = match t {
                Type::Tuple(items) if items.len() == 1 => items.into_iter().next().unwrap(),
                other => other,
            };
            match t {
                Type::Reference(inner) => Ok(*inner),
                Type::MutableRef { inner, .. } => Ok(*inner),
                other => Err(TypeOfError::MalformedAccess {
                    reason: format!("ReadRef of non-reference type {other:?}"),
                }),
            }
        }
        Expr::WriteRef { reference, .. } => {
            // Value-position WriteRef returns the (Mutation-typed)
            // updated reference -- same type as the reference being
            // updated. The operand is NOT required to be a `MutableRef`:
            // a value-typed operand is a legitimate, load-bearing shape.
            // `stage_04_ghost` lowers `*ghost::borrow_mut<K, V>() = e`
            // by rewriting the borrow to the threaded ghost var and
            // deliberately leaving the `*r := e` in place, so `r` is
            // typed `V`; the renderer wraps any non-`MutableRef` operand
            // in `Mutation.ofLocal` (see `render::expr`'s WriteRef arm).
            // What is rejected is an IMMUTABLE reference: accepting one
            // turns a readonly C global into a local Mutation at render
            // time and silently drops the writeback.
            let reference_ty = type_of(reference, scope, program)?;
            if let Type::Reference(_) = &reference_ty {
                return Err(TypeOfError::MalformedAccess {
                    reason: format!(
                        "WriteRef through an immutable reference, got {reference_ty:?}"
                    ),
                });
            }
            Ok(reference_ty)
        }
        Expr::WriteBack { node, world, .. } => {
            let node_ty = match node {
                BorrowNode::LocalRoot(v) | BorrowNode::Reference(v) => scope
                    .get(v)
                    .cloned()
                    .ok_or_else(|| TypeOfError::UnboundVar(v.clone()))?,
                BorrowNode::GlobalRoot(global) => {
                    let decl = program
                        .globals
                        .get(global)
                        .ok_or(TypeOfError::UnknownGlobal(*global))?;
                    if !decl.mutable {
                        return Err(TypeOfError::ImmutableGlobalWrite(*global));
                    }
                    decl.ty.clone()
                }
                BorrowNode::SpecGlobalRoot { type_args } => {
                    // The ghost variable's value type is the SECOND type
                    // arg to `prover::ghost::borrow_mut<T, U>()` (`U`).
                    type_args
                        .get(1)
                        .cloned()
                        .ok_or_else(|| TypeOfError::MalformedAccess {
                            reason: "ghost borrow_mut is missing its U (value) type-arg".into(),
                        })?
                }
            };
            // World-threaded df writeback: produces `(node_value, World)`,
            // exactly like a world-returning call. The trailing slot's
            // type is the threaded `world` var's type.
            match world {
                Some(wv) => {
                    let world_ty = scope
                        .get(wv)
                        .cloned()
                        .ok_or_else(|| TypeOfError::UnboundVar(wv.clone()))?;
                    Ok(Type::Tuple(vec![node_ty, world_ty]))
                }
                None => Ok(node_ty),
            }
        }
        Expr::IsParent { .. } => Ok(Type::Bool),
        // Unified PathStep forms (step 4). Borrow mirrors the matching
        // legacy borrow arm exactly; Update mirrors UpdateField /
        // UpdateVec (the updated container's own type).
        Expr::Borrow { step, base } => {
            use crate::ir::path::PathStep;
            let base_ty = type_of(base, scope, program)?;
            let inner = match step {
                PathStep::Field {
                    struct_id,
                    field_index,
                } => {
                    let (inner, root) =
                        borrow_field_type(&base_ty, *struct_id, *field_index, program)?;
                    return Ok(Type::MutableRef {
                        inner: Box::new(inner),
                        root: Box::new(root),
                    });
                }
                PathStep::VariantField {
                    struct_id,
                    variant,
                    field_index,
                } => {
                    let (inner, root) = borrow_variant_field_type(
                        &base_ty,
                        *struct_id,
                        *variant,
                        *field_index,
                        program,
                    )?;
                    return Ok(Type::MutableRef {
                        inner: Box::new(inner),
                        root: Box::new(root),
                    });
                }
                PathStep::VecIndex(_) => match &base_ty {
                    Type::Vector(t) => (**t).clone(),
                    Type::MutableRef { inner, .. } => match inner.as_ref() {
                        Type::Vector(t) => (**t).clone(),
                        other => {
                            return Err(TypeOfError::MalformedAccess {
                                reason: format!("Borrow VecIndex of non-vector type {other:?}"),
                            });
                        }
                    },
                    other => {
                        return Err(TypeOfError::MalformedAccess {
                            reason: format!("Borrow VecIndex of non-vector type {other:?}"),
                        });
                    }
                },
                PathStep::MapKey { value_type, .. } => value_type.clone(),
            };
            let root_ty = match base_ty {
                Type::MutableRef { root, .. } => *root,
                other => other,
            };
            Ok(Type::MutableRef {
                inner: Box::new(inner),
                root: Box::new(root_ty),
            })
        }
        Expr::Update { step, base, .. } => {
            // Honor the IR's always-Tuple invariant for FIELD updates:
            // a singleton tuple `Tuple([inner])` is a transparent
            // wrapper, produced when an augmented return is rendered
            // uniformly even for single-value returns. Unwrap so the
            // result type matches what downstream consumers expect.
            // Vec-index updates keep the base type verbatim (legacy
            // `UpdateVec` parity).
            let t = type_of(base, scope, program)?;
            Ok(match (step, t) {
                (
                    crate::ir::path::PathStep::Field { .. }
                    | crate::ir::path::PathStep::VariantField { .. },
                    Type::Tuple(items),
                ) if items.len() == 1 => items.into_iter().next().unwrap(),
                (_, other) => other,
            })
        }

        // ---- Coercions ----
        Expr::ToProp(_) => Ok(Type::Prop),
        Expr::ToBool(_) => Ok(Type::Bool),

        // ---- Quantifiers ----
        //
        // Predicate kinds return `Bool` regardless of body / domain.
        // Indexing / aggregation kinds depend on the body's value type
        // (the "callback" return type), so we evaluate the body's
        // tail in a scope augmented with the binder. Mirrors the
        // legacy IR's `get_type` in `intermediate-theorem-format`.
        Expr::Quantifier {
            kind,
            binder,
            binder_type,
            body,
            ..
        } => match kind {
            QuantifierKind::Forall
            | QuantifierKind::Exists
            | QuantifierKind::Any
            | QuantifierKind::All => Ok(Type::Bool),
            QuantifierKind::Count => Ok(Type::UInt(64)),
            // `sum_map!<T, U>(...): Integer`. The lambda `$f` returns
            // `$U` but the macro discards it (`let _ = $f(x);`) and
            // emits `end_sum_map_lambda<$U>(): Integer`. Result type
            // is `Integer`, never the body's type.
            QuantifierKind::SumMap => {
                if let Some(sid) = framework_integer_struct(program) {
                    Ok(Type::Struct {
                        struct_id: sid,
                        type_args: Vec::new(),
                    })
                } else {
                    // Fallback for synthetic test fixtures: preserve
                    // the legacy "body's value type" answer rather
                    // than fail. Real translations always register
                    // Integer (via the lambda's return type).
                    let mut inner = scope.clone();
                    inner.insert(binder.clone(), binder_type.clone());
                    block_value_type(body, &inner, program)
                }
            }
            // `find_index!<T>(...): Option<u64>`. Lambda body is
            // `bool`; result is `Option<u64>` regardless.
            QuantifierKind::FindIndex => {
                if let Some(sid) = framework_option_struct(program) {
                    Ok(Type::Struct {
                        struct_id: sid,
                        type_args: vec![Type::UInt(64)],
                    })
                } else {
                    let mut inner = scope.clone();
                    inner.insert(binder.clone(), binder_type.clone());
                    block_value_type(body, &inner, program)
                }
            }
            // `map!<T, U>(...): &vector<U>`. Body's value type IS
            // the element type (lambda returns `$U`). Result is
            // `Vector(body_ty)`.
            QuantifierKind::Map => {
                let mut inner = scope.clone();
                inner.insert(binder.clone(), binder_type.clone());
                let body_ty = block_value_type(body, &inner, program)?;
                Ok(Type::Vector(Box::new(body_ty)))
            }
            // `filter!<T>(...): &vector<T>`. Result vector is over
            // the INPUT element type (binder's inner type), NOT the
            // lambda body's `bool`.
            QuantifierKind::Filter => {
                let elem_ty = strip_ref(binder_type).clone();
                Ok(Type::Vector(Box::new(elem_ty)))
            }
            // `find!<T>(...): &Option<T>`. Result is `Option<T>`
            // where `T` is the binder's element type. Lambda body
            // is `bool`.
            QuantifierKind::Find => {
                let elem_ty = strip_ref(binder_type).clone();
                if let Some(sid) = framework_option_struct(program) {
                    Ok(Type::Struct {
                        struct_id: sid,
                        type_args: vec![elem_ty],
                    })
                } else {
                    // Fallback only for synthetic fixtures; legacy
                    // shape was `Vector(body_ty)` -- preserve it.
                    let mut inner = scope.clone();
                    inner.insert(binder.clone(), binder_type.clone());
                    let body_ty = block_value_type(body, &inner, program)?;
                    Ok(Type::Vector(Box::new(body_ty)))
                }
            }
            // `find_indices!<T>(...): &vector<u64>`. Result element
            // type is always `u64`, NOT the lambda body's `bool`.
            QuantifierKind::FindIndices => Ok(Type::Vector(Box::new(Type::UInt(64)))),
        },
    }
}

/// Compute the type of a value-tailed `Block`. Errors if the tail
/// is a non-Value terminator.
pub fn block_value_type(
    b: &Block,
    scope: &BTreeMap<VarId, Type>,
    program: &Program,
) -> Result<Type, TypeOfError> {
    // Build a local scope by walking stmts, inferring let types.
    let mut local: BTreeMap<VarId, Type> = scope.clone();
    for s in &b.stmts {
        if let Stmt::Let { pattern, value } = s {
            let val_ty = type_of(value, &local, program)?;
            bind_pattern(pattern, &val_ty, &mut local)?;
        }
    }
    match &b.tail {
        BlockTail::Value(e) => type_of(e, &local, program),
        other => Err(TypeOfError::MalformedAccess {
            reason: format!("expected Value tail, got {other:?}"),
        }),
    }
}

/// Add bindings from a `Stmt::Let` pattern to `scope`.
///
/// Binding semantics by pattern shape:
///
/// - `pattern.len() == 1`: bind the one slot var to the value's
///   element type. Singleton tuples `Tuple([T])` are flattened to
///   `T` -- this matches stage 3 / stage 4's "always-Tuple
///   invariant" storage form (Unit + 1 mut augments to
///   `Tuple([MutableRef<T>])`) which downstream IR bodies treat as
///   `MutableRef<T>`.
/// - `pattern.len() > 1`: value type must be a `Type::Tuple` of
///   matching arity; bind each slot to the corresponding element.
///
/// Callers that want best-effort binding (skip on mismatch instead of
/// erroring) ignore the `Err` -- on the error path nothing is bound, so
/// `let _ = bind_pattern(..)` is exactly the lenient "silently skip"
/// behavior (see `stage_05_ssa::var_types`, `stage_07_dejumps::loop_extract`).
pub(crate) fn bind_pattern(
    pattern: &[Option<VarId>],
    val_ty: &Type,
    scope: &mut BTreeMap<VarId, Type>,
) -> Result<(), TypeOfError> {
    if pattern.len() == 1 {
        if let Some(v) = &pattern[0] {
            let bound = match val_ty {
                Type::Tuple(es) if es.len() == 1 => es[0].clone(),
                _ => val_ty.clone(),
            };
            scope.insert(v.clone(), bound);
        }
        return Ok(());
    }
    // Multi-pattern -> expect Tuple value of matching arity.
    match val_ty {
        Type::Tuple(elems) if elems.len() == pattern.len() => {
            for (slot, ty) in pattern.iter().zip(elems) {
                if let Some(v) = slot {
                    scope.insert(v.clone(), ty.clone());
                }
            }
            Ok(())
        }
        _ => Err(TypeOfError::MalformedAccess {
            reason: format!(
                "multi-pattern Let expects Tuple value of arity {}, got {val_ty:?}",
                pattern.len()
            ),
        }),
    }
}

fn match_arm_value_type(
    arm: &MatchArm,
    fields: &[crate::ir::Field],
    type_args: &[Type],
    scope: &BTreeMap<VarId, Type>,
    program: &Program,
) -> Result<Type, TypeOfError> {
    let mut local = scope.clone();
    for (binding, field) in arm.bindings.iter().zip(fields) {
        local.insert(
            binding.clone(),
            substitute_type_params(&field.field_type, type_args),
        );
    }
    block_value_type(&arm.body, &local, program)
}

fn type_of_const(c: &Const) -> Type {
    match c {
        Const::Bool(_) => Type::Bool,
        Const::UInt { bits, .. } => Type::UInt(*bits),
        Const::Address(_) => Type::Address,
        Const::Vector { elem_type, .. } => Type::Vector(Box::new(elem_type.clone())),
        Const::Unit => Type::Unit,
        Const::Default(ty) => ty.clone(),
    }
}

/// Strip a single layer of `&`/`&mut` wrapping. Returns the input
/// unchanged when it is not a reference.
///
/// Used by `Quantifier` typing to recover the element type from
/// `binder_type`. `binder_type` is always `&T` (or `&mut T`) for
/// collection-binding kinds (`Map`, `Filter`, `Find`, ...) because
/// upstream's `lambda_params[slot]` is the lambda's input parameter
/// type, and `prover::vector_iter`'s lambdas all take `&T`.
fn strip_ref(ty: &Type) -> &Type {
    match ty {
        Type::Reference(inner) | Type::MutableRef { inner, .. } => inner.as_ref(),
        other => other,
    }
}

/// Resolve `MoveStdlib::integer::Integer`'s [`StructId`] from
/// `program`, if registered. Returns `None` when the program has
/// not (yet) referenced the type -- this happens in synthetic test
/// fixtures, not in real translations (any function that uses
/// `sum_map!` brings `end_sum_map_lambda<T>(): Integer` into scope,
/// which registers the struct).
///
/// Match is on `(Module::package_name, Struct::qualified_name)` so
/// a user-defined `integer::Integer` in a different package does
/// not collide.
pub(crate) fn framework_integer_struct(program: &Program) -> Option<StructId> {
    framework_struct(program, "MoveStdlib", "integer::Integer")
}

/// Resolve `MoveStdlib::option::Option`'s [`StructId`] from
/// `program`, if registered. Same fallback semantics as
/// [`framework_integer_struct`].
pub(crate) fn framework_option_struct(program: &Program) -> Option<StructId> {
    framework_struct(program, "MoveStdlib", "option::Option")
}

/// Look up a [`StructId`] by its `(package_name, qualified_name)`
/// tuple. `qualified_name` is the IR-side `{module}::{name}` form
/// stored in [`crate::ir::program::Struct::qualified_name`];
/// `package_name` is read off the struct's module entry.
///
/// `None` when no match is registered. Iterates `program.structs`
/// once -- ok for the call frequency (per-Quantifier in `type_of`)
/// because struct count is small and `type_of` is not on the hot
/// path. Could be cached on `Program` if profiling shows a need.
fn framework_struct(
    program: &Program,
    package_name: &str,
    qualified_name: &str,
) -> Option<StructId> {
    program.structs.iter().find_map(|(sid, s)| {
        if s.qualified_name != qualified_name {
            return None;
        }
        let module = program.modules.get(&s.module_id)?;
        if module.package_name == package_name {
            Some(*sid)
        } else {
            None
        }
    })
}

fn type_of_binop(op: BinOp, operand_ty: Type) -> Type {
    use BinOp::*;
    match op {
        Eq | Neq | Lt | Le | Gt | Ge | SLt | SLe | SGt | SGe | And | Or => Type::Bool,
        Add | Sub | Mul | WrappingAdd | WrappingSub | WrappingMul | SAdd | SSub | SMul | Div
        | Mod | SDiv | SMod | BitAnd | BitOr | BitXor | Shl | Shr | LShr | AShr => operand_ty,
    }
}

fn type_of_bitop(
    op: &BitOp,
    scope: &BTreeMap<VarId, Type>,
    program: &Program,
) -> Result<Type, TypeOfError> {
    match op {
        BitOp::Extract { high, low, .. } => {
            // [high:low] inclusive both ends -> width = high - low + 1.
            let width = high.checked_sub(*low).unwrap_or(0) + 1;
            Ok(Type::UInt(width))
        }
        BitOp::ZeroExtend { bits, operand } | BitOp::SignExtend { bits, operand } => {
            let inner = type_of(operand, scope, program)?;
            let inner_bits = match inner {
                Type::UInt(n) => n,
                _ => 0,
            };
            Ok(Type::UInt(inner_bits + bits))
        }
        BitOp::Concat { high, low } => {
            let h = type_of(high, scope, program)?;
            let l = type_of(low, scope, program)?;
            let hb = if let Type::UInt(n) = h { n } else { 0 };
            let lb = if let Type::UInt(n) = l { n } else { 0 };
            Ok(Type::UInt(hb + lb))
        }
    }
}

/// Recursively replace every `Type::MutableRef { inner, .. }` with
/// its `inner`. Native decls intentionally keep the `MutableRef`
/// wrapper — see the doc comment in `stage_03_mut_to_let::signatures`
/// for why.
pub fn strip_mutable_ref_in_type(ty: &Type) -> Type {
    match ty {
        Type::MutableRef { inner, .. } => strip_mutable_ref_in_type(inner),
        Type::Vector(inner) => Type::Vector(Box::new(strip_mutable_ref_in_type(inner))),
        Type::Tuple(items) => Type::Tuple(items.iter().map(strip_mutable_ref_in_type).collect()),
        Type::Reference(inner) => Type::Reference(Box::new(strip_mutable_ref_in_type(inner))),
        Type::Struct {
            struct_id,
            type_args,
        } => Type::Struct {
            struct_id: *struct_id,
            type_args: type_args.iter().map(strip_mutable_ref_in_type).collect(),
        },
        Type::Unit
        | Type::Bool
        | Type::Prop
        | Type::UInt(_)
        | Type::Address
        | Type::TypeParam(_) => ty.clone(),
    }
}

/// Substitute `Type::TypeParam(i)` in `ty` with `type_args[i]`.
/// Recursive over composite types.
pub fn substitute_type_params(ty: &Type, type_args: &[Type]) -> Type {
    match ty {
        Type::TypeParam(i) => type_args
            .get(*i as usize)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        Type::Vector(inner) => Type::Vector(Box::new(substitute_type_params(inner, type_args))),
        Type::Tuple(elems) => Type::Tuple(
            elems
                .iter()
                .map(|t| substitute_type_params(t, type_args))
                .collect(),
        ),
        Type::Struct {
            struct_id,
            type_args: ta,
        } => Type::Struct {
            struct_id: *struct_id,
            type_args: ta
                .iter()
                .map(|t| substitute_type_params(t, type_args))
                .collect(),
        },
        Type::Reference(inner) => {
            Type::Reference(Box::new(substitute_type_params(inner, type_args)))
        }
        Type::MutableRef { inner, root } => Type::MutableRef {
            inner: Box::new(substitute_type_params(inner, type_args)),
            root: Box::new(substitute_type_params(root, type_args)),
        },
        Type::Unit | Type::Bool | Type::Prop | Type::UInt(_) | Type::Address => ty.clone(),
    }
}

/// Look up the field type of a struct, with type-arg substitution.
fn field_type(
    program: &Program,
    sid: StructId,
    idx: usize,
    type_args: &[Type],
) -> Result<Type, TypeOfError> {
    let s = program
        .structs
        .get(&sid)
        .ok_or(TypeOfError::UnknownStruct(sid))?;
    let fields = if let Some(variants) = &s.variants {
        if variants.is_empty() {
            return Err(TypeOfError::MalformedAccess {
                reason: format!("Field on enum {sid} with no variants"),
            });
        }
        // `Expr::Field` / `Expr::Borrow { step: Field, .. }` carry no variant tag, so
        // for a MULTI-variant enum we cannot know which variant's field
        // is meant -- silently using variant 0 mistypes every other
        // variant (cf. the enum `Unpack` bug fixed alongside this). In
        // well-formed IR enum payloads are reached via `Match` + `Unpack`,
        // never direct field access, so a `Field` on a multi-variant enum
        // is malformed: fail loudly instead of guessing. A single-variant
        // enum is unambiguous (variant 0 is the only one), so it stays.
        if variants.len() > 1 {
            return Err(TypeOfError::MalformedAccess {
                reason: format!(
                    "Field on multi-variant enum {sid} carries no variant tag \
                     (enum payloads must go through Match/Unpack)"
                ),
            });
        }
        &variants[0].fields
    } else {
        &s.fields
    };
    let f = fields.get(idx).ok_or(TypeOfError::FieldOutOfRange {
        struct_id: sid,
        field_index: idx,
    })?;
    Ok(substitute_type_params(&f.field_type, type_args))
}

/// Peek through a singleton-tuple wrapper.
///
/// The IR's always-Tuple invariant represents an augmented return
/// uniformly as `Type::Tuple(_)`, even when the original return type
/// was a single value. Sites that match `Type::Struct` /
/// `Type::Reference` / `Type::MutableRef` against the result of a
/// call (or any value that may have been produced by an augmented
/// callee) must peek through the singleton wrapper to reach the
/// inner type. Multi-element tuples and non-tuples pass through
/// unchanged.
///
/// Precedent: `Expr::ReadRef` in `type_of` performs the same unwrap
/// inline, and the stage-4 postcondition walkers
/// (`walk_tail_expr_calls`, `check_value_augmented_or_descend`) do
/// the equivalent unwrap on `Expr::Tuple` IR shapes (commit
/// `fc637f81`).
pub fn strip_singleton_tuple(ty: &Type) -> &Type {
    if let Type::Tuple(items) = ty {
        if items.len() == 1 {
            return &items[0];
        }
    }
    ty
}

/// Pull the `type_args` out of a base expression's type, dereferencing
/// through `&` / `&mut` if needed, and peeking through a singleton
/// `Type::Tuple` wrapper at the top level.
fn base_struct_type_args(base_ty: &Type, expected_sid: StructId) -> Result<Vec<Type>, TypeOfError> {
    let base_ty = strip_singleton_tuple(base_ty);
    let inner_ty = match base_ty {
        Type::Reference(inner) | Type::MutableRef { inner, .. } => inner.as_ref(),
        other => other,
    };
    match inner_ty {
        Type::Struct {
            struct_id,
            type_args,
        } if *struct_id == expected_sid => Ok(type_args.clone()),
        _ => Err(TypeOfError::MalformedAccess {
            reason: format!("Field/Update on non-Struct(id={expected_sid}) base type {base_ty:?}"),
        }),
    }
}

/// `(inner, root)` for `Expr::Borrow { step: Field, .. }`. `inner` is
/// the substituted field type; `root` follows the chain to the source.
fn borrow_field_type(
    base_ty: &Type,
    sid: StructId,
    idx: usize,
    program: &Program,
) -> Result<(Type, Type), TypeOfError> {
    // The base may itself be a MutableRef (a chained field borrow).
    let (base_inner, root) = match base_ty {
        Type::MutableRef { inner, root } => (inner.as_ref().clone(), root.as_ref().clone()),
        Type::Reference(inner) => (inner.as_ref().clone(), inner.as_ref().clone()),
        other => (other.clone(), other.clone()),
    };
    let type_args = base_struct_type_args(&base_inner, sid).or_else(|_| {
        // Permissive: if base_inner doesn't directly look like
        // Struct(sid), still try fetching field types with empty
        // type-args. Catches edge cases where stage 2 emitted a
        // field borrow off something we can't fully introspect.
        Ok::<_, TypeOfError>(Vec::new())
    })?;
    let inner = field_type(program, sid, idx, &type_args)?;
    Ok((inner, root))
}

fn borrow_variant_field_type(
    base_ty: &Type,
    sid: StructId,
    variant_tag: usize,
    idx: usize,
    program: &Program,
) -> Result<(Type, Type), TypeOfError> {
    let base_ty = strip_singleton_tuple(base_ty);
    let (base_inner, root) = match base_ty {
        Type::MutableRef { inner, root } => (inner.as_ref(), root.as_ref().clone()),
        Type::Reference(inner) => (inner.as_ref(), inner.as_ref().clone()),
        other => (other, other.clone()),
    };
    let type_args = base_struct_type_args(base_inner, sid)?;
    let structure = program
        .structs
        .get(&sid)
        .ok_or(TypeOfError::UnknownStruct(sid))?;
    if structure.variants.is_none() {
        return Err(TypeOfError::MalformedAccess {
            reason: format!("VariantField on non-enum Struct(id={sid})"),
        });
    }
    let variant = structure
        .variant_by_tag(variant_tag)
        .ok_or(TypeOfError::UnknownVariantTag {
            struct_id: sid,
            variant: variant_tag,
        })?;
    let field = variant
        .fields
        .get(idx)
        .ok_or(TypeOfError::FieldOutOfRange {
            struct_id: sid,
            field_index: idx,
        })?;
    Ok((substitute_type_params(&field.field_type, &type_args), root))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::builder::{lit_bool, lit_u64, var};
    use crate::ir::expr::{Block, BlockTail};
    use crate::ir::function::{Function, FunctionKind, Signature};
    use crate::ir::program::{Field, Global, Module, Struct};
    use crate::ir::quant::QuantDomain;

    fn empty_program() -> Program {
        let mut p = Program::default();
        p.modules.insert(
            0,
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

    fn vid(s: &str) -> VarId {
        s.into()
    }

    fn scope_with(entries: &[(&str, Type)]) -> BTreeMap<VarId, Type> {
        entries
            .iter()
            .map(|(n, t)| (VarId::from(*n), t.clone()))
            .collect()
    }

    #[test]
    fn const_types() {
        let p = empty_program();
        let s = BTreeMap::new();
        assert_eq!(type_of(&lit_u64(0), &s, &p).unwrap(), Type::UInt(64));
        assert_eq!(type_of(&lit_bool(true), &s, &p).unwrap(), Type::Bool);
        assert_eq!(type_of(&Expr::Unit, &s, &p).unwrap(), Type::Unit);
    }

    #[test]
    fn var_lookup_returns_scope_type() {
        let p = empty_program();
        let s = scope_with(&[("x", Type::UInt(64))]);
        assert_eq!(type_of(&var("x"), &s, &p).unwrap(), Type::UInt(64));
    }

    #[test]
    fn var_unbound_errors() {
        let p = empty_program();
        let s = BTreeMap::new();
        let err = type_of(&var("x"), &s, &p).unwrap_err();
        assert_eq!(err, TypeOfError::UnboundVar(vid("x")));
    }

    #[test]
    fn borrow_global_honors_mutability() {
        let mut p = empty_program();
        p.globals.insert(
            0,
            Global {
                module_id: 0,
                name: "mutable".into(),
                ty: Type::UInt(32),
                mutable: true,
                definition: crate::ir::GlobalDefinition::BoundarySupplied,
            },
        );
        p.globals.insert(
            1,
            Global {
                module_id: 0,
                name: "readonly".into(),
                ty: Type::Bool,
                mutable: false,
                definition: crate::ir::GlobalDefinition::BoundarySupplied,
            },
        );
        let scope = BTreeMap::new();
        assert_eq!(
            type_of(&Expr::BorrowGlobal(0), &scope, &p).unwrap(),
            Type::MutableRef {
                inner: Box::new(Type::UInt(32)),
                root: Box::new(Type::UInt(32)),
            }
        );
        assert_eq!(
            type_of(&Expr::BorrowGlobal(1), &scope, &p).unwrap(),
            Type::Reference(Box::new(Type::Bool))
        );
        assert_eq!(
            type_of(&Expr::BorrowGlobal(9), &scope, &p),
            Err(TypeOfError::UnknownGlobal(9))
        );
    }

    #[test]
    fn binop_arithmetic_preserves_type() {
        let p = empty_program();
        let s = scope_with(&[("a", Type::UInt(32))]);
        let e = Expr::BinOp {
            op: BinOp::Add,
            lhs: Box::new(var("a")),
            rhs: Box::new(var("a")),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(32));
    }

    #[test]
    fn binop_comparison_returns_bool() {
        let p = empty_program();
        let s = scope_with(&[("a", Type::UInt(64))]);
        let e = Expr::BinOp {
            op: BinOp::Lt,
            lhs: Box::new(var("a")),
            rhs: Box::new(lit_u64(5)),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::Bool);
    }

    #[test]
    fn binop_logical_returns_bool() {
        let p = empty_program();
        let s = scope_with(&[("a", Type::Bool), ("b", Type::Bool)]);
        let e = Expr::BinOp {
            op: BinOp::And,
            lhs: Box::new(var("a")),
            rhs: Box::new(var("b")),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::Bool);
    }

    #[test]
    fn unop_cast_returns_target_width() {
        let p = empty_program();
        let s = scope_with(&[("x", Type::UInt(64))]);
        let e = Expr::UnOp {
            op: UnOp::Cast(8),
            operand: Box::new(var("x")),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(8));
    }

    #[test]
    fn unop_not_returns_bool() {
        let p = empty_program();
        let s = scope_with(&[("b", Type::Bool)]);
        let e = Expr::UnOp {
            op: UnOp::Not,
            operand: Box::new(var("b")),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::Bool);
    }

    #[test]
    fn tuple_of_typed_elems() {
        let p = empty_program();
        let s = scope_with(&[("a", Type::UInt(64)), ("b", Type::Bool)]);
        let e = Expr::Tuple(vec![var("a"), var("b")]);
        assert_eq!(
            type_of(&e, &s, &p).unwrap(),
            Type::Tuple(vec![Type::UInt(64), Type::Bool])
        );
    }

    fn func(name: &str, ret: Type) -> Function {
        Function {
            module: 0,
            name: name.to_string(),
            signature: Signature {
                type_params: vec!["T".to_string()],
                params: vec![],
                return_type: ret,
            },
            body: Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::Unit),
            },
            kind: FunctionKind::Source,
            effects: crate::ir::Effects::CONSERVATIVE,
            explicit_pure: false,
        }
    }

    #[test]
    fn call_returns_callee_return_type_with_substitution() {
        let mut p = empty_program();
        // f<T>() -> T
        p.functions.insert(0, func("f", Type::TypeParam(0)));
        let s = BTreeMap::new();
        let e = Expr::Call {
            fun: 0,
            type_args: vec![Type::UInt(64)],
            args: vec![],
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(64));
    }

    #[test]
    fn call_unknown_fid_errors() {
        let p = empty_program();
        let s = BTreeMap::new();
        let e = Expr::Call {
            fun: 99,
            type_args: vec![],
            args: vec![],
        };
        assert_eq!(
            type_of(&e, &s, &p).unwrap_err(),
            TypeOfError::UnknownFunction(99)
        );
    }

    fn struct_with_fields(p: &mut Program, sid: StructId, fields: Vec<(&str, Type)>) {
        let s = Struct {
            module_id: 0,
            name: format!("S{sid}"),
            qualified_name: format!("S{sid}"),
            type_params: vec!["T".to_string()],
            fields: fields
                .into_iter()
                .map(|(n, t)| Field {
                    name: n.to_string(),
                    field_type: t,
                })
                .collect(),
            variants: None,
            is_native: false,
        };
        p.structs.insert(sid, s);
    }

    #[test]
    fn pack_returns_struct_type() {
        let mut p = empty_program();
        struct_with_fields(&mut p, 0, vec![("v", Type::UInt(64))]);
        let s = BTreeMap::new();
        let e = Expr::Pack {
            struct_id: 0,
            type_args: vec![Type::Bool],
            variant: None,
            fields: vec![lit_u64(1)],
        };
        assert_eq!(
            type_of(&e, &s, &p).unwrap(),
            Type::Struct {
                struct_id: 0,
                type_args: vec![Type::Bool],
            }
        );
    }

    #[test]
    fn field_returns_substituted_field_type() {
        let mut p = empty_program();
        // S<T> { v: T }
        struct_with_fields(&mut p, 0, vec![("v", Type::TypeParam(0))]);
        let s = scope_with(&[(
            "x",
            Type::Struct {
                struct_id: 0,
                type_args: vec![Type::UInt(64)],
            },
        )]);
        let e = Expr::Field {
            struct_id: 0,
            field_index: 0,
            base: Box::new(var("x")),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(64));
    }

    #[test]
    fn field_through_singleton_tuple_unwraps() {
        // Honor the IR's always-Tuple invariant: a base whose type
        // is `Tuple([MutableRef(Struct)])` (the augmented-return
        // shape for a callee returning `&mut Struct`) must be
        // treated as `MutableRef(Struct)` when used as a Field base.
        let mut p = empty_program();
        struct_with_fields(&mut p, 0, vec![("v", Type::UInt(64))]);
        let s = scope_with(&[(
            "x",
            Type::Tuple(vec![Type::MutableRef {
                inner: Box::new(Type::Struct {
                    struct_id: 0,
                    type_args: vec![],
                }),
                root: Box::new(Type::Struct {
                    struct_id: 0,
                    type_args: vec![],
                }),
            }]),
        )]);
        let e = Expr::Field {
            struct_id: 0,
            field_index: 0,
            base: Box::new(var("x")),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(64));
    }

    #[test]
    fn update_field_unwraps_singleton_tuple_result() {
        // UpdateField's result type follows its base. When the base
        // is `Tuple([MutableRef(Struct)])` (the augmented-return
        // shape), the result should be the unwrapped MutableRef(Struct)
        // -- not the 1-tuple wrapper -- so downstream consumers
        // (e.g. another Field off the UpdateField) don't trip.
        let mut p = empty_program();
        struct_with_fields(&mut p, 0, vec![("v", Type::UInt(64))]);
        let s = scope_with(&[(
            "x",
            Type::Tuple(vec![Type::MutableRef {
                inner: Box::new(Type::Struct {
                    struct_id: 0,
                    type_args: vec![],
                }),
                root: Box::new(Type::Struct {
                    struct_id: 0,
                    type_args: vec![],
                }),
            }]),
        )]);
        let e = Expr::Update {
            step: crate::ir::path::PathStep::Field {
                struct_id: 0,
                field_index: 0,
            },
            base: Box::new(var("x")),
            value: Box::new(lit_u64(7)),
        };
        match type_of(&e, &s, &p).unwrap() {
            Type::MutableRef { inner, .. } => {
                assert_eq!(
                    *inner,
                    Type::Struct {
                        struct_id: 0,
                        type_args: vec![],
                    }
                );
            }
            other => panic!("expected MutableRef, got {other:?}"),
        }
    }

    #[test]
    fn field_out_of_range_errors() {
        let mut p = empty_program();
        struct_with_fields(&mut p, 0, vec![("v", Type::UInt(64))]);
        let s = scope_with(&[(
            "x",
            Type::Struct {
                struct_id: 0,
                type_args: vec![],
            },
        )]);
        let e = Expr::Field {
            struct_id: 0,
            field_index: 99,
            base: Box::new(var("x")),
        };
        assert_eq!(
            type_of(&e, &s, &p).unwrap_err(),
            TypeOfError::FieldOutOfRange {
                struct_id: 0,
                field_index: 99
            }
        );
    }

    fn enum_with_variants(p: &mut Program, sid: StructId, variants: Vec<(&str, Vec<Type>)>) {
        use crate::ir::program::Variant;
        let s = Struct {
            module_id: 0,
            name: format!("E{sid}"),
            qualified_name: format!("E{sid}"),
            type_params: vec!["T".to_string()],
            fields: Vec::new(),
            variants: Some(
                variants
                    .into_iter()
                    .enumerate()
                    .map(|(tag, (n, tys))| Variant {
                        name: n.to_string(),
                        tag,
                        fields: tys
                            .into_iter()
                            .enumerate()
                            .map(|(i, t)| Field {
                                name: format!("f{i}"),
                                field_type: t,
                            })
                            .collect(),
                    })
                    .collect(),
            ),
            is_native: false,
        };
        p.structs.insert(sid, s);
    }

    #[test]
    fn borrow_variant_field_resolves_tag_and_substitutes_type_args() {
        use crate::ir::path::PathStep;

        let mut p = empty_program();
        enum_with_variants(
            &mut p,
            0,
            vec![
                ("Other", vec![Type::Bool]),
                ("Selected", vec![Type::UInt(8), Type::TypeParam(0)]),
            ],
        );
        p.structs.get_mut(&0).unwrap().variants.as_mut().unwrap()[0].tag = 3;
        p.structs.get_mut(&0).unwrap().variants.as_mut().unwrap()[1].tag = 9;
        let enum_type = Type::Struct {
            struct_id: 0,
            type_args: vec![Type::Address],
        };
        let scope = scope_with(&[(
            "carrier",
            Type::MutableRef {
                inner: Box::new(enum_type),
                root: Box::new(Type::UInt(256)),
            },
        )]);
        let expression = Expr::Borrow {
            step: PathStep::VariantField {
                struct_id: 0,
                variant: 9,
                field_index: 1,
            },
            base: Box::new(var("carrier")),
        };

        assert_eq!(
            type_of(&expression, &scope, &p).unwrap(),
            Type::MutableRef {
                inner: Box::new(Type::Address),
                root: Box::new(Type::UInt(256)),
            }
        );
    }

    #[test]
    fn borrow_variant_field_rejects_unknown_tag() {
        use crate::ir::path::PathStep;

        let mut p = empty_program();
        enum_with_variants(&mut p, 0, vec![("Only", vec![Type::Bool])]);
        let scope = scope_with(&[(
            "carrier",
            Type::Struct {
                struct_id: 0,
                type_args: vec![Type::UInt(64)],
            },
        )]);
        let expression = Expr::Borrow {
            step: PathStep::VariantField {
                struct_id: 0,
                variant: 7,
                field_index: 0,
            },
            base: Box::new(var("carrier")),
        };

        assert_eq!(
            type_of(&expression, &scope, &p).unwrap_err(),
            TypeOfError::UnknownVariantTag {
                struct_id: 0,
                variant: 7,
            }
        );
    }

    #[test]
    fn match_payload_binding_uses_concrete_selector_type_args() {
        let mut p = empty_program();
        enum_with_variants(&mut p, 0, vec![("Carry", vec![Type::TypeParam(0)])]);
        p.structs.get_mut(&0).unwrap().variants.as_mut().unwrap()[0].tag = 7;
        let payload_type = Type::Tuple(vec![Type::UInt(64), Type::Bool]);
        let s = scope_with(&[(
            "carrier",
            Type::Struct {
                struct_id: 0,
                type_args: vec![payload_type.clone()],
            },
        )]);
        let e = Expr::Match {
            struct_id: 0,
            selector: Box::new(var("carrier")),
            cases: vec![MatchArm {
                variant: 7,
                bindings: vec![vid("payload")],
                body: Box::new(Block::just(var("payload"))),
            }],
        };

        assert_eq!(type_of(&e, &s, &p).unwrap(), payload_type);
    }

    #[test]
    fn unpack_uses_matched_variant_fields() {
        // Regression: an enum `Unpack` must type its payload from the
        // MATCHED variant's fields, not variant 0's. cetus-dlmm
        // `BlockEntity::POSITION(ID)` (v1) was being typed as the v0
        // `USER(address)` payload, so the extracted continuation applied
        // `id_to_address` to an `Address`. See type_of's Unpack arm.
        let mut p = empty_program();
        enum_with_variants(
            &mut p,
            0,
            vec![
                ("V0", vec![Type::Bool]),
                ("V1", vec![Type::UInt(64), Type::Address]),
            ],
        );
        p.structs.get_mut(&0).unwrap().variants.as_mut().unwrap()[0].tag = 3;
        p.structs.get_mut(&0).unwrap().variants.as_mut().unwrap()[1].tag = 7;
        let s = scope_with(&[(
            "x",
            Type::Struct {
                struct_id: 0,
                type_args: vec![],
            },
        )]);
        // Tag 7 -> Tuple of v1's two fields, NOT v0's single Bool.
        let e1 = Expr::Unpack {
            struct_id: 0,
            variant: Some(7),
            value: Box::new(var("x")),
        };
        assert_eq!(
            type_of(&e1, &s, &p).unwrap(),
            Type::Tuple(vec![Type::UInt(64), Type::Address])
        );
        // Tag 3 -> its single field, unwrapped (no 1-tuple).
        let e0 = Expr::Unpack {
            struct_id: 0,
            variant: Some(3),
            value: Box::new(var("x")),
        };
        assert_eq!(type_of(&e0, &s, &p).unwrap(), Type::Bool);
    }

    #[test]
    fn unpack_enum_variant_substitutes_type_args() {
        // The matched variant's field types are substituted with the
        // value's type-args, exactly like plain-struct fields.
        let mut p = empty_program();
        enum_with_variants(
            &mut p,
            0,
            vec![("V0", vec![Type::Bool]), ("V1", vec![Type::TypeParam(0)])],
        );
        let s = scope_with(&[(
            "x",
            Type::Struct {
                struct_id: 0,
                type_args: vec![Type::UInt(128)],
            },
        )]);
        let e = Expr::Unpack {
            struct_id: 0,
            variant: Some(1),
            value: Box::new(var("x")),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(128));
    }

    #[test]
    fn unpack_variant_out_of_range_errors() {
        let mut p = empty_program();
        enum_with_variants(&mut p, 0, vec![("V0", vec![Type::Bool])]);
        let s = scope_with(&[(
            "x",
            Type::Struct {
                struct_id: 0,
                type_args: vec![],
            },
        )]);
        let e = Expr::Unpack {
            struct_id: 0,
            variant: Some(7),
            value: Box::new(var("x")),
        };
        match type_of(&e, &s, &p).unwrap_err() {
            TypeOfError::MalformedAccess { reason } => {
                assert!(reason.contains("variant tag 7"), "got: {reason}");
            }
            other => panic!("expected MalformedAccess, got {other:?}"),
        }
    }

    #[test]
    fn unpack_enum_without_variant_tag_errors() {
        let mut p = empty_program();
        enum_with_variants(&mut p, 0, vec![("V0", vec![Type::Bool])]);
        let s = scope_with(&[(
            "x",
            Type::Struct {
                struct_id: 0,
                type_args: vec![],
            },
        )]);
        let e = Expr::Unpack {
            struct_id: 0,
            variant: None,
            value: Box::new(var("x")),
        };

        match type_of(&e, &s, &p).unwrap_err() {
            TypeOfError::MalformedAccess { reason } => {
                assert!(reason.contains("missing a variant tag"), "got: {reason}");
            }
            other => panic!("expected MalformedAccess, got {other:?}"),
        }
    }

    #[test]
    fn borrow_loc_returns_mutable_ref() {
        let p = empty_program();
        let s = scope_with(&[("x", Type::UInt(64))]);
        let e = Expr::BorrowLoc(vid("x"));
        match type_of(&e, &s, &p).unwrap() {
            Type::MutableRef { inner, root } => {
                assert_eq!(*inner, Type::UInt(64));
                assert_eq!(*root, Type::UInt(64));
            }
            other => panic!("expected MutableRef, got {other:?}"),
        }
    }

    #[test]
    fn borrow_loc_of_immutable_reference_borrows_underlying_value() {
        // Regression (sui-system
        // `metadata_invalid_equal_both_pubkey_next_epoch`):
        // `*validator.network_pubkey_bytes()` -- getter returns
        // `&vector<u8>` -- is erased to a plain value local by upstream
        // EliminateImmRefs (the result is stored straight into the local
        // with no `ReadRef`). A following `&mut` (`borrow_mut(0)`) must
        // borrow that underlying VALUE, yielding `MutableRef { Vector }`,
        // NOT the un-representable `MutableRef { Reference(Vector) }`.
        let p = empty_program();
        let vec_u8 = Type::Vector(Box::new(Type::UInt(8)));
        let s = scope_with(&[("pk", Type::Reference(Box::new(vec_u8.clone())))]);
        let e = Expr::BorrowLoc(vid("pk"));
        match type_of(&e, &s, &p).unwrap() {
            Type::MutableRef { inner, root } => {
                assert_eq!(*inner, vec_u8);
                assert_eq!(*root, vec_u8);
            }
            other => panic!("expected MutableRef of the erased value, got {other:?}"),
        }
    }

    #[test]
    fn borrow_vec_index_through_immutable_ref_local_resolves() {
        // The full failing chain: a local holding an immutable-ref value,
        // `&mut`-borrowed, then indexed. `BorrowLoc` must peel the
        // immutable `Reference` so the `VecIndex` arm sees
        // `MutableRef { Vector }` and resolves to the element type --
        // the reference-to-reference must not occur (previously panicked
        // `MalformedAccess { Borrow VecIndex of non-vector type
        // Reference(Vector(UInt(8))) }`).
        use crate::ir::path::PathStep;
        let p = empty_program();
        let s = scope_with(&[(
            "pk",
            Type::Reference(Box::new(Type::Vector(Box::new(Type::UInt(8))))),
        )]);
        let e = Expr::Borrow {
            step: PathStep::VecIndex(Box::new(lit_u64(0))),
            base: Box::new(Expr::BorrowLoc(vid("pk"))),
        };
        match type_of(&e, &s, &p).unwrap() {
            Type::MutableRef { inner, .. } => assert_eq!(*inner, Type::UInt(8)),
            other => panic!("expected MutableRef of element type, got {other:?}"),
        }
    }

    #[test]
    fn read_ref_dereferences() {
        let p = empty_program();
        let s = scope_with(&[(
            "r",
            Type::MutableRef {
                inner: Box::new(Type::UInt(64)),
                root: Box::new(Type::UInt(64)),
            },
        )]);
        let e = Expr::ReadRef(Box::new(var("r")));
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(64));
    }

    #[test]
    fn if_picks_value_arm_type() {
        let p = empty_program();
        let s = BTreeMap::new();
        let then_b = Block {
            stmts: vec![],
            tail: BlockTail::Value(lit_u64(1)),
        };
        let else_b = Block {
            stmts: vec![],
            tail: BlockTail::Value(lit_u64(2)),
        };
        let e = Expr::If {
            cond: Box::new(lit_bool(true)),
            then_branch: Box::new(then_b),
            else_branch: Box::new(else_b),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(64));
    }

    #[test]
    fn if_falls_through_to_else_when_then_aborts() {
        let p = empty_program();
        let s = BTreeMap::new();
        let then_b = Block {
            stmts: vec![],
            tail: BlockTail::Abort {
                code: Box::new(lit_u64(7)),
            },
        };
        let else_b = Block {
            stmts: vec![],
            tail: BlockTail::Value(lit_u64(2)),
        };
        let e = Expr::If {
            cond: Box::new(lit_bool(true)),
            then_branch: Box::new(then_b),
            else_branch: Box::new(else_b),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(64));
    }

    #[test]
    fn while_returns_iter_locals_tuple() {
        let p = empty_program();
        let s = scope_with(&[("init_i", Type::UInt(64)), ("init_n", Type::UInt(32))]);
        let e = Expr::While {
            header: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::Unit),
            }),
            cond: Box::new(lit_bool(true)),
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Continue {
                    level: 0,
                    value: Box::new(Expr::Unit),
                },
            }),
            iter_locals: vec![(vid("i"), var("init_i")), (vid("n"), var("init_n"))],
            header_exit_locals: vec![vid("i"), vid("n")],
            live_out: vec![],
        };
        assert_eq!(
            type_of(&e, &s, &p).unwrap(),
            Type::Tuple(vec![Type::UInt(64), Type::UInt(32)])
        );
    }

    #[test]
    fn while_with_one_iter_local_unwraps_to_singleton() {
        let p = empty_program();
        let s = scope_with(&[("init_i", Type::UInt(64))]);
        let e = Expr::While {
            header: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::Unit),
            }),
            cond: Box::new(lit_bool(true)),
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Continue {
                    level: 0,
                    value: Box::new(Expr::Unit),
                },
            }),
            iter_locals: vec![(vid("i"), var("init_i"))],
            header_exit_locals: vec![vid("i")],
            live_out: vec![],
        };
        // Single iter_local -> bare type, not Tuple.
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(64));
    }

    #[test]
    fn while_with_no_iter_locals_returns_unit() {
        let p = empty_program();
        let s = BTreeMap::new();
        let e = Expr::While {
            header: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::Unit),
            }),
            cond: Box::new(lit_bool(true)),
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Break {
                    level: 0,
                    value: Box::new(Expr::Unit),
                },
            }),
            iter_locals: vec![],
            header_exit_locals: vec![],
            live_out: vec![],
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::Unit);
    }

    #[test]
    fn while_live_out_appends_header_local_types() {
        // A live-out var bound in the header escapes the loop as an
        // extra trailing tuple element, typed from the header scope
        // (iter-local binders + header lets), NOT the outer scope.
        // Guards the stage-5 live_out round-trip.
        let p = empty_program();
        let s = scope_with(&[("init_i", Type::UInt(64))]);
        let e = Expr::While {
            header: Box::new(Block {
                // h = i + 1 -- references the iter-local binder `i`.
                stmts: vec![crate::ir::expr::Stmt::Let {
                    pattern: vec![Some(vid("h"))],
                    value: Expr::BinOp {
                        op: BinOp::Add,
                        lhs: Box::new(var("i")),
                        rhs: Box::new(lit_u64(1)),
                    },
                }],
                tail: BlockTail::Value(Expr::Unit),
            }),
            cond: Box::new(lit_bool(true)),
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Continue {
                    level: 0,
                    value: Box::new(Expr::Unit),
                },
            }),
            iter_locals: vec![(vid("i"), var("init_i"))],
            header_exit_locals: vec![vid("i")],
            live_out: vec![(vid("h"), vid("h_post"))],
        };
        // iter-local `i` (UInt 64) followed by live-out `h` (UInt 64).
        assert_eq!(
            type_of(&e, &s, &p).unwrap(),
            Type::Tuple(vec![Type::UInt(64), Type::UInt(64)])
        );
    }

    #[test]
    fn while_exit_override_replaces_carried_slot_without_growing_result() {
        let p = empty_program();
        let s = scope_with(&[("init_i", Type::UInt(64))]);
        let e = Expr::While {
            header: Box::new(Block {
                stmts: vec![crate::ir::expr::Stmt::Let {
                    pattern: vec![Some(vid("i_next"))],
                    value: Expr::BinOp {
                        op: BinOp::Add,
                        lhs: Box::new(var("i")),
                        rhs: Box::new(lit_u64(1)),
                    },
                }],
                tail: BlockTail::Value(Expr::Unit),
            }),
            cond: Box::new(lit_bool(true)),
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Continue {
                    level: 0,
                    value: Box::new(var("i_next")),
                },
            }),
            iter_locals: vec![(vid("i"), var("init_i"))],
            // The post-header value of carried slot `i` is `i_next`; the merged
            // representation records that in `header_exit_locals`. type_of also
            // still tolerates the legacy destination-is-a-binder override form
            // in `live_out` without adding a result slot.
            header_exit_locals: vec![vid("i_next")],
            live_out: vec![(vid("i_next"), vid("i"))],
        };

        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(64));
    }

    #[test]
    fn bitop_extract_width_is_high_minus_low_plus_one() {
        let p = empty_program();
        let s = scope_with(&[("x", Type::UInt(64))]);
        // [7:3] inclusive -> width 5.
        let e = Expr::BitOp(BitOp::Extract {
            high: 7,
            low: 3,
            operand: Box::new(var("x")),
        });
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(5));
    }

    #[test]
    fn bitop_concat_sums_operand_widths() {
        let p = empty_program();
        let s = scope_with(&[("hi", Type::UInt(8)), ("lo", Type::UInt(16))]);
        let e = Expr::BitOp(BitOp::Concat {
            high: Box::new(var("hi")),
            low: Box::new(var("lo")),
        });
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(24));
    }

    #[test]
    fn bitop_extend_adds_bits_to_operand_width() {
        let p = empty_program();
        let s = scope_with(&[("x", Type::UInt(8))]);
        let ze = Expr::BitOp(BitOp::ZeroExtend {
            bits: 8,
            operand: Box::new(var("x")),
        });
        assert_eq!(type_of(&ze, &s, &p).unwrap(), Type::UInt(16));
        let se = Expr::BitOp(BitOp::SignExtend {
            bits: 24,
            operand: Box::new(var("x")),
        });
        assert_eq!(type_of(&se, &s, &p).unwrap(), Type::UInt(32));
    }

    #[test]
    fn quantifier_forall_is_bool() {
        let p = empty_program();
        let s = BTreeMap::new();
        let e = Expr::Quantifier {
            kind: QuantifierKind::Forall,
            binder: vid("x"),
            binder_type: Type::UInt(64),
            domain: QuantDomain::Unbounded,
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(lit_bool(true)),
            }),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::Bool);
    }

    /// Register a synthetic `MoveStdlib::<module>::<name>` struct.
    /// Reuses module 0 (`empty_program`'s default) but flips its
    /// `package_name` to `MoveStdlib` for the duration of the test.
    /// Returns the allocated `StructId`.
    fn register_framework_struct(
        p: &mut Program,
        sid: StructId,
        module_name: &str,
        struct_name: &str,
        type_params: Vec<String>,
    ) {
        if let Some(m) = p.modules.get_mut(&0) {
            m.package_name = "MoveStdlib".to_string();
            m.name = module_name.to_string();
        }
        p.structs.insert(
            sid,
            Struct {
                module_id: 0,
                name: struct_name.to_string(),
                qualified_name: format!("{module_name}::{struct_name}"),
                type_params,
                fields: vec![],
                variants: None,
                is_native: false,
            },
        );
    }

    /// `sum_map!` returns `Integer`, never the lambda body's type.
    /// Regression test for the bug where `type_of` reported the
    /// body's `UInt(64)` and the `BinOpOperandTypesAgree` invariant
    /// fired on `Integer == sum_map!(...)` ember specs.
    #[test]
    fn quantifier_sum_map_is_integer_not_body_type() {
        let mut p = empty_program();
        register_framework_struct(&mut p, 7, "integer", "Integer", vec![]);
        let s = BTreeMap::new();
        // Body evaluates to UInt(64) (modeling `|x| x.get_request_shares()`).
        let e = Expr::Quantifier {
            kind: QuantifierKind::SumMap,
            binder: vid("x"),
            binder_type: Type::Reference(Box::new(Type::UInt(64))),
            domain: QuantDomain::Unbounded,
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(lit_u64(0)),
            }),
        };
        assert_eq!(
            type_of(&e, &s, &p).unwrap(),
            Type::Struct {
                struct_id: 7,
                type_args: vec![],
            }
        );
    }

    /// Without `Integer` registered, `SumMap` falls back to the
    /// legacy body-typed answer so synthetic test fixtures keep
    /// working. Real translations always register Integer (via the
    /// macro expansion's `end_sum_map_lambda<T>(): Integer`).
    #[test]
    fn quantifier_sum_map_fallback_when_integer_missing() {
        let p = empty_program();
        let s = BTreeMap::new();
        let e = Expr::Quantifier {
            kind: QuantifierKind::SumMap,
            binder: vid("x"),
            binder_type: Type::Reference(Box::new(Type::UInt(64))),
            domain: QuantDomain::Unbounded,
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(lit_u64(0)),
            }),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::UInt(64));
    }

    /// `find_index!` returns `Option<u64>` regardless of body type.
    #[test]
    fn quantifier_find_index_is_option_u64() {
        let mut p = empty_program();
        register_framework_struct(&mut p, 7, "option", "Option", vec!["T".to_string()]);
        let s = BTreeMap::new();
        let e = Expr::Quantifier {
            kind: QuantifierKind::FindIndex,
            binder: vid("x"),
            binder_type: Type::Reference(Box::new(Type::UInt(64))),
            domain: QuantDomain::Unbounded,
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(lit_bool(true)),
            }),
        };
        assert_eq!(
            type_of(&e, &s, &p).unwrap(),
            Type::Struct {
                struct_id: 7,
                type_args: vec![Type::UInt(64)],
            }
        );
    }

    /// `filter!` returns `Vector<element_ty>` (the binder's inner
    /// type, with `&` stripped), NOT `Vector<bool>`.
    #[test]
    fn quantifier_filter_is_vector_of_element_type_not_body_type() {
        let p = empty_program();
        let s = BTreeMap::new();
        let e = Expr::Quantifier {
            kind: QuantifierKind::Filter,
            binder: vid("x"),
            binder_type: Type::Reference(Box::new(Type::UInt(64))),
            domain: QuantDomain::Unbounded,
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(lit_bool(true)),
            }),
        };
        assert_eq!(
            type_of(&e, &s, &p).unwrap(),
            Type::Vector(Box::new(Type::UInt(64)))
        );
    }

    /// `find!` returns `Option<element_ty>`, NOT `Vector<bool>`.
    #[test]
    fn quantifier_find_is_option_of_element_type() {
        let mut p = empty_program();
        register_framework_struct(&mut p, 7, "option", "Option", vec!["T".to_string()]);
        let s = BTreeMap::new();
        let e = Expr::Quantifier {
            kind: QuantifierKind::Find,
            binder: vid("x"),
            binder_type: Type::Reference(Box::new(Type::UInt(64))),
            domain: QuantDomain::Unbounded,
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(lit_bool(true)),
            }),
        };
        assert_eq!(
            type_of(&e, &s, &p).unwrap(),
            Type::Struct {
                struct_id: 7,
                type_args: vec![Type::UInt(64)],
            }
        );
    }

    /// `find_indices!` returns `Vector<u64>` regardless of body or
    /// element type.
    #[test]
    fn quantifier_find_indices_is_vector_u64() {
        let p = empty_program();
        let s = BTreeMap::new();
        let e = Expr::Quantifier {
            kind: QuantifierKind::FindIndices,
            binder: vid("x"),
            binder_type: Type::Reference(Box::new(Type::Bool)),
            domain: QuantDomain::Unbounded,
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(lit_bool(true)),
            }),
        };
        assert_eq!(
            type_of(&e, &s, &p).unwrap(),
            Type::Vector(Box::new(Type::UInt(64)))
        );
    }

    /// `map!` keeps the legacy `Vector<body_ty>` shape -- the
    /// lambda's return type IS the element type for map.
    #[test]
    fn quantifier_map_is_vector_of_body_type() {
        let p = empty_program();
        let s = BTreeMap::new();
        let e = Expr::Quantifier {
            kind: QuantifierKind::Map,
            binder: vid("x"),
            binder_type: Type::Reference(Box::new(Type::UInt(64))),
            domain: QuantDomain::Unbounded,
            body: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(lit_bool(true)),
            }),
        };
        // body returns Bool; Map's result element type is the body's.
        assert_eq!(
            type_of(&e, &s, &p).unwrap(),
            Type::Vector(Box::new(Type::Bool))
        );
    }

    #[test]
    fn coercion_to_prop_returns_prop() {
        let p = empty_program();
        let s = BTreeMap::new();
        let e = Expr::ToProp(Box::new(lit_bool(true)));
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::Prop);
    }

    #[test]
    fn block_value_type_threads_lets() {
        // { let x = 5; x + 1 }  -> UInt(64)
        let p = empty_program();
        let s = BTreeMap::new();
        let b = Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(vid("x"))],
                value: lit_u64(5),
            }],
            tail: BlockTail::Value(Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(var("x")),
                rhs: Box::new(lit_u64(1)),
            }),
        };
        assert_eq!(block_value_type(&b, &s, &p).unwrap(), Type::UInt(64));
    }

    #[test]
    fn block_value_type_handles_tuple_destructure() {
        // { let (a, b) = (5u64, true); b }  -> Bool
        let p = empty_program();
        let s = BTreeMap::new();
        let b = Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(vid("a")), Some(vid("b"))],
                value: Expr::Tuple(vec![lit_u64(5), lit_bool(true)]),
            }],
            tail: BlockTail::Value(var("b")),
        };
        assert_eq!(block_value_type(&b, &s, &p).unwrap(), Type::Bool);
    }

    #[test]
    fn write_ref_rejects_an_immutable_reference() {
        let mut p = empty_program();
        p.globals.insert(
            0,
            Global {
                module_id: 0,
                name: "readonly".into(),
                ty: Type::UInt(64),
                mutable: false,
                definition: crate::ir::GlobalDefinition::BoundarySupplied,
            },
        );
        let e = Expr::WriteRef {
            reference: Box::new(Expr::BorrowGlobal(0)),
            value: Box::new(lit_u64(1)),
        };
        assert!(matches!(
            type_of(&e, &BTreeMap::new(), &p),
            Err(TypeOfError::MalformedAccess { reason })
                if reason.contains("WriteRef through an immutable reference")
        ));
    }

    /// A value-typed WriteRef operand is legitimate: `stage_04_ghost`
    /// lowers `*ghost::borrow_mut<K, V>() = e` onto the threaded ghost
    /// var, which carries the ghost's VALUE type. Requiring a
    /// `MutableRef` here rejected every spec that writes a ghost.
    #[test]
    fn write_ref_accepts_a_value_typed_operand() {
        let p = empty_program();
        let s = scope_with(&[("__ghost_m__Marker", Type::Bool)]);
        let e = Expr::WriteRef {
            reference: Box::new(var("__ghost_m__Marker")),
            value: Box::new(lit_bool(false)),
        };
        assert_eq!(type_of(&e, &s, &p).unwrap(), Type::Bool);
    }

    #[test]
    fn write_ref_accepts_mutable_reference() {
        let p = empty_program();
        let s = scope_with(&[(
            "r",
            Type::MutableRef {
                inner: Box::new(Type::UInt(64)),
                root: Box::new(Type::UInt(64)),
            },
        )]);
        let valid = Expr::WriteRef {
            reference: Box::new(var("r")),
            value: Box::new(lit_u64(1)),
        };
        assert_eq!(type_of(&valid, &s, &p).unwrap(), s[&vid("r")]);
    }

    #[test]
    fn substitute_type_params_recurses_into_composites() {
        // Vector<Tuple<T, Bool>> with T=UInt(64).
        let ty = Type::Vector(Box::new(Type::Tuple(vec![Type::TypeParam(0), Type::Bool])));
        let result = substitute_type_params(&ty, &[Type::UInt(64)]);
        assert_eq!(
            result,
            Type::Vector(Box::new(Type::Tuple(vec![Type::UInt(64), Type::Bool,])))
        );
    }
}
