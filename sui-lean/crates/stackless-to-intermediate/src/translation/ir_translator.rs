// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

use super::{convert_binop, convert_constant, convert_constant_with_type};
use crate::program_builder::ProgramBuilder;
use intermediate_theorem_format::{IRNode, QuantifierKind, TempId, UnOp, WriteBackEdge};
use move_model::model::{FunId, QualifiedId};
use move_model::ty::Type as MoveType;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::{
    BorrowEdge, BorrowNode, Bytecode, Constant, Operation, QuantifierType,
};
use std::rc::Rc;

pub fn translate_one(
    target: &FunctionTarget,
    builder: &mut ProgramBuilder,
    borrow_state: &super::borrow_tracking::BorrowState,
    bytecode: &Bytecode,
) -> IRNode {
    match bytecode {
        Bytecode::Assign(_, dest, src, _) => make_let(target, &[*dest], make_var(target, *src)),

        Bytecode::Load(_, dest, constant) => {
            // Get the expected type from the destination temp for better type inference
            let dest_type = target.get_local_type(*dest);
            let expected_type = builder.convert_type(dest_type);
            let cnst = convert_constant_with_type(constant, &expected_type);
            make_let(target, &[*dest], IRNode::Const(cnst))
        }

        Bytecode::Call(_, dests, operation, srcs, _) => {
            // For real function calls, swap in the live child borrow for any
            // src slot whose declared type doesn't match the callee's expected
            // param type. Move stackless bytecode encodes mutable-reference
            // arguments by passing the parent slot index plus borrow-graph
            // metadata (see docs/borrow-translation.md).
            let callee_param_types = match operation {
                Operation::Function(mid, fid, type_args)
                | Operation::OpaqueCallBegin(mid, fid, type_args)
                | Operation::OpaqueCallEnd(mid, fid, type_args) => {
                    let module_env = builder.env().get_module(*mid);
                    let func_env = module_env.get_function(*fid);
                    let raw: Vec<MoveType> = func_env.get_parameter_types();
                    Some(
                        raw.into_iter()
                            .map(|t| t.instantiate(type_args))
                            .collect::<Vec<_>>(),
                    )
                }
                _ => None,
            };
            let args: Vec<IRNode> = srcs
                .iter()
                .enumerate()
                .map(|(i, &t)| {
                    let resolved = match callee_param_types.as_ref().and_then(|ts| ts.get(i)) {
                        Some(expected) => {
                            borrow_state.resolve_typed(target, t, expected).unwrap_or(t)
                        }
                        None => t,
                    };
                    make_var(target, resolved)
                })
                .collect();
            // Lower `Operation::Unpack` for regular structs into a chain of
            // `let dest_i := Field { base = src_0, field_index = i }` — one per dest temp.
            // This keeps the IR free of `IRNode::Unpack` for non-enum structs, which
            // would otherwise claim to return a tuple of ALL fields (including synthetic
            // ghost fields like `dynamic_fields`) and silently corrupt Let patterns.
            // `Operation::UnpackVariant` keeps using `IRNode::Unpack` since it has real
            // runtime tag semantics that `Field` cannot express.
            if let Operation::Unpack(module_id, struct_id, _) = operation {
                let sid = builder.struct_id(module_id.qualified(*struct_id));
                let base = args[0].clone();
                let mut chain = IRNode::default();
                for (i, &dest) in dests.iter().enumerate() {
                    let field = IRNode::Field {
                        struct_id: sid,
                        field_index: i,
                        base: Box::new(base.clone()),
                    };
                    let let_node = make_let(target, &[dest], field);
                    chain = IRNode::assign(chain, let_node);
                }
                return chain;
            }
            let expr = translate_call(target, builder, borrow_state, operation, &args, srcs, dests);
            make_let(target, dests, expr)
        }

        Bytecode::Ret(_, temps) => {
            let values: Vec<IRNode> = temps.iter().map(|&t| make_var(target, t)).collect();
            if values.len() == 1 {
                values.into_iter().next().unwrap()
            } else {
                IRNode::Tuple(values)
            }
        }

        Bytecode::Abort(_, _)
        | Bytecode::Label(_, _)
        | Bytecode::Jump(_, _)
        | Bytecode::Branch(_, _, _, _)
        | Bytecode::VariantSwitch(_, _, _) => {
            panic!("Control flow bytecode in translate_one: {:?}", bytecode)
        }

        Bytecode::Nop(_) | Bytecode::Prop(_, _, _) | Bytecode::SaveMem(_, _, _) => {
            IRNode::default()
        }
    }
}

pub fn temp_id(target: &FunctionTarget, temp: usize) -> TempId {
    let symbol = target.get_local_name(temp);
    Rc::from(target.global_env().symbol_pool().string(symbol).as_str())
}

fn translate_call(
    target: &FunctionTarget,
    builder: &mut ProgramBuilder,
    borrow_state: &super::borrow_tracking::BorrowState,
    operation: &Operation,
    args: &[IRNode],
    src_temps: &[usize],
    dest_temps: &[usize],
) -> IRNode {
    match operation {
        // `Operation::Unpack` is handled in `translate_one` and never reaches here.
        Operation::UnpackVariant(module_id, struct_id, variant_id, _, _) => {
            let tag = builder
                .env()
                .get_module(*module_id)
                .into_enum(*struct_id)
                .get_variant(*variant_id)
                .get_tag();
            IRNode::Unpack {
                struct_id: builder.struct_id(module_id.qualified(*struct_id)),
                value: Box::new(args[0].clone()),
                variant_index: Some(tag),
            }
        }

        Operation::Pack(module_id, struct_id, type_args) => IRNode::Pack {
            struct_id: builder.struct_id(module_id.qualified(*struct_id)),
            type_args: type_args
                .iter()
                .map(|ty| builder.convert_type(ty))
                .collect(),
            fields: args.to_vec(),
            variant_index: None,
        },

        Operation::PackVariant(module_id, struct_id, variant_id, type_args) => {
            let tag = builder
                .env()
                .get_module(*module_id)
                .into_enum(*struct_id)
                .get_variant(*variant_id)
                .get_tag();
            let type_args = type_args
                .iter()
                .map(|ty| builder.convert_type(ty))
                .collect();
            IRNode::Pack {
                struct_id: builder.struct_id(module_id.qualified(*struct_id)),
                type_args,
                fields: args.to_vec(),
                variant_index: Some(tag),
            }
        }

        Operation::Function(module_id, fun_id, type_args) => {
            let qualified_id = module_id.qualified(*fun_id);

            // Extract all needed info before mutating builder
            let (func_name, module_name, is_zero_address, callee_type_param_count) = {
                let module_env = builder.env().get_module(*module_id);
                let func_env = module_env.get_function(*fun_id);
                let func_name = func_env
                    .get_name()
                    .display(builder.env().symbol_pool())
                    .to_string();
                let module_name = module_env
                    .get_name()
                    .display(builder.env().symbol_pool())
                    .to_string();
                let is_zero_address = module_env.self_address().iter().all(|val| *val == 0);
                let callee_type_param_count = func_env.get_type_parameters().len();
                (
                    func_name,
                    module_name,
                    is_zero_address,
                    callee_type_param_count,
                )
            };

            // Track spec intrinsic function IDs for later extraction
            let is_prover_module = module_name == "prover" && is_zero_address;
            if is_prover_module {
                let func_id = builder.function_id(qualified_id);
                if func_name == "requires" {
                    builder.program.requires_function_id = Some(func_id);
                } else if func_name == "ensures" {
                    builder.program.ensures_function_id = Some(func_id);
                } else if func_name == "asserts" {
                    builder.program.asserts_function_id = Some(func_id);
                }
            }

            let callee_type_param_count = callee_type_param_count;
            let declared_type_param_count = callee_type_param_count.min(type_args.len());
            let _extra_type_args = &type_args[declared_type_param_count..];

            // When type_args is empty but callee has type parameters, infer from caller.
            // This handles loop invariant functions where Move prover injects calls without type args.
            let ir_type_args: Vec<_> = if type_args.is_empty() && callee_type_param_count > 0 {
                let caller_type_param_count = target.func_env.get_type_parameter_count();
                (0..callee_type_param_count.min(caller_type_param_count))
                    .map(|i| intermediate_theorem_format::Type::TypeParameter(i as u16))
                    .collect()
            } else {
                type_args[..declared_type_param_count]
                    .iter()
                    .map(|ty| builder.convert_type(ty))
                    .collect()
            };

            let ir_args: Vec<_> = args.to_vec();

            IRNode::Call {
                function: builder.function_id(qualified_id),
                args: ir_args,
                type_args: ir_type_args,
            }
        }

        Operation::GetField(module_id, struct_id, _, field_idx) => IRNode::Field {
            struct_id: builder.struct_id(module_id.qualified(*struct_id)),
            field_index: *field_idx,
            base: Box::new(args[0].clone()),
        },

        Operation::BorrowField(module_id, struct_id, _, field_idx) => {
            let dest_type = target.get_local_type(dest_temps[0]);
            let struct_id_ir = builder.struct_id(module_id.qualified(*struct_id));
            if dest_type.is_mutable_reference() {
                translate_mutable_borrow_field(
                    target,
                    builder,
                    src_temps[0],
                    struct_id_ir,
                    *field_idx,
                )
            } else {
                IRNode::Field {
                    struct_id: struct_id_ir,
                    field_index: *field_idx,
                    base: Box::new(args[0].clone()),
                }
            }
        }

        Operation::BorrowLoc => {
            let dest_type = target.get_local_type(dest_temps[0]);
            if dest_type.is_mutable_reference() {
                let src_type = target.get_local_type(src_temps[0]);
                let state_type = builder.convert_type(&src_type);
                IRNode::MutableBorrow {
                    val_expr: Box::new(args[0].clone()),
                    reconstruct_param: Rc::from("__v"),
                    reconstruct_expr: Box::new(IRNode::Var(Rc::from("__v"))),
                    state_type,
                }
            } else {
                args[0].clone()
            }
        }

        Operation::BorrowGlobal(..) => args[0].clone(),

        Operation::ReadRef => {
            let src_type = target.get_local_type(src_temps[0]);
            if src_type.is_mutable_reference() {
                IRNode::ReadRef(Box::new(args[0].clone()))
            } else {
                args[0].clone()
            }
        }

        Operation::FreezeRef => {
            // FreezeRef converts &mut T to &T
            // In our functional model:
            // - &mut T is Mutable T s
            // - &T is just T (immutable refs are values)
            // So freezing a mutable ref requires extracting the value with ReadRef
            let src_type = target.get_local_type(src_temps[0]);
            if src_type.is_mutable_reference() {
                IRNode::ReadRef(Box::new(args[0].clone()))
            } else {
                args[0].clone()
            }
        }

        Operation::WriteRef => {
            assert_eq!(args.len(), 2, "BUG: WriteRef expects 2 sources");
            IRNode::WriteRef {
                reference: Box::new(args[0].clone()),
                value: Box::new(args[1].clone()),
            }
        }

        Operation::Add
        | Operation::Sub
        | Operation::Mul
        | Operation::Div
        | Operation::Mod
        | Operation::BitOr
        | Operation::BitAnd
        | Operation::Xor
        | Operation::Shl
        | Operation::Shr
        | Operation::Lt
        | Operation::Gt
        | Operation::Le
        | Operation::Ge
        | Operation::Or
        | Operation::And
        | Operation::Eq
        | Operation::Neq => {
            assert_eq!(
                args.len(),
                2,
                "BUG: Binary operation with {} operands",
                args.len()
            );
            IRNode::BinOp {
                op: convert_binop(operation),
                lhs: Box::new(args[0].clone()),
                rhs: Box::new(args[1].clone()),
            }
        }

        Operation::Not => {
            assert_eq!(
                args.len(),
                1,
                "BUG: Unary operation with {} operands",
                args.len()
            );
            IRNode::UnOp {
                op: UnOp::Not,
                operand: Box::new(args[0].clone()),
            }
        }

        Operation::CastU8
        | Operation::CastU16
        | Operation::CastU32
        | Operation::CastU64
        | Operation::CastU128
        | Operation::CastU256 => {
            assert_eq!(
                args.len(),
                1,
                "BUG: Cast operation with {} operands",
                args.len()
            );
            let op = match operation {
                Operation::CastU8 => UnOp::Cast(8),
                Operation::CastU16 => UnOp::Cast(16),
                Operation::CastU32 => UnOp::Cast(32),
                Operation::CastU64 => UnOp::Cast(64),
                Operation::CastU128 => UnOp::Cast(128),
                Operation::CastU256 => UnOp::Cast(256),
                _ => unreachable!(),
            };
            IRNode::UnOp {
                op,
                operand: Box::new(args[0].clone()),
            }
        }

        Operation::Destroy
        | Operation::TraceLocal(_)
        | Operation::TraceReturn(_)
        | Operation::TraceAbort
        | Operation::TraceExp(_, _)
        | Operation::TraceGlobalMem(_)
        | Operation::TraceGhost(_, _) => IRNode::default(),

        Operation::WriteBack(borrow_node, edge) => {
            // Write-back from child borrow to parent.
            // srcs[0] is the child temp being written back.
            // We return WriteBack directly — the caller wraps it in make_let with empty dests,
            // but we override the pattern to rebind the parent variable.
            assert!(!src_temps.is_empty(), "BUG: WriteBack has no source temp");
            let child = temp_id(target, src_temps[0]);
            let parent_idx = match borrow_node {
                BorrowNode::LocalRoot(idx) | BorrowNode::Reference(idx) => *idx,
                other => {
                    let func_name = target
                        .func_env
                        .get_name()
                        .display(target.func_env.symbol_pool())
                        .to_string();
                    eprintln!(
                        "WARNING: Dropped WriteBack in {}: child={}, borrow_node={:?}",
                        func_name, child, other
                    );
                    return IRNode::default();
                }
            };
            let parent = temp_id(target, parent_idx);
            let writeback_edge =
                translate_borrow_edge(target, builder, borrow_state, parent_idx, edge);
            IRNode::WriteBack {
                child,
                parent,
                edge: writeback_edge,
            }
        }

        Operation::Havoc(_) | Operation::Stop => IRNode::default(),

        // `IsParent` is a borrow-analysis predicate emitted by `MemoryInstrumentationProcessor`
        // (Move stackless bytecode) to check whether a temp's borrow is a parent of a given
        // node via a specific edge. Our IR collapses every borrow to a direct parent-of via
        // `MutableBorrow` / `WriteBack`, so this predicate is always true. Returning `Bool(true)`
        // keeps the destination temp well-typed for downstream `BinOp::And` chains; later
        // `inline_temps` + `logical_simplification` collapse the And to `true` and drop the
        // gating `If`. Returning `IRNode::default()` (unit) here would create
        // `Let { pattern: [$tN], value: () }` — malformed in Test mode where these temps are
        // consumed as `Bool` operands inside `.aborts` companions.
        Operation::IsParent(..) => IRNode::Const(intermediate_theorem_format::Const::Bool(true)),

        Operation::Quantifier(qtype, fun_id, type_args, lambda_index) => translate_quantifier(
            target,
            builder,
            src_temps,
            qtype,
            fun_id,
            type_args,
            *lambda_index,
        ),

        Operation::PackRef
        | Operation::UnpackRef
        | Operation::PackRefDeep
        | Operation::UnpackRefDeep
        | Operation::Uninit => IRNode::default(),

        Operation::GetGlobal(..)
        | Operation::MoveFrom(..)
        | Operation::MoveTo(..)
        | Operation::Exists(..) => {
            unreachable!("Global operations don't exist in modern Sui")
        }

        op => panic!("BUG: Unhandled operation {:?}", op),
    }
}

fn translate_mutable_borrow_field(
    target: &FunctionTarget,
    builder: &mut ProgramBuilder,
    src: usize,
    struct_id: intermediate_theorem_format::StructID,
    field_idx: usize,
) -> IRNode {
    let src_type = target.get_local_type(src);
    let inner_type = match &src_type {
        MoveType::Reference(_, inner) => inner.as_ref(),
        _ => &src_type,
    };
    let state_type = builder.convert_type(inner_type);
    let src_name = temp_id(target, src);

    IRNode::MutableBorrow {
        val_expr: Box::new(IRNode::Field {
            struct_id,
            field_index: field_idx,
            base: Box::new(make_var(target, src)),
        }),
        reconstruct_param: Rc::from("__v"),
        reconstruct_expr: Box::new(IRNode::UpdateField {
            base: Box::new(IRNode::Var(src_name)),
            struct_id,
            field_index: field_idx,
            value: Box::new(IRNode::Var(Rc::from("__v"))),
        }),
        state_type,
    }
}

/// Translate the upstream `BorrowEdge` carried on `Operation::WriteBack`
/// into the IR-level `WriteBackEdge` consumed by the renderer.
///
/// The cases we model right now:
///
/// * `Direct` (and any unrecognised shape): emit `WriteBackEdge::Direct`,
///   which preserves the legacy "`Mutable.set parent (Mutable.apply
///   child)` / `Mutable.apply child` / etc." rendering. Safe fallback.
///
/// * `Field(qid, field_index)`: emit `WriteBackEdge::Field { struct_id,
///   field_index }`. Renderer turns this into
///   `{ parent with <field> := Mutable.apply child }` (or `child` if
///   plain) — the field-update form.
///
/// * `Hyper([..., DynamicField(qid, _, _) | Field(qid, idx) at the head ])`:
///   pull the FIRST edge out and recurse on it. The dynamic-field case
///   collapses to `Field { struct_id: qid, field_index: <UID field of
///   that struct> }` — Sui convention pins the UID at field index 0
///   on `key`-having structs (e.g. `Reserve`, `Asset`). If the parent's
///   actual local type tells us a different UID position we use that
///   instead.
///
/// Other variants (`Index`, `EnumField`, plain `DynamicField`,
/// `Hyper` with an unrecognised head) currently fall back to `Direct`.
/// The fallback is conservative — Lean will surface the resulting type
/// mismatch so we can extend the match later.
fn translate_borrow_edge(
    target: &FunctionTarget,
    builder: &mut ProgramBuilder,
    borrow_state: &super::borrow_tracking::BorrowState,
    parent_idx: usize,
    edge: &BorrowEdge,
) -> WriteBackEdge {
    // We emit `WriteBackEdge::Field` only for the dynamic-field-on-object
    // pattern (`Hyper([DynamicField, Index])`). In that case the child
    // borrow's `Mutable.apply` returns the parent's *id* slot (a `UID`)
    // and the renderer needs to fold it into `parent.id` via a
    // record-update.
    //
    // Even within Hyper(DF, Index) we have to distinguish two shapes:
    //
    //  (a) Reserve / Asset family: `BorrowField(self, id) -> $tN` then
    //      `Function(Dynamic_field.borrow_mut, $tN, key) -> $tM`. The
    //      lean-level result is `Mutable<V, UID>` (state = UID). We need
    //      `{ self with id := Mutable.apply $tM }`.
    //
    //  (b) Bag.borrow_mut / Wit_table.borrow_mut family: the parent is
    //      passed *whole* to a wrapper function that internally composes
    //      its dynamic-field result back through `Mutable.mk (self.id) ...`.
    //      Lean-level result is `Mutable<V, Bag>` (state = parent type).
    //      `Mutable.apply $tM` already returns the parent type — a plain
    //      assignment is correct, NOT a field-update.
    //
    // The discriminator is per-block borrow tracking: in (a) the call's
    // first arg was substituted for a BorrowField-rooted child of the
    // parent slot, so `borrow_state.has_live_children(parent)` is true at
    // the WriteBack site. In (b) the parent was passed directly, no
    // BorrowField child was introduced.
    //
    // Plain `BorrowEdge::Field` cases (e.g. `let p := &mut self.field`)
    // stay on the `Direct` path: the IR's `MutableBorrow` already carries
    // a reconstruct closure that wraps back to the parent struct, so
    // `Mutable.apply` returns the parent type directly.
    match edge {
        BorrowEdge::Hyper(inner) => match inner.first() {
            Some(BorrowEdge::DynamicField(qid, _, _))
                if borrow_state.saw_borrow_field(parent_idx) =>
            {
                let struct_id = builder.struct_id(qid.module_id.qualified(qid.id));
                let field_index = find_uid_field_index(target, parent_idx).unwrap_or(0);
                WriteBackEdge::Field {
                    struct_id,
                    field_index,
                }
            }
            _ => WriteBackEdge::Direct,
        },
        BorrowEdge::Direct
        | BorrowEdge::Field(_, _)
        | BorrowEdge::EnumField(_, _, _)
        | BorrowEdge::Index(_)
        | BorrowEdge::DynamicField(_, _, _) => WriteBackEdge::Direct,
    }
}

/// Best-effort: walk `parent`'s declared local type and return the
/// field index of its `sui::object::UID` field, if any. Used by
/// `translate_borrow_edge` for the Hyper-with-DynamicField case to
/// reconstruct the implicit BorrowField from `parent` to `parent.id`.
/// Returns `None` if the parent isn't a struct or doesn't carry a UID
/// field — caller falls back to `0` (Sui convention) or `Direct`.
fn find_uid_field_index(target: &FunctionTarget, parent_idx: usize) -> Option<usize> {
    let parent_ty = target.get_local_type(parent_idx);
    let underlying = match parent_ty {
        MoveType::Reference(_, inner) => inner.as_ref(),
        other => other,
    };
    let (module_id, struct_id, _) = match underlying {
        MoveType::Datatype(m, s, args) => (*m, *s, args.clone()),
        _ => return None,
    };
    let env = target.func_env.module_env.env;
    let module_env = env.get_module(module_id);
    let struct_env = module_env.get_struct(struct_id);
    for (i, field) in struct_env.get_fields().enumerate() {
        let field_ty = field.get_type();
        if is_uid_type(&field_ty, env) {
            return Some(i);
        }
    }
    None
}

/// Detect `sui::object::UID` (the only `key`-bearing struct in Sui
/// framework). The qualified name is `0x2::object::UID`.
fn is_uid_type(ty: &MoveType, env: &move_model::model::GlobalEnv) -> bool {
    match ty {
        MoveType::Datatype(mid, sid, _) => {
            let module_env = env.get_module(*mid);
            let module_name = module_env.get_name();
            let module_str = env
                .symbol_pool()
                .string(module_name.name())
                .as_str()
                .to_owned();
            let struct_env = module_env.get_struct(*sid);
            let struct_str = env
                .symbol_pool()
                .string(struct_env.get_name())
                .as_str()
                .to_owned();
            module_str == "object" && struct_str == "UID"
        }
        _ => false,
    }
}

fn make_var(target: &FunctionTarget, temp: usize) -> IRNode {
    IRNode::Var(temp_id(target, temp))
}

fn make_constant(constant: &Constant) -> IRNode {
    IRNode::Const(convert_constant(constant))
}

fn make_let(target: &FunctionTarget, results: &[usize], value: IRNode) -> IRNode {
    IRNode::Let {
        pattern: results.iter().map(|&temp| temp_id(target, temp)).collect(),
        value: Box::new(value),
        body: Box::new(IRNode::unit()),
    }
}

fn translate_quantifier(
    target: &FunctionTarget,
    builder: &mut ProgramBuilder,
    srcs: &[usize],
    qtype: &QuantifierType,
    fun_id: &QualifiedId<FunId>,
    type_args: &[MoveType],
    lambda_index: usize,
) -> IRNode {
    let kind = match qtype {
        QuantifierType::Forall => QuantifierKind::Forall,
        QuantifierType::Exists => QuantifierKind::Exists,
        QuantifierType::Any => QuantifierKind::Any,
        QuantifierType::AnyRange => QuantifierKind::AnyRange,
        QuantifierType::All => QuantifierKind::All,
        QuantifierType::AllRange => QuantifierKind::AllRange,
        QuantifierType::Map => QuantifierKind::Map,
        QuantifierType::MapRange => QuantifierKind::MapRange,
        QuantifierType::RangeMap => QuantifierKind::RangeMap,
        QuantifierType::Filter => QuantifierKind::Filter,
        QuantifierType::FilterRange => QuantifierKind::FilterRange,
        QuantifierType::Find => QuantifierKind::Find,
        QuantifierType::FindRange => QuantifierKind::FindRange,
        QuantifierType::FindIndex => QuantifierKind::FindIndex,
        QuantifierType::FindIndexRange => QuantifierKind::FindIndexRange,
        QuantifierType::FindIndices => QuantifierKind::FindIndices,
        QuantifierType::FindIndicesRange => QuantifierKind::FindIndicesRange,
        QuantifierType::Count => QuantifierKind::Count,
        QuantifierType::CountRange => QuantifierKind::CountRange,
        QuantifierType::SumMap => QuantifierKind::SumMap,
        QuantifierType::SumMapRange => QuantifierKind::SumMapRange,
        QuantifierType::RangeCount => QuantifierKind::RangeCount,
        QuantifierType::RangeSumMap => QuantifierKind::RangeSumMap,
    };

    let is_vector_based = qtype.vector_based();
    let is_range_based = qtype.range_based();

    let skip_count = if is_vector_based {
        if is_range_based {
            3
        } else {
            1
        }
    } else {
        if is_range_based {
            2
        } else {
            0
        }
    };

    let collection = if is_vector_based {
        Some(Box::new(make_var(target, srcs[0])))
    } else {
        None
    };

    let range = if is_range_based {
        if is_vector_based {
            Some((
                Box::new(make_var(target, srcs[1])),
                Box::new(make_var(target, srcs[2])),
            ))
        } else {
            Some((
                Box::new(make_var(target, srcs[0])),
                Box::new(make_var(target, srcs[1])),
            ))
        }
    } else {
        None
    };

    let callback_srcs = &srcs[skip_count..];
    let lambda_param_name = temp_id(target, callback_srcs[lambda_index]);
    let lambda_type = builder.convert_type(target.get_local_type(callback_srcs[lambda_index]));

    let ir_type_args: Vec<_> = type_args
        .iter()
        .map(|ty| builder.convert_type(ty))
        .collect();

    let ir_args: Vec<IRNode> = callback_srcs
        .iter()
        .map(|&temp| make_var(target, temp))
        .collect();

    IRNode::Quantifier {
        kind,
        callback: Box::new(IRNode::Call {
            function: builder.function_id(*fun_id),
            type_args: ir_type_args,
            args: ir_args,
        }),
        lambda_param: lambda_param_name,
        lambda_type,
        collection,
        range,
    }
}
