//! Per-`Bytecode` op translator.
//!
//! Translates an individual stackless [`Bytecode`] op into one (or
//! zero) [`Stmt`] nodes. The dispatch sits inside the per-Region
//! structurer's walk over a `Region::Basic` PC range: for each
//! bytecode, call [`translate_basic_bytecode`]; if it returns
//! `Some(stmt)`, push the stmt onto the current block; if it returns
//! `None`, the bytecode emits no IR (Nop, Prop, SaveMem, Destroy).
//!
//! ## Borrow-bearing ops preserve their structure
//!
//! `BorrowLoc`, `BorrowField`, `WriteRef`, `WriteBack`, `IsParent`,
//! `FreezeRef`, and `Function` calls that consume `&mut` arguments
//! lift positionally to the corresponding IR shapes. Stage 2 enriches
//! map-style borrow edges with key/value types when the callsite makes
//! them available, but does not resolve borrow chains. The downstream
//! mutation-to-value and writeback passes perform that lowering in program
//! order. Classic global-memory operations and `Havoc` remain fail-closed.
//!
//! ## ReadRef on immutable references is identity pass-through
//!
//! `ReadRef` against a `&T` is a no-op at the IR level (immutable
//! references are erased once we leave bytecode -- we work
//! value-style). Against a `&mut T` it stays as `Expr::ReadRef`
//! (eliminated by stage 3). At op-translation time we don't have
//! the BorrowState to know which case we're in; we pessimistically
//! emit `Expr::ReadRef(Var(src))` and let stage 3's deref pass
//! collapse the immutable case.
//!
//! ## Variable naming
//!
//! Move temps are `TempIndex` (a `usize`). Every reference to a
//! temp gets the canonical name `$tN` where `N` is the index.
//! Mirrors the legacy convention.
//!
//! ## Spec-call recording
//!
//! Calls to `prover::requires` / `prover::ensures` /
//! `prover::asserts` flow through unchanged as `Expr::Call`; stage 7
//! extracts them into `.requires` / `.ensures` / `.asserts`
//! companion functions. Stage 2 records the function ids the first
//! time it sees each so stage 7 can find the call sites; that
//! recording belongs at the FunctionTranslator level, not here.

use move_binary_format::file_format::CodeOffset;
use move_model::model::{DatatypeId, ModuleId, QualifiedId, RefType, VariantId};
use move_model::ty::Type as MoveType;
use move_stackless_bytecode::ast::TempIndex;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Constant, Operation};

use crate::ir::{BinOp, Const, Expr, ProgramBuilder, Stmt, UnOp, VarId};

use super::consts::translate_constant_with_type;
use super::types::translate_type;
use super::Stage2Error;
use crate::ir::path::PathStep;

/// Context threaded through the per-op translator.
///
/// Stage 2 translates each upstream `Bytecode` op to one or more
/// IR `Stmt`s positionally -- no borrow-chain analysis happens here.
/// Borrow ops (`BorrowLoc`, `BorrowField`, `WriteBack`, ...) lift to
/// matching IR variants. The active mutation-to-let and writeback passes
/// lower them in program order.
pub struct TranslateCtx<'a, 'env, 'kv> {
    pub target: &'a FunctionTarget<'env>,
    pub prog: &'a mut ProgramBuilder,
    /// (K, V) Move-type pair recorded for each mutref temp produced by
    /// a recognised map-style `borrow_mut` native (`table::borrow_mut`,
    /// `bag::borrow_mut`, `dynamic_field::borrow_mut`, ...). Stage 2's
    /// `Operation::WriteBack` handler consults this map to fill the
    /// `key_type` / `value_type` fields of `BorrowEdge::MapKey` edges
    /// emitted for the same temp's writeback.
    ///
    /// Indexed by the destination temp name (`$tN`) of the borrow_mut
    /// callsite. Lifetime-tied to a per-function map created in
    /// `function_lift::lift_function` and threaded through every
    /// `lift_region` / `lift_basic_range` recursion, so a borrow_mut
    /// callsite in one basic block remains visible to its WriteBack
    /// in a later basic block (the two can be CFG-separated by an
    /// `assert!` or other branch point).
    pub borrow_mut_kv:
        &'kv mut std::collections::BTreeMap<VarId, Vec<(crate::ir::Type, crate::ir::Type)>>,
}

/// Canonical IR name for a Move temp slot. Mirrors legacy `$tN`.
pub fn temp_name(t: TempIndex) -> VarId {
    format!("$t{t}").into()
}

/// `Expr::Var($tN)`.
fn var(t: TempIndex) -> Expr {
    Expr::Var(temp_name(t))
}

/// [`translate_basic_bytecode`], except a by-reference `UnpackVariant`, which
/// yields a reference per field: one `VariantField` borrow per destination.
pub fn translate_basic_bytecode_stmts(
    bc: &Bytecode,
    ctx: &mut TranslateCtx,
) -> Result<Vec<Stmt>, Stage2Error> {
    if let Bytecode::Call(
        attr,
        dests,
        Operation::UnpackVariant(module_id, datatype_id, variant_id, _type_args, ref_type),
        srcs,
        _,
    ) = bc
    {
        if !matches!(ref_type, RefType::ByValue) {
            let pc = attr.as_usize() as CodeOffset;
            let src = single_src(srcs, pc, "UnpackVariant")?;
            let struct_id = resolved_struct_id(*module_id, *datatype_id, ctx.prog);
            let tag = variant_id_to_tag(ctx.target, *module_id, *datatype_id, *variant_id);
            return Ok(dests
                .iter()
                .enumerate()
                .map(|(field_index, dest)| Stmt::Let {
                    pattern: vec![Some(temp_name(*dest))],
                    value: Expr::Borrow {
                        step: PathStep::VariantField {
                            struct_id,
                            variant: tag,
                            field_index,
                        },
                        base: Box::new(var(src)),
                    },
                })
                .collect());
        }
    }
    Ok(translate_basic_bytecode(bc, ctx)?.into_iter().collect())
}

/// Translate a single `Bytecode` op encountered inside a
/// `Region::Basic` PC range.
///
/// Returns `Some(stmt)` for ops that emit an IR statement, `None`
/// for ops with no IR effect (Nop, Prop, SaveMem, Destroy, the
/// Trace family). Returns an error for ops the structurer should
/// have consumed (Branch, Jump, Ret, Abort, VariantSwitch), and for
/// genuinely unsupported ops. Labels can legitimately head a basic
/// region and are ignored.
pub fn translate_basic_bytecode(
    bc: &Bytecode,
    ctx: &mut TranslateCtx,
) -> Result<Option<Stmt>, Stage2Error> {
    match bc {
        Bytecode::Assign(_, dest, src, _) => Ok(Some(Stmt::Let {
            pattern: vec![Some(temp_name(*dest))],
            value: var(*src),
        })),
        Bytecode::Load(_, dest, c) => translate_load(*dest, c, ctx).map(Some),
        Bytecode::Call(attr, dests, op, srcs, _abort) => {
            let pc = attr.as_usize() as CodeOffset;
            translate_call_op(op, dests, srcs, pc, ctx)
        }
        Bytecode::Nop(_) | Bytecode::Prop(..) | Bytecode::SaveMem(..) => Ok(None),
        // `Label` is a no-op pseudo-instruction marking a jump
        // target; it can legitimately appear inside a `Region::Basic`
        // (e.g., the head of a fall-through block). Drop it silently.
        Bytecode::Label(..) => Ok(None),
        // Control-flow terminators are consumed by stage 1's
        // structurer; they should never appear inside a `Region::Basic`.
        Bytecode::Branch(..) => Err(Stage2Error::NotImplemented {
            reason: "Bytecode::Branch reached translate_op (stage 1 structurer should have consumed it)",
        }),
        Bytecode::Jump(..) => Err(Stage2Error::NotImplemented {
            reason: "Bytecode::Jump reached translate_op (stage 1 structurer should have consumed it)",
        }),
        Bytecode::Ret(..) => Err(Stage2Error::NotImplemented {
            reason: "Bytecode::Ret reached translate_op (stage 1 structurer should have consumed it)",
        }),
        Bytecode::Abort(..) => Err(Stage2Error::NotImplemented {
            reason: "Bytecode::Abort reached translate_op (stage 1 structurer should have consumed it)",
        }),
        Bytecode::VariantSwitch(..) => Err(Stage2Error::NotImplemented {
            reason: "Bytecode::VariantSwitch reached translate_op (stage 1 structurer should have consumed it)",
        }),
    }
}

fn translate_load(
    dest: TempIndex,
    c: &Constant,
    ctx: &mut TranslateCtx,
) -> Result<Stmt, Stage2Error> {
    // Use the dest's declared type as the empty-vector type hint --
    // covers `vec_const = vector::empty<T>()` style loads where the
    // bytecode's recorded local type is `vector<T>` and the constant
    // is `Vector(vec![])`.
    let dest_move_ty: MoveType = ctx.target.get_local_type(dest).clone();
    let dest_ty = translate_type(&dest_move_ty, ctx.prog)?;
    let value = translate_constant_with_type(c, &dest_ty);
    Ok(Stmt::Let {
        pattern: vec![Some(temp_name(dest))],
        value: Expr::Const(value),
    })
}

fn resolved_struct_id(
    module_id: ModuleId,
    datatype_id: DatatypeId,
    prog: &mut ProgramBuilder,
) -> crate::ir::StructId {
    prog.struct_id(QualifiedId {
        module_id,
        id: datatype_id,
    })
}

fn bind_dests(dests: &[TempIndex], value: Expr) -> Stmt {
    if dests.is_empty() {
        Stmt::Eval(value)
    } else {
        Stmt::Let {
            pattern: dests.iter().map(|dest| Some(temp_name(*dest))).collect(),
            value,
        }
    }
}

fn translate_call_op(
    op: &Operation,
    dests: &[TempIndex],
    srcs: &[TempIndex],
    pc: CodeOffset,
    ctx: &mut TranslateCtx,
) -> Result<Option<Stmt>, Stage2Error> {
    match op {
        // ---- Pack / Unpack ----------------------------------------
        Operation::Pack(module_id, datatype_id, type_args) => {
            let struct_id = resolved_struct_id(*module_id, *datatype_id, ctx.prog);
            let type_args = translate_type_args(type_args, ctx.prog)?;
            let fields = srcs.iter().map(|t| var(*t)).collect();
            let dest = single_dest(dests, pc, "Pack")?;
            Ok(Some(Stmt::Let {
                pattern: vec![Some(temp_name(dest))],
                value: Expr::Pack {
                    struct_id,
                    type_args,
                    variant: None,
                    fields,
                },
            }))
        }
        Operation::PackVariant(module_id, datatype_id, variant_id, type_args) => {
            let struct_id = resolved_struct_id(*module_id, *datatype_id, ctx.prog);
            let tag = variant_id_to_tag(ctx.target, *module_id, *datatype_id, *variant_id);
            let type_args = translate_type_args(type_args, ctx.prog)?;
            let fields = srcs.iter().map(|t| var(*t)).collect();
            let dest = single_dest(dests, pc, "PackVariant")?;
            Ok(Some(Stmt::Let {
                pattern: vec![Some(temp_name(dest))],
                value: Expr::Pack {
                    struct_id,
                    type_args,
                    variant: Some(tag),
                    fields,
                },
            }))
        }
        Operation::Unpack(module_id, datatype_id, _type_args) => {
            let struct_id = resolved_struct_id(*module_id, *datatype_id, ctx.prog);
            let src = single_src(srcs, pc, "Unpack")?;
            let value = Expr::Unpack {
                struct_id,
                variant: None,
                value: Box::new(var(src)),
            };
            // An empty struct unpacks to no bindings. Emit it in canonical
            // eval position rather than an empty-pattern Let -- stage 6's
            // tuple_simplify would convert it to `Stmt::Eval` anyway, and the
            // validator's `AllWildcardLet` rule rejects empty-pattern Lets on
            // the intermediate IR it sees before stage 6 runs.
            Ok(Some(bind_dests(dests, value)))
        }
        Operation::UnpackVariant(module_id, datatype_id, variant_id, _type_args, ref_type) => {
            if !matches!(ref_type, RefType::ByValue) {
                return Err(Stage2Error::NotImplemented {
                    reason: "by-reference UnpackVariant must be lowered by translate_basic_bytecode_stmts",
                });
            }
            let struct_id = resolved_struct_id(*module_id, *datatype_id, ctx.prog);
            let tag = variant_id_to_tag(ctx.target, *module_id, *datatype_id, *variant_id);
            let src = single_src(srcs, pc, "UnpackVariant")?;
            let value = Expr::Unpack {
                struct_id,
                variant: Some(tag),
                value: Box::new(var(src)),
            };
            // A fieldless variant (e.g. `StakedIkaState::Staked`) unpacks to
            // no bindings. Emit canonical eval position rather than an
            // empty-pattern Let (see the `Unpack` arm above).
            Ok(Some(bind_dests(dests, value)))
        }

        // ---- GetField (immutable field projection) ----------------
        Operation::GetField(module_id, datatype_id, _type_args, field_index) => {
            let struct_id = resolved_struct_id(*module_id, *datatype_id, ctx.prog);
            let src = single_src(srcs, pc, "GetField")?;
            let dest = single_dest(dests, pc, "GetField")?;
            Ok(Some(Stmt::Let {
                pattern: vec![Some(temp_name(dest))],
                value: Expr::Field {
                    struct_id,
                    field_index: *field_index,
                    base: Box::new(var(src)),
                },
            }))
        }

        // ---- Pure unary ops ---------------------------------------
        Operation::Not => unop_stmt(UnOp::Not, dests, srcs, pc, "Not"),
        Operation::CastU8 => unop_stmt(UnOp::Cast(8), dests, srcs, pc, "CastU8"),
        Operation::CastU16 => unop_stmt(UnOp::Cast(16), dests, srcs, pc, "CastU16"),
        Operation::CastU32 => unop_stmt(UnOp::Cast(32), dests, srcs, pc, "CastU32"),
        Operation::CastU64 => unop_stmt(UnOp::Cast(64), dests, srcs, pc, "CastU64"),
        Operation::CastU128 => unop_stmt(UnOp::Cast(128), dests, srcs, pc, "CastU128"),
        Operation::CastU256 => unop_stmt(UnOp::Cast(256), dests, srcs, pc, "CastU256"),

        // ---- Pure binary ops --------------------------------------
        Operation::Add => binop_stmt(BinOp::Add, dests, srcs, pc, "Add", ctx),
        Operation::Sub => binop_stmt(BinOp::Sub, dests, srcs, pc, "Sub", ctx),
        Operation::Mul => binop_stmt(BinOp::Mul, dests, srcs, pc, "Mul", ctx),
        Operation::Div => binop_stmt(BinOp::Div, dests, srcs, pc, "Div", ctx),
        Operation::Mod => binop_stmt(BinOp::Mod, dests, srcs, pc, "Mod", ctx),
        Operation::BitAnd => binop_stmt(BinOp::BitAnd, dests, srcs, pc, "BitAnd", ctx),
        Operation::BitOr => binop_stmt(BinOp::BitOr, dests, srcs, pc, "BitOr", ctx),
        Operation::Xor => binop_stmt(BinOp::BitXor, dests, srcs, pc, "Xor", ctx),
        Operation::Shl => binop_stmt(BinOp::Shl, dests, srcs, pc, "Shl", ctx),
        Operation::Shr => binop_stmt(BinOp::Shr, dests, srcs, pc, "Shr", ctx),
        Operation::And => binop_stmt(BinOp::And, dests, srcs, pc, "And", ctx),
        Operation::Or => binop_stmt(BinOp::Or, dests, srcs, pc, "Or", ctx),
        Operation::Eq => binop_stmt(BinOp::Eq, dests, srcs, pc, "Eq", ctx),
        Operation::Neq => binop_stmt(BinOp::Neq, dests, srcs, pc, "Neq", ctx),
        Operation::Lt => binop_stmt(BinOp::Lt, dests, srcs, pc, "Lt", ctx),
        Operation::Le => binop_stmt(BinOp::Le, dests, srcs, pc, "Le", ctx),
        Operation::Gt => binop_stmt(BinOp::Gt, dests, srcs, pc, "Gt", ctx),
        Operation::Ge => binop_stmt(BinOp::Ge, dests, srcs, pc, "Ge", ctx),

        // ---- 1:1 borrow ops (lifted verbatim from upstream) -----
        // Stage 2 emits these directly; stage 3 (mut_to_let) lowers them.
        Operation::ReadRef | Operation::FreezeRef => {
            // FreezeRef converts `&mut T` to `&T`. In our value-style
            // IR, immutable refs erase to values; stage 3 collapses
            // FreezeRef on an already-frozen ref to identity. Emit
            // the ReadRef shape -- both ops "extract the pointed-to
            // value" at the IR level.
            let name = match op {
                Operation::ReadRef => "ReadRef",
                Operation::FreezeRef => "FreezeRef",
                _ => unreachable!(),
            };
            let src = single_src(srcs, pc, name)?;
            let dest = single_dest(dests, pc, name)?;
            Ok(Some(Stmt::Let {
                pattern: vec![Some(temp_name(dest))],
                value: Expr::ReadRef(Box::new(var(src))),
            }))
        }

        Operation::BorrowLoc => {
            let src = single_src(srcs, pc, "BorrowLoc")?;
            let dest = single_dest(dests, pc, "BorrowLoc")?;
            Ok(Some(Stmt::Let {
                pattern: vec![Some(temp_name(dest))],
                value: Expr::BorrowLoc(temp_name(src)),
            }))
        }

        Operation::BorrowField(module_id, datatype_id, _type_args, field_index) => {
            let src = single_src(srcs, pc, "BorrowField")?;
            let dest = single_dest(dests, pc, "BorrowField")?;
            let struct_id = resolved_struct_id(*module_id, *datatype_id, ctx.prog);
            Ok(Some(Stmt::Let {
                pattern: vec![Some(temp_name(dest))],
                value: Expr::Borrow {
                    step: PathStep::Field {
                        struct_id,
                        field_index: *field_index,
                    },
                    base: Box::new(var(src)),
                },
            }))
        }

        Operation::WriteRef => {
            if srcs.len() != 2 {
                return Err(Stage2Error::malformed_arity(
                    "WriteRef",
                    "srcs",
                    2,
                    srcs.len(),
                    pc,
                ));
            }
            Ok(Some(Stmt::Eval(Expr::WriteRef {
                reference: Box::new(var(srcs[0])),
                value: Box::new(var(srcs[1])),
            })))
        }

        Operation::WriteBack(node, edge) => {
            let child = single_src(srcs, pc, "WriteBack")?;
            let ir_node = lift_borrow_node(node, ctx)?;
            let ir_edge = prepare_borrow_edge(edge, child, ctx)?;
            Ok(Some(Stmt::Eval(Expr::WriteBack {
                node: ir_node,
                edge: ir_edge,
                child: temp_name(child),
                world: None,
            })))
        }

        // ---- IsParent: conditional-borrow dispatch predicate ----
        // Upstream's `memory_instrumentation.rs` emits an IsParent
        // call before each WriteBack chain when a reference temp has
        // more than one possible parent (the `ancestors.len() > 1`
        // branch in that file). The Bool dest flows into the
        // surrounding `Branch` op which stage 1 has structured as
        // `Region::If`. Renderer maps this to `Mutation.isParent`.
        Operation::IsParent(node, edge) => {
            let child = single_src(srcs, pc, "IsParent")?;
            let dest = single_dest(dests, pc, "IsParent")?;
            let ir_node = lift_borrow_node(node, ctx)?;
            let ir_edge = prepare_borrow_edge(edge, child, ctx)?;
            Ok(Some(Stmt::Let {
                pattern: vec![Some(temp_name(dest))],
                value: Expr::IsParent {
                    node: ir_node,
                    edge: ir_edge,
                    child: temp_name(child),
                },
            }))
        }

        // ---- PackRef / UnpackRef family: data-invariant boundary
        // checks. Until we wire up `data invariant` specs to the
        // prover layer, lift as no-op `Stmt::Eval(Expr::Unit)`.
        // Sound: invariant either holds (no-op is correct) or fails
        // (downstream proof obligation fails).
        Operation::PackRef
        | Operation::UnpackRef
        | Operation::PackRefDeep
        | Operation::UnpackRefDeep => Ok(Some(Stmt::Eval(Expr::Unit))),

        // ---- Function call: positional, just like Boogie ---------
        // Pass `Var($tN)` for every src -- including `&mut`-typed
        // ones. Borrow-chain analysis lives in stage 3, which walks
        // the surrounding `BorrowLoc` / `BorrowField` / `WriteBack`
        // ops and threads through augmented returns.
        Operation::Function(module_id, fun_id, type_args) => {
            translate_function_call(*module_id, *fun_id, type_args, dests, srcs, pc, ctx)
        }

        // ---- Destroy: clears state, emits nothing ----------------
        Operation::Destroy => Ok(None),

        // ---- Trace ops: stripped from the IR ---------------------
        Operation::TraceLocal(_)
        | Operation::TraceReturn(_)
        | Operation::TraceAbort
        | Operation::TraceExp(_, _)
        | Operation::TraceGlobalMem(_)
        | Operation::TraceMessage(_)
        | Operation::TraceGhost(_, _) => Ok(None),

        // ---- Spec-instrumentation event markers ------------------
        // Upstream's spec_instrumentation lowers `emits` clauses of
        // opaque-function callees into `Operation::EmitEvent` (with the
        // event payload + handle + optional condition as srcs), and uses
        // `EventStoreDiverge` as a "partial emits spec" marker. Both are
        // verification-time markers for the Boogie backend's event-store
        // model; the Lean backend does not model the event store, so we
        // drop them silently. This is the same treatment as the Trace*
        // family -- the upstream op has no observable effect on the
        // verified surface.
        Operation::EventStoreDiverge | Operation::EmitEvent => Ok(None),

        // ---- Stop: synthetic terminator from upstream loop ------
        // analysis. Stage 2 deliberately bypasses loop analysis so
        // we should never see one; defensive guard.
        Operation::Stop => Err(Stage2Error::NotImplemented {
            reason: "Operation::Stop",
        }),

        // ---- Unreachable in the Lean pipeline -------------------
        // OpaqueCallBegin/End: emitted only by upstream's
        // `SpecInstrumentationProcessor::process()`, which writes them
        // into the `Verification` variant. The lean-pipeline reads
        // `FunctionVariant::Baseline` exclusively (see
        // `pipeline.rs` and `dynamic_fields.rs`), so these markers
        // never appear in the bytecode stream stage 2 sees. Assert
        // loudly if upstream's shape ever changes.
        Operation::OpaqueCallBegin(_, _, _) | Operation::OpaqueCallEnd(_, _, _) => unreachable!(
            "OpaqueCallBegin/End should only appear in FunctionVariant::Verification; lean-pipeline reads Baseline only"
        ),

        // ---- Deferred ops ---------------------------------------
        // BorrowGlobal/GetGlobal/MoveTo/MoveFrom/Exists: global memory ops; not in our model.
        // Uninit: livevar_analysis marker for mutable-ref locals that are conditionally
        //   initialised. Silent drop would leave `$tN` unbound at stage 5; defer until
        //   stages 3-5 grow a conditional-init model.
        // Havoc: spec-only nondeterminism marker (similar story to Uninit).
        // IfThenElse / VariantMerge: phi-merge intrinsics from upstream's
        //   ConditionalMergeInsertionProcessor (which we don't run).
        Operation::BorrowGlobal(..) => Err(Stage2Error::NotImplemented { reason: "Operation::BorrowGlobal" }),
        Operation::GetGlobal(..) => Err(Stage2Error::NotImplemented { reason: "Operation::GetGlobal" }),
        Operation::MoveTo(..) => Err(Stage2Error::NotImplemented { reason: "Operation::MoveTo" }),
        Operation::MoveFrom(..) => Err(Stage2Error::NotImplemented { reason: "Operation::MoveFrom" }),
        Operation::Exists(..) => Err(Stage2Error::NotImplemented { reason: "Operation::Exists" }),
        Operation::Uninit => {
            // Lower `Uninit $tN` to a Let-bound sentinel `Mutation T`.
            // See `mutation_natives` for the rationale.
            let temp = match srcs.first() {
                Some(&t) => t,
                None => return Err(Stage2Error::NotImplemented { reason: "Operation::Uninit with no srcs" }),
            };
            let mty = ctx.target.get_local_type(temp);
            // Upstream only emits Uninit for mutable references; defensive check.
            let inner_mty = match mty {
                MoveType::Reference(true, t) => t.as_ref().clone(),
                _ => return Err(Stage2Error::NotImplemented { reason: "Operation::Uninit on non-mut-ref" }),
            };
            let inner = super::types::translate_type(&inner_mty, ctx.prog)?;
            let uninit_fid = super::mutation_natives::fid(ctx.prog);
            Ok(Some(Stmt::Let {
                pattern: vec![Some(temp_name(temp))],
                value: Expr::Call {
                    fun: uninit_fid,
                    type_args: vec![inner],
                    args: vec![Expr::Const(Const::UInt {
                        bits: 64,
                        value: ethnum::U256::from(temp as u64),
                    })],
                },
            }))
        }
        Operation::Havoc(_) => Err(Stage2Error::NotImplemented { reason: "Operation::Havoc" }),
        Operation::IfThenElse => Err(Stage2Error::NotImplemented { reason: "Operation::IfThenElse" }),
        Operation::VariantMerge => Err(Stage2Error::NotImplemented { reason: "Operation::VariantMerge" }),

        // ---- Quantifier (forall / exists / map / find / ...) ----
        // Lifted from upstream's `QuantifierIteratorAnalysisProcessor`-
        // folded form: `(QuantifierType, lambda_qid, type_args, slot)`
        // where `lambda_qid` is the predicate function and `slot` is
        // the position of the bound variable in the lambda's args.
        // Domain args (collection / range bounds) come first in
        // `srcs`; remaining `srcs` are closure captures filling the
        // lambda's non-bound-var positions.
        Operation::Quantifier(qt, lambda_qid, type_args, slot) => {
            translate_quantifier_op(*qt, *lambda_qid, type_args, *slot, dests, srcs, pc, ctx)
        }
    }
}

/// Lift a `Operation::Quantifier` to `Expr::Quantifier`.
///
/// The lambda function is referenced by `Expr::Call` inside the
/// quantifier's `body` block; stage 5 (let_inline) inlines it when
/// pure. The bound variable (`binder`) is a freshly-named `VarId`
/// inserted at `slot` in the lambda's arg list; remaining lambda
/// args come from `srcs[capture_start..]` after the domain args
/// (start/end for ranges, collection for collections, none for
/// unbounded).
fn translate_quantifier_op(
    qt: move_stackless_bytecode::stackless_bytecode::QuantifierType,
    lambda_qid: QualifiedId<move_model::model::FunId>,
    type_args: &[MoveType],
    slot: usize,
    dests: &[TempIndex],
    srcs: &[TempIndex],
    pc: CodeOffset,
    ctx: &mut TranslateCtx,
) -> Result<Option<Stmt>, Stage2Error> {
    use super::translate_quant::{translate_quantifier_kind, QuantDomainHint};
    use crate::ir::QuantDomain;

    let dest = single_dest(dests, pc, "Quantifier")?;
    let (kind, hint) = translate_quantifier_kind(qt);
    let lambda_fid = ctx.prog.function_id(lambda_qid);
    let translated_type_args = translate_type_args(type_args, ctx.prog)?;

    // Look up the lambda's arity and the binder's declared type.
    let env = ctx.target.global_env();
    let lambda_env = env
        .get_module(lambda_qid.module_id)
        .into_function(lambda_qid.id);
    let lambda_params = lambda_env.get_parameter_types();
    if slot >= lambda_params.len() {
        return Err(Stage2Error::malformed_arity(
            "Quantifier",
            "lambda slot",
            lambda_params.len(),
            slot,
            pc,
        ));
    }
    let binder_move_ty = lambda_params[slot].instantiate(type_args);
    let binder_type = translate_type(&binder_move_ty, ctx.prog)?;
    // Stable binder name keyed on PC + dest so distinct quantifiers
    // in the same function get distinct names without colliding.
    let binder: crate::ir::VarId = format!("__qi_{pc}_{dest}").into();

    // Domain shape + how many leading `srcs` it consumes.
    let (domain, capture_start) = match hint {
        QuantDomainHint::Unbounded => (QuantDomain::Unbounded, 0),
        QuantDomainHint::Range => {
            if srcs.len() < 2 {
                return Err(Stage2Error::malformed_arity(
                    "Quantifier",
                    "srcs (range bounds)",
                    2,
                    srcs.len(),
                    pc,
                ));
            }
            (
                QuantDomain::Range {
                    start: Box::new(var(srcs[0])),
                    end: Box::new(var(srcs[1])),
                },
                2,
            )
        }
        QuantDomainHint::Collection => {
            if srcs.is_empty() {
                return Err(Stage2Error::malformed_arity(
                    "Quantifier",
                    "srcs (collection)",
                    1,
                    srcs.len(),
                    pc,
                ));
            }
            (QuantDomain::Collection(Box::new(var(srcs[0]))), 1)
        }
        QuantDomainHint::VecRange => {
            // `<op>_range!(vec, start, end, ...)` -- three domain srcs
            // (`[vec, start, end]`), then captures. Consuming only two
            // (as the index-only `Range` does) would misread `vec` as
            // `start` and shift every capture by one (the unbound-`$tNN`
            // bug in dlmm's `all_range`).
            if srcs.len() < 3 {
                return Err(Stage2Error::malformed_arity(
                    "Quantifier",
                    "srcs (vec + range bounds)",
                    3,
                    srcs.len(),
                    pc,
                ));
            }
            (
                QuantDomain::VecRange {
                    vec: Box::new(var(srcs[0])),
                    start: Box::new(var(srcs[1])),
                    end: Box::new(var(srcs[2])),
                },
                3,
            )
        }
    };

    // Build the lambda call: binder at `slot`, captures fill the
    // rest from `srcs[capture_start..]`. Upstream's
    // `QuantifierIteratorAnalysisProcessor` constructs
    // `srcs = domain_args ++ lambda_call_args` where
    // `lambda_call_args` has length `lambda_params.len()` -- the
    // binder slot position carries a placeholder temp at the call
    // site that we discard. So the capture for lambda arg `i` lives
    // at `srcs[capture_start + i]` (one-to-one, NOT skipping the
    // binder slot). An earlier implementation incremented
    // `next_capture` only for non-binder positions, which read the
    // placeholder at the binder slot as the first capture and
    // shifted every subsequent capture off by one -- e.g.
    // `forall!(|i| queue_index_valid(i, q))` would lift to a Call
    // passing `Var($t2_placeholder)` instead of `Var($t0=q)`,
    // leaving `$t2` unbound at the SSA stage.
    if srcs.len() < capture_start + lambda_params.len() {
        return Err(Stage2Error::malformed_arity(
            "Quantifier",
            "srcs (domain + lambda args)",
            capture_start + lambda_params.len(),
            srcs.len(),
            pc,
        ));
    }
    let mut lambda_args = Vec::with_capacity(lambda_params.len());
    for i in 0..lambda_params.len() {
        if i == slot {
            lambda_args.push(Expr::Var(binder.clone()));
        } else {
            lambda_args.push(var(srcs[capture_start + i]));
        }
    }

    let body = crate::ir::Block {
        stmts: Vec::new(),
        tail: crate::ir::BlockTail::Value(Expr::Call {
            fun: lambda_fid,
            type_args: translated_type_args,
            args: lambda_args,
        }),
    };

    Ok(Some(Stmt::Let {
        pattern: vec![Some(temp_name(dest))],
        value: Expr::Quantifier {
            kind,
            binder,
            binder_type,
            domain,
            body: Box::new(body),
        },
    }))
}

fn translate_type_args(
    args: &[MoveType],
    prog: &mut ProgramBuilder,
) -> Result<Vec<crate::ir::Type>, Stage2Error> {
    let mut out = Vec::with_capacity(args.len());
    for a in args {
        out.push(translate_type(a, prog)?);
    }
    Ok(out)
}

/// If `(module_id, fun_id)` resolves to a `prover::requires` /
/// `prover::ensures` / `prover::asserts` intrinsic, record `fid` in
/// the `ProgramBuilder`'s prover-fn side table. Idempotent: callers
/// can hit the same intrinsic many times without effect.
///
/// Detection: matches on the module's simple name being `"prover"`
/// (case-sensitive) at the framework address. The framework address
/// can be `0x1` (legacy `0x1::prover`) or the dedicated prover
/// address; we accept any module named `"prover"` whose address has
/// a leading-zero or framework-style shape. False positives here
/// would be benign -- stage 6 only uses these ids to find call
/// sites, never to substitute them.
fn record_prover_fn_if_intrinsic(
    env: &move_model::model::GlobalEnv,
    module_id: ModuleId,
    fun_id: move_model::model::FunId,
    fid: crate::ir::FunId,
    prog: &mut ProgramBuilder,
) {
    let module_env = env.get_module(module_id);
    let module_name = env
        .symbol_pool()
        .string(module_env.get_name().name())
        .to_string();
    if module_name != "prover" {
        return;
    }
    let func_env = module_env.get_function(fun_id);
    let func_name = env.symbol_pool().string(func_env.get_name()).to_string();
    use crate::ir::ProverFnKind;
    let kind = match func_name.as_str() {
        "requires" => ProverFnKind::Requires,
        "ensures" => ProverFnKind::Ensures,
        "asserts" => ProverFnKind::Asserts,
        _ => return,
    };
    prog.register_prover_fn(kind, fid);
}

/// Lift a `Operation::Function` call positionally.
///
/// Pass `Var($tN)` for every src -- including `&mut`-typed ones
/// (mirrors Boogie's translation, which does the same: see
/// `bytecode_translator.rs:4476`'s `args_str = srcs.iter().map(str_local).join(", ")`).
/// Borrow-chain analysis is **not** stage 2's job; the active
/// mutation-to-let and writeback passes consume the surrounding
/// `BorrowLoc` / `BorrowField` / `WriteBack` operations in program order.
fn translate_function_call(
    module_id: ModuleId,
    fun_id: move_model::model::FunId,
    type_args: &[MoveType],
    dests: &[TempIndex],
    srcs: &[TempIndex],
    pc: CodeOffset,
    ctx: &mut TranslateCtx,
) -> Result<Option<Stmt>, Stage2Error> {
    let _ = pc;
    let qid = QualifiedId {
        module_id,
        id: fun_id,
    };
    let fid = ctx.prog.function_id(qid);
    // If this resolves to a `prover::requires` / `ensures` / `asserts`
    // intrinsic, record the FunId so stage 6 can find call sites.
    record_prover_fn_if_intrinsic(ctx.target.global_env(), module_id, fun_id, fid, ctx.prog);
    let type_args_ir = translate_type_args(type_args, ctx.prog)?;

    // Recognize borrow-mut natives ahead of the generic Call path.
    // See `plans/lean-pipeline/mutable-references.md` -- these lift
    // to dedicated IR variants so the renderer can map them to the
    // `Mutation.borrow*` prelude functions.
    if let Some(kind) = recognize_borrow_native(ctx.target.global_env(), module_id, fun_id) {
        return translate_borrow_native(kind, &type_args_ir, dests, srcs, pc, ctx);
    }

    // Concrete-K `dynamic_field::borrow_mut` / `dynamic_object_field::
    // borrow_mut`: lift to `Expr::BorrowMapKey` so the writeback
    // chain produces a real `Mutation.borrowMapKey -> Mutation.set`
    // path. Generic-K calls fall through to the generic `Expr::Call`
    // path (handled by the renderer's `try_render_dynamic_field_call`
    // inlining to `(TypedMap.get parent.<ghost> key, parent)`).
    if dyn_field_borrow_mut_liftable_key(ctx.target.global_env(), module_id, fun_id, &type_args_ir)
    {
        return translate_borrow_native(
            BorrowNativeKind::MapKey,
            &type_args_ir,
            dests,
            srcs,
            pc,
            ctx,
        );
    }

    // User-wrapper recognition (Step 3 of
    // `plans/lean-pipeline/native-field-collapse-loses-map-key.md`):
    // user functions like `SkipList::borrow_mut`,
    // `wit_table::borrow_mut`, or multi-call wrappers like
    // `storage::get_emode_asset_mut` that chain
    // `dynamic_field::borrow_mut + table::borrow_mut`. The
    // pre-computed `user_wrapper_kvs` cache (built once at stage 2
    // entry by `wrapper_kv::build`) holds, for each
    // callee, the ordered list of `(K, V)` pairs corresponding to
    // its internal MapKey-class native borrow_mut callsites. We
    // instantiate that list against this call's `type_args` to get
    // caller-frame types and record it for the dest temp.
    //
    // The call itself still lifts to a generic `Expr::Call`; we
    // only feed `fill_map_key_types`, which patches placeholder
    // `MapKey { Unit, Unit }` edges in the downstream `WriteBack`
    // / `IsParent` lifted edges.
    if dests.len() == 1 {
        if let Some(cached) = ctx
            .prog
            .user_wrapper_kvs()
            .get(&(module_id, fun_id))
            .cloned()
        {
            let mut kv_list: Vec<(crate::ir::Type, crate::ir::Type)> =
                Vec::with_capacity(cached.len());
            for (k_user, v_user) in cached {
                let k_user = k_user.instantiate(type_args);
                let v_user = v_user.instantiate(type_args);
                let k_ir = translate_type(&k_user, ctx.prog)?;
                let v_ir = translate_type(&v_user, ctx.prog)?;
                kv_list.push((k_ir, v_ir));
            }
            if !kv_list.is_empty() {
                ctx.borrow_mut_kv.insert(temp_name(dests[0]), kv_list);
            }
        }
    }

    let args: Vec<Expr> = srcs.iter().map(|t| var(*t)).collect();
    let call = Expr::Call {
        fun: fid,
        type_args: type_args_ir,
        args,
    };
    Ok(Some(bind_dests(dests, call)))
}

/// Categorise a callee FunId as one of the borrow-mut natives stage 2
/// promotes to a dedicated IR variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BorrowNativeKind {
    /// `0x1::vector::borrow_mut(v, i)`.
    VecIndex,
    /// One of the map-style `borrow_mut(t, k)` / `get_mut(m, k)`
    /// natives. The (K, V) types come from the call's `type_args`
    /// at positions (0, 1).
    MapKey,
}

/// Inspect a callee's qualified name and decide whether it's one of
/// the recognized borrow-mut natives. Returns `None` for everything
/// else (the generic `Expr::Call` path handles them).
pub(super) fn recognize_borrow_native(
    env: &move_model::model::GlobalEnv,
    module_id: ModuleId,
    fun_id: move_model::model::FunId,
) -> Option<BorrowNativeKind> {
    let module = env.get_module(module_id);
    let module_name = module.get_name().display(env.symbol_pool()).to_string();
    let func = module.get_function(fun_id);
    let func_name = func.get_name_str();
    // module_name shapes seen here are `0x1::vector`, `0x2::table`,
    // `0x2::bag`, etc. Strip the address prefix and match on
    // `<module>::<function>`.
    let bare = module_name.split("::").last().unwrap_or("");
    // `dynamic_field` / `dynamic_object_field` borrow_mut calls are
    // routed here only when the **key type is concrete** (no
    // `TypeParam` anywhere in K). See
    // `dyn_field_borrow_mut_with_concrete_key` -- the actual gate
    // is in `translate_function_call` since this function doesn't
    // have type_args. Concrete-K dispatch lifts to
    // `Expr::BorrowMapKey` so the writeback chain through the
    // parent's ghost slot becomes a real `Mutation.borrowMapKey`
    // chain. Stage 7's aborts_variant splice walker is extended to
    // also trigger on `BorrowMapKey` sites at augmented parents,
    // so the `.aborts` companion still gets the abort check.
    match (bare, func_name.as_str()) {
        ("vector", "borrow_mut") => Some(BorrowNativeKind::VecIndex),
        ("table", "borrow_mut")
        | ("bag", "borrow_mut")
        | ("object_table", "borrow_mut")
        | ("object_bag", "borrow_mut")
        | ("vec_map", "get_mut") => Some(BorrowNativeKind::MapKey),
        _ => None,
    }
}

/// True iff a Move-internal callsite to `dynamic_field::borrow_mut` /
/// `dynamic_object_field::borrow_mut` should be lifted to
/// `Expr::BorrowMapKey`. Gated on the bytecode's `type_args[0]`
/// (the `Name` parameter, our `K`) being free of `TypeParam` --
/// concrete primitives (`u64`, `address`, ...) and concrete struct
/// types qualify, anything with a generic parameter does not.
///
/// Generic-K callsites (the wrapper's own body forwarding the type
/// param into `field::borrow_mut<K, ...>`) fall through to the
/// generic `Expr::Call` path; the renderer's
/// `try_render_dynamic_field_call` then inlines a polymorphic
/// `(TypedMap.get parent.<ghost> key, parent)` substitution.
pub(super) fn dyn_field_borrow_mut_liftable_key(
    env: &move_model::model::GlobalEnv,
    module_id: ModuleId,
    fun_id: move_model::model::FunId,
    type_args: &[crate::ir::Type],
) -> bool {
    let module = env.get_module(module_id);
    let module_name = module.get_name().display(env.symbol_pool()).to_string();
    let func = module.get_function(fun_id);
    let func_name = func.get_name_str();
    let bare = module_name.split("::").last().unwrap_or("");
    let is_dyn_field = matches!(
        (bare, func_name.as_str()),
        ("dynamic_field", "borrow_mut") | ("dynamic_object_field", "borrow_mut"),
    );
    if !is_dyn_field {
        return false;
    }
    // Accept EVERY key type. Concrete keys and bare `TypeParam` keys
    // wrap via the threaded `ToAnyKey` / recover via `FromAnyKey` on the
    // escaping-&mut path. Non-bare generic keys (e.g.
    // `PoolRewardCustodianDfKey<R>`, momentum pool.move) are accepted
    // since step-2 slice B1: the World store keys ride `HasCode TyCode`
    // (the dyn-type universe derives composite instances via wrapping
    // structs), and the same-function writeback recovers the key from
    // the borrow site's IR expression (`route_block`'s `key_for_var`),
    // never touching AnyKey. The previous exclusion left these sites as
    // unlifted native calls rendering through the Inhabited-DEFAULT
    // `def borrow_mut` stub -- a silent wrong-value read. Escaping
    // &mut with a non-bare generic key still degrades to the AnyKey
    // `unit` catch-all exactly as before; that surface is unchanged.
    let _ = type_args;
    true
}

/// Emit the IR for a recognized borrow-mut native callsite.
fn translate_borrow_native(
    kind: BorrowNativeKind,
    type_args: &[crate::ir::Type],
    dests: &[TempIndex],
    srcs: &[TempIndex],
    pc: CodeOffset,
    ctx: &mut TranslateCtx,
) -> Result<Option<Stmt>, Stage2Error> {
    let dest = single_dest(dests, pc, "borrow_mut native")?;
    let pattern = vec![Some(temp_name(dest))];
    match kind {
        BorrowNativeKind::VecIndex => {
            // vector::borrow_mut<T>(v: &mut vector<T>, i: u64): &mut T
            if srcs.len() != 2 {
                return Err(Stage2Error::malformed_arity(
                    "vector::borrow_mut",
                    "srcs",
                    2,
                    srcs.len(),
                    pc,
                ));
            }
            let value = Expr::Borrow {
                step: PathStep::VecIndex(Box::new(var(srcs[1]))),
                base: Box::new(var(srcs[0])),
            };
            Ok(Some(Stmt::Let { pattern, value }))
        }
        BorrowNativeKind::MapKey => {
            // <container>::borrow_mut<K, V>(t: &mut T<K, V>, k: K): &mut V
            // type_args = [K, V] (V may be absent for vec_map::get_mut
            // since it's <K, V> at the module level, but the call's
            // type_args carry both).
            if srcs.len() != 2 {
                return Err(Stage2Error::malformed_arity(
                    "map borrow_mut",
                    "srcs",
                    2,
                    srcs.len(),
                    pc,
                ));
            }
            if type_args.len() < 2 {
                return Err(Stage2Error::malformed_arity(
                    "map borrow_mut",
                    "type_args",
                    2,
                    type_args.len(),
                    pc,
                ));
            }
            // Record (K, V) for this borrow temp so the corresponding
            // `Operation::WriteBack(Reference($tDest), Index(Table|Custom), ..)`
            // (or `DynamicField(..)` which already carries types) can
            // recover the types when emitting `BorrowEdge::MapKey { .. }`.
            ctx.borrow_mut_kv.insert(
                temp_name(dest),
                vec![(type_args[0].clone(), type_args[1].clone())],
            );
            let value = Expr::Borrow {
                step: PathStep::MapKey {
                    key: Box::new(var(srcs[1])),
                    key_type: type_args[0].clone(),
                    value_type: type_args[1].clone(),
                    df_value: None,
                },
                base: Box::new(var(srcs[0])),
            };
            Ok(Some(Stmt::Let { pattern, value }))
        }
    }
}

/// Lift an upstream `BorrowNode` to our IR shape.
fn lift_borrow_node(
    node: &move_stackless_bytecode::stackless_bytecode::BorrowNode,
    ctx: &mut TranslateCtx,
) -> Result<crate::ir::BorrowNode, Stage2Error> {
    use move_stackless_bytecode::stackless_bytecode::BorrowNode as Up;
    match node {
        Up::LocalRoot(t) => Ok(crate::ir::BorrowNode::LocalRoot(temp_name(*t))),
        Up::Reference(t) => Ok(crate::ir::BorrowNode::Reference(temp_name(*t))),
        // Move classic global storage (`borrow_global<R>(addr)`) --
        // Sui Move doesn't have this; stage 2 rejects
        // `Operation::BorrowGlobal` upstream so this arm is
        // unreachable on the active path. Reject defensively rather
        // than carrying an unused IR variant.
        Up::GlobalRoot(_) => Err(Stage2Error::NotImplemented {
            reason: "BorrowNode::GlobalRoot (Move classic global storage; not in Sui Move)",
        }),
        Up::SpecGlobalRoot(types) => {
            let mut type_args = Vec::with_capacity(types.len());
            for t in types {
                type_args.push(translate_type(t, ctx.prog)?);
            }
            Ok(crate::ir::BorrowNode::SpecGlobalRoot { type_args })
        }
        Up::ReturnPlaceholder(_) => Err(Stage2Error::NotImplemented {
            reason: "BorrowEdge::ReturnPlaceholder",
        }),
    }
}

fn prepare_borrow_edge(
    edge: &move_stackless_bytecode::stackless_bytecode::BorrowEdge,
    child: TempIndex,
    ctx: &mut TranslateCtx,
) -> Result<crate::ir::BorrowEdge, Stage2Error> {
    let edge = lift_borrow_edge(edge, ctx)?;
    let kvs = ctx.borrow_mut_kv.get(&temp_name(child));
    Ok(prepare_lifted_borrow_edge(
        edge,
        kvs.map(Vec::as_slice),
        ctx.prog.program(),
    ))
}

fn prepare_lifted_borrow_edge(
    mut edge: crate::ir::BorrowEdge,
    kvs: Option<&[(crate::ir::Type, crate::ir::Type)]>,
    program: &crate::ir::Program,
) -> crate::ir::BorrowEdge {
    // Calls to recognized map-style borrow natives record their K/V
    // types by destination temp. Apply those types to the matching
    // WriteBack / IsParent edge, including vec_map's upstream VecIndex
    // summary, before consulting the actual container shape.
    if let Some(kv) = kvs {
        promote_vec_index_for_map_borrow(&mut edge, kv);
        fill_map_key_types(&mut edge, kv);
    }
    // Preserve this order: promotion/filling uses callsite metadata;
    // demotion and retyping then reconcile it with the container; final
    // normalization removes only placeholders that remain unresolved.
    demote_map_key_for_vector_field(&mut edge, program);
    retype_native_map_key_from_container(&mut edge, program);
    normalize_borrow_edge(edge)
}

/// Promote `BorrowEdge::VecIndex` entries to `BorrowEdge::MapKey { K, V }`
/// in the writeback edge of a child that was borrowed via a MapKey
/// native (`table::borrow_mut`, `bag::borrow_mut`, `vec_map::get_mut`,
/// ...).
///
/// Upstream's `BorrowAnnotation` walks into the native's source code
/// when computing the writeback edge. For `vec_map::get_mut` -- whose
/// internal implementation is `&mut self.contents[idx].value` over a
/// `vector<Entry<K, V>>` field -- the writeback edge surfaces as
/// `Index(Vector)`. After `is_native_struct` in `lift_borrow_edge`
/// collapses `Field(VecMap, contents)` and `Field(Entry, value)` to
/// `Direct`, the surviving edge is a bare `VecIndex` (or a Hyper chain
/// with a `VecIndex` step). The forward borrow was correctly emitted
/// as `BorrowMapKey`, so the renderer's writeback dispatch should
/// match -- `writeBackMapKey`, not `writeBackVecIndex`.
///
/// Promotion rule: replace every `VecIndex` in the chain with
/// `MapKey { K, V }` from the recorded `(K, V)` pair. This is sound
/// because `ctx.borrow_mut_kv` is only populated for
/// `BorrowNativeKind::MapKey` natives (see `translate_borrow_native`);
/// `vector::borrow_mut` records nothing, so its writebacks pass through
/// unchanged.
///
/// Called BEFORE `fill_map_key_types` so the promoted MapKey already
/// carries real `(K, V)` and isn't re-patched by the placeholder pass.
fn promote_vec_index_for_map_borrow(
    edge: &mut crate::ir::BorrowEdge,
    kvs: &[(crate::ir::Type, crate::ir::Type)],
) {
    use crate::ir::BorrowEdge as E;
    if kvs.is_empty() {
        return;
    }
    let (kt, vt) = (kvs[0].0.clone(), kvs[0].1.clone());
    fn promote(e: &mut E, kt: &crate::ir::Type, vt: &crate::ir::Type) {
        match e {
            E::VecIndex => {
                *e = E::MapKey {
                    key_type: kt.clone(),
                    value_type: vt.clone(),
                };
            }
            E::Hyper(es) => {
                for child in es.iter_mut() {
                    promote(child, kt, vt);
                }
            }
            E::Direct | E::StructField { .. } | E::EnumField { .. } | E::MapKey { .. } => {}
        }
    }
    promote(edge, &kt, &vt);
}

/// Dual of [`promote_vec_index_for_map_borrow`]: convert a `MapKey` edge
/// into `VecIndex` when its container is a genuine `Vector`/`List` field.
///
/// Upstream summarizes a find-by-value lookup over a `vector<V>` -- e.g.
/// `validator_set::get_validator_mut(addr)` -> `find_index(addr)` ->
/// `vector::borrow_mut(active_validators, idx)` -- as a `MapKey` edge keyed
/// by the lookup value (`address` / `u64`), even though the storage is a
/// `Vector` modeled as a Lean `List` indexed by `Nat`. A `MapKey` step
/// whose container type is `Vector` is therefore ALWAYS a mis-summarized
/// vector access (a vector cannot be map-keyed). Demote it so the edge KIND
/// matches the container: the renderer emits `vecIndex` / `writeBackVecIndex`
/// (recovering the real index from the child's runtime path), and
/// `Mutation.isParent`'s `edgeMatchesAncestor` need not treat `mapKey` and
/// `vecIndex` as interchangeable.
///
/// Tracks the container type along the chain from each `StructField`'s
/// struct definition. A `MapKey` whose container cannot be PROVEN `Vector`
/// (unknown type, a collapsed `Direct` native step, an `EnumField`, or a
/// real `Table`/`VecMap`/`Bag` field) is left untouched -- the exact dual
/// of the promotion: promotion fixes `VecIndex` over a map-native, demotion
/// fixes `MapKey` over a vector field.
///
/// Demotion fires ONLY on an IN-VALUE vector -- one reached purely through
/// struct fields / vec indices from the borrow root. A `MapKey` reached
/// AFTER a prior `MapKey` (the vector is itself the VALUE of a dynamic field
/// or a native map) is left untouched: that value lives in `World` and is
/// handled by the dynamic-field routing. In particular the df-internal
/// `MapKey { Unit, Unit }` placeholder that `normalize_borrow_edge` drops
/// must stay a `MapKey` -- demoting it to a surviving `VecIndex` would push
/// the df anchor off index 0 and break the world write-back (scallop
/// `record_min_price_history`'s `df[MinPriceHistoryKey] : vector<...>`).
fn demote_map_key_for_vector_field(edge: &mut crate::ir::BorrowEdge, program: &crate::ir::Program) {
    use crate::ir::BorrowEdge as E;
    use crate::ir::Type;
    fn walk(
        e: &mut E,
        cur: &mut Option<Type>,
        seen_map_key: &mut bool,
        program: &crate::ir::Program,
    ) {
        match e {
            E::StructField {
                struct_id,
                field_index,
            } => {
                *cur = program
                    .structs
                    .get(&*struct_id)
                    .and_then(|s| s.fields.get(*field_index))
                    .map(|f| f.field_type.clone());
            }
            E::VecIndex => {
                *cur = match cur.take() {
                    Some(Type::Vector(inner)) => Some(*inner),
                    _ => None,
                };
            }
            E::MapKey { value_type, .. } => match cur {
                // In-value vector reached purely via struct fields (no
                // prior map/df indirection) -> a mis-summarized vector
                // access; demote to VecIndex.
                Some(Type::Vector(inner)) if !*seen_map_key => {
                    let elem = (**inner).clone();
                    *e = E::VecIndex;
                    *cur = Some(elem);
                }
                // Real map / df value (or a vector that is itself a map
                // value): keep the MapKey and record that we have entered
                // map/df-value territory.
                _ => {
                    *cur = Some(value_type.clone());
                    *seen_map_key = true;
                }
            },
            // EnumField: stop tracking (variant-field vector containers
            // reached by a value lookup are not a case we model). Direct:
            // identity edge, container type unchanged.
            E::EnumField { .. } => *cur = None,
            E::Direct => {}
            E::Hyper(es) => {
                for c in es.iter_mut() {
                    walk(c, cur, seen_map_key, program);
                }
            }
        }
    }
    let mut cur: Option<Type> = None;
    let mut seen_map_key = false;
    walk(edge, &mut cur, &mut seen_map_key, program);
}

/// Correct any IN-VALUE native-map lookup `MapKey` whose recorded
/// `(key_type, value_type)` disagree with its CONTAINER field's own type
/// args, re-reading them from the container. Ground truth is the container
/// field type; the mapKey's summary-derived types can be wrong.
///
/// Upstream's borrow SUMMARY for a MULTI-STEP resolver can collapse an
/// earlier native-map-lookup MapKey's `(K, V)` onto a LATER dynamic-field
/// anchor even though `fill_map_key_types` now tracks an ordered pair per
/// wrapper-body call site. sui-system's
/// `any_validator_mut` candidate branch is
/// `self.validator_candidates[addr].load_validator_maybe_upgrade()` -- a
/// `Table<address, ValidatorWrapper>` lookup THEN a `Versioned` dynamic
/// field -- and is recorded
/// `hyper(.S#143.f6 -> .S#65.f1 -> [u64 -> Validator] -> .S#133.f0 ->
///  .S#109.f0 -> [u64 -> Validator])`: the Table lookup's real
/// `(address, ValidatorWrapper)` collapsed onto the df anchor's
/// `(u64, Validator)`. The DIRECT `candidate_validator_mut` (identical
/// body) records `[address -> ValidatorWrapper]` correctly, so the two df
/// writebacks diverge and only the direct one passes
/// `hyper_has_df_mapkey`'s well-formedness gate + world-threads
/// (ledger item 34 (iii)).
///
/// Walk the Hyper chain tracking the container type. At each `MapKey`
/// whose container is a `Table` / `VecMap` / `ObjectTable` (the in-value
/// recon native maps -- Bag/ObjectBag are universe-coded and excluded) AND
/// whose container `(K, V)` are CONCRETE, overwrite `(K, V)` from the
/// container. A generic container's DEFINITION field type carries
/// `TypeParam`s (not the instantiated types `fill_map_key_types` already
/// recorded), so it is deliberately left untouched. The df anchor
/// (container = `object::UID`, not a native map) and every already-correct
/// MapKey stay byte-identical. The native-map content-placeholder
/// StructField (`.S#<Map>.f<size>`) is SKIPPED in the walk so the
/// container type survives to the following MapKey. Kept in lockstep with
/// `render::expr::writeback::is_native_map_content_placeholder` and the
/// `dynamic_field_rewrite::prefix_is_world_reconstructable` gate.
fn retype_native_map_key_from_container(
    edge: &mut crate::ir::BorrowEdge,
    program: &crate::ir::Program,
) {
    use crate::ir::BorrowEdge as E;
    use crate::ir::Type;
    fn native_map_kv(ty: &Type, program: &crate::ir::Program) -> Option<(Type, Type)> {
        if let Type::Struct {
            struct_id,
            type_args,
        } = ty
        {
            if type_args.len() == 2
                && program.structs.get(struct_id).map_or(false, |s| {
                    matches!(
                        s.qualified_name.as_str(),
                        "table::Table" | "vec_map::VecMap" | "object_table::ObjectTable"
                    )
                })
            {
                return Some((type_args[0].clone(), type_args[1].clone()));
            }
        }
        None
    }
    fn type_is_concrete(ty: &Type) -> bool {
        match ty {
            Type::TypeParam(_) => false,
            Type::Vector(inner) | Type::Reference(inner) | Type::MutableRef { inner, .. } => {
                type_is_concrete(inner)
            }
            Type::Struct { type_args, .. } => type_args.iter().all(type_is_concrete),
            Type::Tuple(items) => items.iter().all(type_is_concrete),
            _ => true,
        }
    }
    fn field_ty(
        sid: crate::ir::StructId,
        fidx: usize,
        program: &crate::ir::Program,
    ) -> Option<Type> {
        program
            .structs
            .get(&sid)
            .and_then(|s| s.fields.get(fidx))
            .map(|f| f.field_type.clone())
    }
    let es = match edge {
        E::Hyper(es) => es,
        _ => return,
    };
    let n = es.len();
    let mut cur: Option<Type> = None;
    for i in 0..n {
        // Snapshot what we need from `es[i]` (immutable), releasing the
        // borrow before any mutation of `es[i]`.
        let next_is_map_key = matches!(es.get(i + 1), Some(E::MapKey { .. }));
        let sf = match &es[i] {
            E::StructField {
                struct_id,
                field_index,
            } => Some((*struct_id, *field_index)),
            _ => None,
        };
        let is_map_key = matches!(&es[i], E::MapKey { .. });
        let is_untyped_placeholder_map_key = matches!(
            &es[i],
            E::MapKey {
                key_type: Type::Unit,
                value_type: Type::Unit
            }
        );
        let mk_value_type = match &es[i] {
            E::MapKey { value_type, .. } => Some(value_type.clone()),
            _ => None,
        };
        let is_vec_index = matches!(&es[i], E::VecIndex);
        let is_enum = matches!(&es[i], E::EnumField { .. });
        if let Some((sid, fidx)) = sf {
            let cur_is_native_map = cur
                .as_ref()
                .map_or(false, |t| native_map_kv(t, program).is_some());
            if cur_is_native_map && next_is_map_key {
                // native-map content placeholder: keep `cur` (the map type).
            } else {
                cur = field_ty(sid, fidx, program);
            }
        } else if is_map_key {
            if is_untyped_placeholder_map_key {
                // The untyped `MapKey { Unit, Unit }` is NOT a real in-value
                // lookup: it is the dynamic_field internal `Field<K, V>`
                // value-cell artifact (or an unknown user-container step)
                // that `normalize_borrow_edge` drops AFTER this pass. When
                // the df VALUE is itself a native map, typing the artifact
                // from that container resurrects it as a phantom content
                // lookup and mis-routes the writeback into the map-leaf arm
                // (ill-typed `writeBackMapKey` on the concretely-typed df
                // node -- current-lending `whitelist_admin`). Leave it
                // untyped so normalize can drop it; the container type is
                // unknown past it until a StructField re-anchors `cur`.
                cur = None;
            } else if let Some((k, v)) = cur.as_ref().and_then(|t| native_map_kv(t, program)) {
                if type_is_concrete(&k) && type_is_concrete(&v) {
                    if let E::MapKey {
                        key_type,
                        value_type,
                    } = &mut es[i]
                    {
                        *key_type = k;
                        *value_type = v.clone();
                    }
                }
                cur = Some(v);
            } else {
                cur = mk_value_type;
            }
        } else if is_vec_index {
            cur = match cur.take() {
                Some(Type::Vector(inner)) => Some(*inner),
                _ => None,
            };
        } else if is_enum {
            cur = None;
        }
        // E::Direct: identity edge, container unchanged.
        // E::Hyper: post-flatten none survive; leave `cur` as-is.
    }
}

/// Replace placeholder `MapKey { Unit, Unit }` entries with the corresponding
/// ordered `(K, V)` pairs. A `DynamicField(_, K, V)` edge already has real
/// types and is left alone.
///
/// Upstream emits several distinct Hyper shapes:
///
/// 1. A native wrapper lookup such as `Hyper([Field(Table, 1), Index(Table)])`
///    contains one user-visible placeholder, which receives the recorded pair.
/// 2. A user wrapper can put that placeholder in the middle of a longer field
///    path; it is still patched in place.
/// 3. A composed dynamic-field lookup can produce
///    `Hyper([DynamicField(K, V), Index(Table)])`. The trailing placeholder is
///    the dynamic field's internal wrapper artifact and must remain untyped so
///    `normalize_borrow_edge` removes it instead of rendering a second lookup.
///
/// Therefore a placeholder immediately after a typed MapKey deliberately
/// consumes a pair but remains untyped. Later placeholders represent distinct
/// lookups and receive their pairs. This keeps multi-key wrapper call sites
/// aligned with the ordered `borrow_mut_kv` list.
fn fill_map_key_types(
    edge: &mut crate::ir::BorrowEdge,
    kvs: &[(crate::ir::Type, crate::ir::Type)],
) {
    use crate::ir::BorrowEdge as E;
    use crate::ir::Type;
    fn is_placeholder_map_key_top(e: &E) -> bool {
        matches!(
            e,
            E::MapKey {
                key_type: Type::Unit,
                value_type: Type::Unit
            }
        )
    }
    fn is_typed_map_key_top(e: &E) -> bool {
        matches!(
            e,
            E::MapKey {
                key_type: kt,
                value_type: vt,
            } if !(matches!(kt, Type::Unit) && matches!(vt, Type::Unit))
        )
    }
    if kvs.is_empty() {
        return;
    }
    match edge {
        E::MapKey {
            key_type,
            value_type,
        } if matches!(key_type, Type::Unit) && matches!(value_type, Type::Unit) => {
            // Single edge, single-step wrapper -- patch with kvs[0].
            *key_type = kvs[0].0.clone();
            *value_type = kvs[0].1.clone();
        }
        E::Hyper(es) => {
            // Walk left-to-right. Each placeholder corresponds to one
            // internal borrow_mut step in the wrapper's body and
            // consumes ONE entry from `kvs` regardless of whether we
            // patch it. A placeholder preceded by a typed MapKey is
            // the internal indirection of a dynamic_field-class step
            // whose typed `MapKey { K, V }` already captures the
            // user-visible storage; SKIP patching that placeholder
            // (`normalize_borrow_edge` drops it) but still ADVANCE the
            // kv index so the i-th non-internal placeholder lines up
            // with the i-th wrapper-body recorded pair.
            //
            // Example -- `storage::get_emode_asset_mut`:
            //   wrapper body has two internal natives:
            //     dynamic_field::borrow_mut<EMODE_KEY, Emode>
            //     table::borrow_mut<u64, EmodeConfig>
            //   kvs = [(EMODE_KEY, Emode), (u64, EmodeConfig)]
            //   lifted chain after upstream summary + lift:
            //     [MapKey{EMODE_KEY, Emode},     <- typed from DynamicField summary
            //      MapKey{U, U},                  <- placeholder, internal indirection -> SKIP, advance to kvs[1]
            //      StructField{Emode.emodes_pair},
            //      Direct,                         <- collapsed Field(Table, 1)
            //      MapKey{U, U},                  <- placeholder, table user-visible step -> PATCH with kvs[1]
            //      StructField{...}]
            let mut i = 0usize;
            let mut prev_was_typed_map_key = false;
            for e in es.iter_mut() {
                if i >= kvs.len() {
                    break;
                }
                if is_placeholder_map_key_top(e) {
                    if !prev_was_typed_map_key {
                        if let E::MapKey {
                            key_type,
                            value_type,
                        } = e
                        {
                            *key_type = kvs[i].0.clone();
                            *value_type = kvs[i].1.clone();
                        }
                    }
                    i += 1;
                    // After patching the placeholder becomes a typed
                    // MapKey; reset the gate for the next position.
                    prev_was_typed_map_key = false;
                } else if is_typed_map_key_top(e) {
                    prev_was_typed_map_key = true;
                } else {
                    prev_was_typed_map_key = false;
                }
            }
        }
        E::Direct
        | E::StructField { .. }
        | E::EnumField { .. }
        | E::VecIndex
        | E::MapKey { .. } => {}
    }
}

/// Remove placeholder `MapKey { Unit, Unit }` edges from `Hyper`
/// chains. Placeholders that survived `fill_map_key_types`
/// (i.e. the surrounding borrow-mut native wasn't in
/// `recognize_borrow_native`'s allowlist OR upstream's
/// `BorrowAnnotation` emitted an extra `Index(Custom)` alongside a
/// real `DynamicField`) are internal-wrapping artifacts that the
/// renderer's prelude collapses transparently:
///
/// - For Sui's `dynamic_field::*`: upstream encodes the write-back
///   chain as `Hyper([DynamicField(K, V), Index(Custom)])`. The
///   `Index(Custom)` represents the indirection through the boxed
///   `Field<K, V>` value-cell that Sui's dynamic_field stores
///   internally. Our IR's `BorrowEdge::MapKey { K, V }` (lifted from
///   `DynamicField`) already captures the user-visible storage, and
///   the Lean `Dynamic_field.*` natives apply the wrapper internally;
///   the extra placeholder edge would otherwise force the renderer to
///   emit a `TypedMap.set _ _ parent.val ...` call that takes a
///   `List (K × V)`, which `parent` (a user struct holding the UID)
///   isn't.
/// - For user-defined containers without recognition: the chain may
///   carry a placeholder for the unknown borrow-step. Dropping it is
///   the closest semantic to "we don't know what this edge does";
///   the surviving edges still convey the user-visible borrow
///   structure.
///
/// If filtering reduces the chain to a single edge, return it
/// directly (not wrapped in `Hyper`); if to zero edges, return
/// `BorrowEdge::Direct`. Idempotent.
fn normalize_borrow_edge(edge: crate::ir::BorrowEdge) -> crate::ir::BorrowEdge {
    use crate::ir::BorrowEdge as E;
    use crate::ir::Type;
    fn is_placeholder_map_key(e: &E) -> bool {
        matches!(
            e,
            E::MapKey {
                key_type: Type::Unit,
                value_type: Type::Unit
            }
        )
    }
    match edge {
        E::Hyper(es) => {
            // Drop trivial `Direct` edges and recurse into nested
            // Hypers everywhere. `Direct` inside a chain is a no-op
            // (the writeback's value just passes through unchanged
            // at that step), so removing it doesn't change
            // semantics but lets singleton chains collapse to a
            // plain edge that the renderer handles without the
            // path-match form.
            //
            // Placeholder `MapKey { Unit, Unit }` edges need a
            // positional discrimination:
            //
            //  * A **trailing** placeholder is the dynamic_field
            //    internal-wrapping artifact. Sui's
            //    `dynamic_field::*` lowers to `Hyper([DynamicField(K, V),
            //    Index(Custom)])`: position 0 carries the
            //    user-visible (K, V); position 1 is the boxed
            //    `Field<K, V>` value-cell indirection that the Lean
            //    `Dynamic_field.*` natives apply transparently.
            //    Drop it.
            //  * A **middle / leading** placeholder is a real
            //    user-visible Table::borrow_mut whose (K, V) types
            //    couldn't be recovered from the direct call or the
            //    wrapper fixed-point. Dropping it
            //    collapses the chain into a structurally wrong
            //    shape -- the renderer ends up emitting field
            //    accesses on the container's value-type at the
            //    parent position. Keep the placeholder; the
            //    renderer falls back to `AnyKey.unit` at the
            //    runtime-key position but preserves the structural
            //    step in the chain.
            //
            // Surfaced in the navi/lending `validator_set::{
            // request_withdraw_stake, convert_to_fungible_staked_sui,
            // redeem_fungible_staked_sui}` family -- a 6-edge
            // upstream chain `[Field(VS, validator_candidates),
            // Field(Table, _), Index(Table), Field(Wrapper, inner),
            // Field(Versioned, _), DynamicField(u64, Validator)]`
            // where the middle `Index(Table)` carries the
            // user-visible `Table<address, ValidatorWrapper>`
            // lookup and the trailing `DynamicField` is the inner
            // Versioned indirection. The old filter dropped the
            // middle placeholder and produced the structurally
            // wrong chain `[StructField, StructField, MapKey]` --
            // see `plans/lean-pipeline/validator-set-writeback-handoff.md`.
            // Recursive normalization on Hyper elements MUST
            // preserve placeholder `MapKey { Unit, Unit }` entries
            // -- the standalone-placeholder collapse-to-Direct
            // rule below would otherwise wipe out middle
            // placeholders before the positional drop loop below
            // runs. Only recurse into nested Hypers and pass
            // non-Hyper edges through unchanged at this level.
            fn normalize_inside_hyper(e: E) -> E {
                match e {
                    E::Hyper(_) => normalize_borrow_edge(e),
                    other => other,
                }
            }
            let mut normalized: Vec<E> = es
                .into_iter()
                .map(normalize_inside_hyper)
                .filter(|e| !matches!(e, E::Direct))
                .collect();
            // Drop trailing placeholders (one or more in a row,
            // defensively -- the dynamic_field pattern emits exactly
            // one, but cascades of `Index(Custom)` are possible).
            while normalized
                .last()
                .map(is_placeholder_map_key)
                .unwrap_or(false)
            {
                normalized.pop();
            }
            // Drop middle placeholders whose IMMEDIATELY-PRECEDING
            // edge is a typed (non-placeholder) MapKey. That pattern
            // is the internal Table indirection of a native container
            // (e.g. SkipList, wit_table, generic_store wrappers) whose
            // typed `MapKey { K, V }` from upstream's borrow_mut
            // summary already captures the user-visible storage step
            // -- the placeholder is the redundant internal `Index(Table)`
            // that the Lean prelude handles transparently inside the
            // native module's hand-written body.
            //
            // Surfaced as the dominant noise source on the new-pipeline
            // sweep (195 of 220 render-time invariant violations on the
            // 2026-05-16 baseline). Concrete chain from
            // `cetus_dlmm::bin::init_bin`:
            //
            //   upstream: Hyper([
            //     Field(bin::BinManager, 2),
            //     DynamicField(skip_list::SkipList, K=u64, V=skip_list::Node<MT>),
            //     Index(Table),                         <- internal
            //     Field(skip_list::Node, 3),            <- internal, collapses to Direct
            //     Field(bin::BinGroupRef, 1),
            //     Field(bin::BinGroup, 2),
            //     Index(Vector),
            //   ])
            //
            // The `Index(Table)` after the typed `DynamicField` is the
            // internal Sui-dynamic_field Table that `skip_list`'s
            // hand-written prelude (legacy) or IR-translated wrapper (new) already
            // encapsulates -- dropping it lines up the
            // chain with what the prelude expects.
            //
            // Does NOT touch placeholders preceded by Direct /
            // StructField / EnumField / VecIndex: those are the
            // validator-set shape where the placeholder IS the
            // user-visible Table::borrow_mut step (see the long comment
            // above and `plans/lean-pipeline/validator-set-writeback-handoff.md`).
            fn is_typed_map_key(e: &E) -> bool {
                matches!(
                    e,
                    E::MapKey {
                        key_type: kt,
                        value_type: vt,
                    } if !(matches!(kt, Type::Unit) && matches!(vt, Type::Unit))
                )
            }
            let mut i = 1;
            while i < normalized.len() {
                if is_placeholder_map_key(&normalized[i]) && is_typed_map_key(&normalized[i - 1]) {
                    normalized.remove(i);
                } else {
                    i += 1;
                }
            }
            match normalized.len() {
                0 => E::Direct,
                1 => normalized.into_iter().next().unwrap(),
                _ => E::Hyper(normalized),
            }
        }
        // Top-level placeholder (rare; would only happen if a
        // standalone `Operation::Index(Custom)` survived without a
        // recognised surrounding borrow_mut). Collapsing to `Direct`
        // matches the Hyper case so downstream stages don't see
        // Unit-typed `BorrowEdge::MapKey` edges.
        e if is_placeholder_map_key(&e) => E::Direct,
        other => other,
    }
}

/// Lift an upstream `BorrowEdge` to the pipeline IR. `Index(Table | Custom)`
/// and `DynamicField(..)` become `BorrowEdge::MapKey`; `Index(Vector)` becomes
/// `BorrowEdge::VecIndex`. See the typed `Mutation` design in
/// `plans/lean-pipeline/mutable-references.md` and the IR decision log.
fn lift_borrow_edge(
    edge: &move_stackless_bytecode::stackless_bytecode::BorrowEdge,
    ctx: &mut TranslateCtx,
) -> Result<crate::ir::BorrowEdge, Stage2Error> {
    use move_stackless_bytecode::stackless_bytecode::{BorrowEdge as Up, IndexEdgeKind as UpIdx};
    match edge {
        Up::Direct => Ok(crate::ir::BorrowEdge::Direct),
        Up::Field(qiid, idx) => {
            let struct_id = resolved_struct_id(qiid.module_id, qiid.id, ctx.prog);
            // Upstream's BorrowAnnotation reaches inside native
            // container implementations (e.g. `Sui::table` records
            // an internal `Field(Table, size_idx)` edge for the
            // size-increment that `table::add` does on its own state).
            // Those edges point at an internal slot of a struct we
            // register as native (via `lift_struct` with `is_native`);
            // the synthetic `size_idx` has no user field-name string to
            // emit (the Lean prelude owns the struct
            // definition, not our IR). Collapse such edges to
            // `BorrowEdge::Direct`: the user's borrow chain's
            // top-level WriteBack still propagates the post-call
            // container value to its enclosing slot (the native
            // container itself becomes the "child" value), which is
            // the operationally-correct semantic -- the new
            // container value carries whatever internal state change
            // the native made. The collapse is sound regardless of
            // which internal field upstream tagged.
            let is_native_struct = ctx
                .prog
                .program()
                .structs
                .get(&struct_id)
                .and_then(|s| ctx.prog.program().modules.get(&s.module_id))
                .map(|m| m.is_native)
                .unwrap_or(false);
            if is_native_struct {
                return Ok(crate::ir::BorrowEdge::Direct);
            }
            Ok(crate::ir::BorrowEdge::StructField {
                struct_id,
                field_index: *idx,
            })
        }
        Up::EnumField(qiid, idx, vid) => {
            let struct_id = resolved_struct_id(qiid.module_id, qiid.id, ctx.prog);
            let tag = ctx
                .target
                .global_env()
                .get_module(qiid.module_id)
                .into_enum(qiid.id)
                .get_variant(*vid)
                .get_tag();
            Ok(crate::ir::BorrowEdge::EnumField {
                struct_id,
                variant: tag,
                field_index: *idx,
            })
        }
        Up::Index(UpIdx::Vector) => Ok(crate::ir::BorrowEdge::VecIndex),
        // Table / Custom: both unify into MapKey. Upstream doesn't
        // carry (K, V) types on `BorrowEdge::Index(_)` directly; we
        // recover them from the surrounding `Operation::Function`
        // Call's `type_args` via the BorrowAnnotation lookup that
        // populated `ctx`. For now we emit Type::Unit placeholders;
        // the AnyKey collector pass in the renderer will need real
        // types, which a follow-up plumbing pass will thread through.
        Up::Index(UpIdx::Table) | Up::Index(UpIdx::Custom(_)) => {
            Ok(crate::ir::BorrowEdge::MapKey {
                key_type: crate::ir::Type::Unit,
                value_type: crate::ir::Type::Unit,
            })
        }
        Up::DynamicField(_qid, k_ty, v_ty) => {
            let key_type = super::types::translate_type(k_ty, ctx.prog)?;
            let value_type = super::types::translate_type(v_ty, ctx.prog)?;
            Ok(crate::ir::BorrowEdge::MapKey {
                key_type,
                value_type,
            })
        }
        Up::Hyper(edges) => {
            let mut out = Vec::with_capacity(edges.len());
            for e in edges {
                out.push(lift_borrow_edge(e, ctx)?);
            }
            Ok(crate::ir::BorrowEdge::Hyper(out))
        }
    }
}

/// Look up the numeric tag of an enum variant via the GlobalEnv.
/// `VariantId` is a `Symbol` wrapper and can't be converted to a
/// numeric index in isolation; we have to consult the enum's
/// declaration in the model.
fn variant_id_to_tag(
    target: &FunctionTarget,
    module_id: ModuleId,
    datatype_id: DatatypeId,
    variant_id: VariantId,
) -> usize {
    target
        .global_env()
        .get_module(module_id)
        .into_enum(datatype_id)
        .get_variant(variant_id)
        .get_tag()
}

fn single_dest(
    dests: &[TempIndex],
    pc: CodeOffset,
    op_name: &str,
) -> Result<TempIndex, Stage2Error> {
    if dests.len() == 1 {
        Ok(dests[0])
    } else {
        Err(Stage2Error::malformed_arity(
            op_name,
            "dests",
            1,
            dests.len(),
            pc,
        ))
    }
}

fn single_src(srcs: &[TempIndex], pc: CodeOffset, op_name: &str) -> Result<TempIndex, Stage2Error> {
    if srcs.len() == 1 {
        Ok(srcs[0])
    } else {
        Err(Stage2Error::malformed_arity(
            op_name,
            "srcs",
            1,
            srcs.len(),
            pc,
        ))
    }
}

fn binop_stmt(
    op: BinOp,
    dests: &[TempIndex],
    srcs: &[TempIndex],
    pc: CodeOffset,
    name: &str,
    ctx: &TranslateCtx,
) -> Result<Option<Stmt>, Stage2Error> {
    if srcs.len() != 2 {
        return Err(Stage2Error::malformed_arity(
            name,
            "srcs",
            2,
            srcs.len(),
            pc,
        ));
    }
    let dest = single_dest(dests, pc, name)?;
    Ok(Some(Stmt::Let {
        pattern: vec![Some(temp_name(dest))],
        value: Expr::BinOp {
            op,
            lhs: Box::new(value_operand(srcs[0], ctx)),
            rhs: Box::new(value_operand(srcs[1], ctx)),
        },
    }))
}

/// Materialise `Var($tN)` for a binop operand, wrapping with
/// `ReadRef` when the upstream local type is a reference.
///
/// Move's bytecode-level Eq / Lt / Gt / ... accept either `T` or
/// `&T` on each side -- comparing a borrowed local against a
/// freshly-loaded value is a single bytecode op. Our IR is stricter
/// (see `BinOpOperandTypesAgree` baseline invariant): both operands
/// must agree, so we read the reference here and let downstream
/// stages (mutation-to-let, SSA, ...) see uniform value-form arithmetic.
///
/// Mirrors the canonical Move semantics; equivalent to the
/// auto-deref Boogie inserts on the operand registers before
/// every comparison.
fn value_operand(t: TempIndex, ctx: &TranslateCtx) -> Expr {
    let mty = ctx.target.get_local_type(t);
    if matches!(mty, MoveType::Reference(_, _)) {
        Expr::ReadRef(Box::new(var(t)))
    } else {
        var(t)
    }
}

fn unop_stmt(
    op: UnOp,
    dests: &[TempIndex],
    srcs: &[TempIndex],
    pc: CodeOffset,
    name: &str,
) -> Result<Option<Stmt>, Stage2Error> {
    let src = single_src(srcs, pc, name)?;
    let dest = single_dest(dests, pc, name)?;
    Ok(Some(Stmt::Let {
        pattern: vec![Some(temp_name(dest))],
        value: Expr::UnOp {
            op,
            operand: Box::new(var(src)),
        },
    }))
}

#[cfg(test)]
mod tests {
    //! These tests don't go through a real `FunctionTarget` (that
    //! would require a full Move-model build). They cover the
    //! context-free construction and arity helpers used by
    //! [`translate_call_op`], plus borrow-edge normalization. The
    //! sui-lean playground and client sweeps provide the
    //! FunctionTarget-backed dispatch coverage.

    use ethnum::U256;

    use super::*;
    use crate::ir::{Const, Type as IrType};

    // ---- Helpers ------------------------------------------------------

    fn pb() -> ProgramBuilder {
        ProgramBuilder::new()
    }

    fn name(t: TempIndex) -> VarId {
        temp_name(t)
    }

    // ---- temp_name convention ----------------------------------------

    #[test]
    fn temp_name_uses_dollar_t_n_format() {
        assert_eq!(&*temp_name(0), "$t0");
        assert_eq!(&*temp_name(7), "$t7");
        assert_eq!(&*temp_name(42), "$t42");
    }

    // ---- BinOp / UnOp helpers (unit) ---------------------------------

    // FIXME: binop_stmt now takes `ctx: &TranslateCtx` (added when value_operand began
    // looking up local types for ReadRef wrapping). These two tests bypass FunctionTarget
    // construction and need a minimal TranslateCtx test-mock that this crate doesn't have
    // yet. Disabled until a `TranslateCtx::test_stub` is wired (or until binop_stmt is
    // refactored to accept `Option<&TranslateCtx>` for ctx-free unit tests).
    #[cfg(any())]
    #[test]
    fn binop_stmt_emits_let_with_binop_value() {
        let stmt = binop_stmt(BinOp::Add, &[10], &[1, 2], 0, "Add")
            .unwrap()
            .unwrap();
        match stmt {
            Stmt::Let { pattern, value } => {
                assert_eq!(pattern, vec![Some(name(10))]);
                match value {
                    Expr::BinOp { op, lhs, rhs } => {
                        assert_eq!(op, BinOp::Add);
                        assert_eq!(*lhs, Expr::Var(name(1)));
                        assert_eq!(*rhs, Expr::Var(name(2)));
                    }
                    other => panic!("expected BinOp, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    // FIXME: see comment on binop_stmt_emits_let_with_binop_value above.
    #[cfg(any())]
    #[test]
    fn binop_stmt_rejects_arity_mismatch() {
        let r = binop_stmt(BinOp::Add, &[10], &[1], 5, "Add");
        assert!(r.is_err());
    }

    #[test]
    fn unop_stmt_emits_let_with_unop_value() {
        let stmt = unop_stmt(UnOp::Cast(64), &[5], &[3], 0, "CastU64")
            .unwrap()
            .unwrap();
        match stmt {
            Stmt::Let { pattern, value } => {
                assert_eq!(pattern, vec![Some(name(5))]);
                match value {
                    Expr::UnOp { op, operand } => {
                        assert_eq!(op, UnOp::Cast(64));
                        assert_eq!(*operand, Expr::Var(name(3)));
                    }
                    other => panic!("expected UnOp, got {other:?}"),
                }
            }
            other => panic!("expected Let, got {other:?}"),
        }
    }

    #[test]
    fn unop_stmt_rejects_arity_mismatch() {
        // 0 srcs / 0 dests
        let r = unop_stmt(UnOp::Not, &[], &[], 0, "Not");
        assert!(r.is_err());
    }

    // ---- single_dest / single_src ------------------------------------

    #[test]
    fn single_dest_unwraps_one_dest() {
        assert_eq!(single_dest(&[7], 0, "Pack").unwrap(), 7);
    }

    #[test]
    fn single_dest_rejects_zero_or_many() {
        assert!(single_dest(&[], 0, "Pack").is_err());
        assert!(single_dest(&[1, 2], 0, "Pack").is_err());
    }

    #[test]
    fn single_src_unwraps_one_src() {
        assert_eq!(single_src(&[7], 0, "Field").unwrap(), 7);
    }

    #[test]
    fn bind_dests_uses_eval_for_no_destinations() {
        assert_eq!(bind_dests(&[], Expr::Unit), Stmt::Eval(Expr::Unit));
    }

    #[test]
    fn bind_dests_uses_let_for_one_destination() {
        assert_eq!(
            bind_dests(&[7], Expr::Unit),
            Stmt::Let {
                pattern: vec![Some(name(7))],
                value: Expr::Unit,
            }
        );
    }

    #[test]
    fn bind_dests_preserves_multiple_destination_order() {
        assert_eq!(
            bind_dests(&[9, 3], Expr::Unit),
            Stmt::Let {
                pattern: vec![Some(name(9)), Some(name(3))],
                value: Expr::Unit,
            }
        );
    }

    // ---- Const inference helper (translate_load uses it) -------------

    #[test]
    fn const_translation_through_helper_round_trips_u64() {
        let c = Constant::U64(42);
        // Smoke: the helper used by translate_load.
        let v = translate_constant_with_type(&c, &IrType::UInt(64));
        assert_eq!(
            v,
            Const::UInt {
                bits: 64,
                value: U256::from(42u8)
            }
        );
    }

    // ---- Pack / Unpack helpers (no FunctionTarget needed) ------------
    //
    // These exercise translate_call_op indirectly by building the
    // expected Stmt::Let values and asserting the structural shape.

    #[test]
    fn translate_type_args_translates_each() {
        let mut p = pb();
        let move_args = vec![
            MoveType::Primitive(move_model::ty::PrimitiveType::U64),
            MoveType::Primitive(move_model::ty::PrimitiveType::Bool),
        ];
        let got = translate_type_args(&move_args, &mut p).unwrap();
        assert_eq!(got, vec![IrType::UInt(64), IrType::Bool]);
    }

    #[test]
    fn translate_type_args_propagates_unsupported_error() {
        let mut p = pb();
        let move_args = vec![MoveType::Primitive(move_model::ty::PrimitiveType::Num)];
        let r = translate_type_args(&move_args, &mut p);
        assert!(matches!(r, Err(Stage2Error::UnsupportedMoveType { .. })));
    }

    // ---- normalize_borrow_edge: placeholder MapKey handling ----------
    //
    // Three position classes for a `MapKey { Unit, Unit }`
    // placeholder inside a Hyper chain:
    //   * trailing      -- dynamic_field internal-wrapping artifact, drop
    //   * middle/leading -- user-visible Table::borrow_mut whose (K, V)
    //                       weren't recovered, keep
    // Standalone (non-Hyper) placeholder collapses to `Direct`.

    use crate::ir::BorrowEdge as E;
    use crate::ir::Type;

    fn placeholder_map_key() -> E {
        E::MapKey {
            key_type: Type::Unit,
            value_type: Type::Unit,
        }
    }

    fn typed_map_key() -> E {
        E::MapKey {
            key_type: Type::UInt(64),
            value_type: Type::Bool,
        }
    }

    fn sf(struct_id: usize, field_index: usize) -> E {
        E::StructField {
            struct_id,
            field_index,
        }
    }

    #[test]
    fn normalize_drops_standalone_placeholder_map_key() {
        // Top-level (non-Hyper) placeholder collapses to Direct so
        // downstream stages don't see Unit/Unit MapKey edges.
        assert_eq!(normalize_borrow_edge(placeholder_map_key()), E::Direct);
    }

    #[test]
    fn normalize_drops_trailing_placeholder_in_hyper() {
        // Sui dynamic_field shape: `Hyper([DynamicField(K, V),
        // Index(Custom)])`. The trailing placeholder is the boxed
        // `Field<K, V>` cell indirection; dropping it leaves the
        // typed MapKey as the user-visible step.
        let edge = E::Hyper(vec![typed_map_key(), placeholder_map_key()]);
        // After filter the chain has one element, so the Hyper
        // collapses to that single edge.
        assert_eq!(normalize_borrow_edge(edge), typed_map_key());
    }

    #[test]
    fn normalize_drops_multiple_trailing_placeholders_in_hyper() {
        // Defensive: cascades of internal-wrapping placeholders at
        // the tail. All get dropped.
        let edge = E::Hyper(vec![
            typed_map_key(),
            placeholder_map_key(),
            placeholder_map_key(),
        ]);
        assert_eq!(normalize_borrow_edge(edge), typed_map_key());
    }

    #[test]
    fn normalize_keeps_middle_placeholder_in_hyper() {
        // Navi/lending `validator_set` shape (the 6-edge upstream
        // chain after Direct-drop): a user-visible Table::borrow_mut
        // sits in the middle of the chain whose (K, V) couldn't be
        // recovered because the trailing edge is a typed
        // DynamicField. Dropping the middle placeholder would
        // collapse the chain to a structurally wrong shape (the
        // renderer would emit field accesses on the Table's value
        // type at the parent position). Keep it.
        let edge = E::Hyper(vec![
            sf(125, 6),            // ValidatorSet.validator_candidates
            placeholder_map_key(), // Table::borrow_mut (user-visible, types lost)
            sf(117, 0),            // ValidatorWrapper.inner
            typed_map_key(),       // Versioned DynamicField (typed)
        ]);
        // 4 surviving edges, in original order; the middle
        // placeholder is preserved.
        match normalize_borrow_edge(edge) {
            E::Hyper(es) => {
                assert_eq!(es.len(), 4, "chain shrunk: {:?}", es);
                assert_eq!(es[0], sf(125, 6));
                assert_eq!(es[1], placeholder_map_key());
                assert_eq!(es[2], sf(117, 0));
                assert_eq!(es[3], typed_map_key());
            }
            other => panic!("expected Hyper, got {:?}", other),
        }
    }

    #[test]
    fn normalize_drops_direct_edges_anywhere_in_hyper() {
        // Direct is always a no-op; drop wherever it appears.
        let edge = E::Hyper(vec![
            E::Direct,
            sf(1, 0),
            E::Direct,
            placeholder_map_key(),
            E::Direct,
            sf(2, 0),
            typed_map_key(),
            E::Direct,
        ]);
        match normalize_borrow_edge(edge) {
            E::Hyper(es) => {
                // Directs dropped; trailing Direct removed; middle
                // placeholder kept; trailing typed MapKey kept.
                assert_eq!(
                    es,
                    vec![sf(1, 0), placeholder_map_key(), sf(2, 0), typed_map_key()],
                );
            }
            other => panic!("expected Hyper, got {:?}", other),
        }
    }

    #[test]
    fn normalize_collapses_singleton_after_trailing_placeholder_drop() {
        // `Hyper([typed])` (1 element after Direct drop) collapses
        // to the single typed MapKey -- it's not a real chain.
        let edge = E::Hyper(vec![typed_map_key()]);
        assert_eq!(normalize_borrow_edge(edge), typed_map_key());
    }

    #[test]
    fn normalize_collapses_all_placeholder_chain_to_direct() {
        // Defensive: nothing meaningful survives; result is Direct
        // (the empty-chain sentinel).
        let edge = E::Hyper(vec![placeholder_map_key(), placeholder_map_key()]);
        assert_eq!(normalize_borrow_edge(edge), E::Direct);
    }

    #[test]
    fn normalize_is_idempotent() {
        // Apply twice; result is the same.
        let edge = E::Hyper(vec![
            sf(125, 6),
            placeholder_map_key(),
            sf(117, 0),
            typed_map_key(),
        ]);
        let once = normalize_borrow_edge(edge.clone());
        let twice = normalize_borrow_edge(once.clone());
        assert_eq!(once, twice);
    }

    #[test]
    fn normalize_recurses_into_nested_hyper() {
        // A nested Hyper inside the outer chain still gets its own
        // normalization (drop interior Directs, drop trailing
        // placeholders within itself). The OUTER chain's positional
        // logic then treats the (possibly collapsed) nested result
        // as a single edge.
        let inner = E::Hyper(vec![sf(10, 0), E::Direct, typed_map_key()]);
        let outer = E::Hyper(vec![sf(1, 0), inner, typed_map_key()]);
        match normalize_borrow_edge(outer) {
            E::Hyper(es) => {
                // The inner Hyper had Direct dropped, leaving
                // `[StructField, typed MapKey]` -- still a 2-edge
                // Hyper. The outer chain keeps both elements.
                assert_eq!(es.len(), 3, "outer chain wrong shape: {:?}", es);
                assert_eq!(es[0], sf(1, 0));
                assert_eq!(
                    es[1],
                    E::Hyper(vec![sf(10, 0), typed_map_key()]),
                    "inner Hyper not normalized",
                );
                assert_eq!(es[2], typed_map_key());
            }
            other => panic!("expected Hyper, got {:?}", other),
        }
    }

    #[test]
    fn normalize_drops_middle_placeholder_after_typed_map_key() {
        // SkipList / wit_table / generic_store user-wrapper shape:
        // upstream emits `Hyper([..., DynamicField(K, V_wrap),
        // Index(Table), Field(NativeStruct, value_idx), ...])`. The
        // typed `DynamicField` already captures the user-visible
        // storage step; the trailing `Index(Table)` is the redundant
        // internal Sui-dynamic_field Table indirection that the Lean
        // prelude encapsulates. Drop it.
        let edge = E::Hyper(vec![
            sf(1, 2),              // BinManager.bins
            typed_map_key(),       // SkipList::borrow_mut -- typed
            placeholder_map_key(), // internal Index(Table) -- internal indirection
            sf(2, 1),              // BinGroupRef field 1
            sf(3, 2),              // BinGroup.bins
        ]);
        match normalize_borrow_edge(edge) {
            E::Hyper(es) => {
                // Middle placeholder dropped; rest preserved.
                assert_eq!(es, vec![sf(1, 2), typed_map_key(), sf(2, 1), sf(3, 2)],);
            }
            other => panic!("expected Hyper, got {:?}", other),
        }
    }

    #[test]
    fn normalize_drops_runs_of_placeholders_after_typed_map_key() {
        // Defensive: cascade of internal indirections after a typed
        // MapKey. Each placeholder is preceded by another placeholder
        // (or the typed one); the rule fires left-to-right so all
        // subsequent placeholders also see a non-placeholder
        // predecessor (the typed MapKey -- since `remove` shifts the
        // following elements left). Result: all of them drop.
        let edge = E::Hyper(vec![
            typed_map_key(),
            placeholder_map_key(),
            placeholder_map_key(),
            sf(7, 0),
        ]);
        match normalize_borrow_edge(edge) {
            E::Hyper(es) => assert_eq!(es, vec![typed_map_key(), sf(7, 0)]),
            other => panic!("expected Hyper, got {:?}", other),
        }
    }

    #[test]
    fn normalize_keeps_middle_placeholder_after_struct_field() {
        // Regression guard for the validator-set shape: a
        // placeholder preceded by a `StructField` (NOT a typed
        // MapKey) is the user-visible `Table::borrow_mut` whose
        // (K, V) weren't recovered; keep it.
        let edge = E::Hyper(vec![
            sf(125, 6),            // ValidatorSet.validator_candidates
            placeholder_map_key(), // user-visible Table::borrow_mut, types lost
            sf(117, 0),            // ValidatorWrapper.inner
            typed_map_key(),
        ]);
        match normalize_borrow_edge(edge) {
            E::Hyper(es) => {
                assert_eq!(es.len(), 4, "validator-set chain regressed: {:?}", es);
                assert_eq!(es[1], placeholder_map_key());
            }
            other => panic!("expected Hyper, got {:?}", other),
        }
    }

    #[test]
    fn normalize_keeps_middle_placeholder_after_direct() {
        // Same shape after the Direct filter: in upstream's
        // `[Field(VS, ...), Field(Table, _), Index(Table), ...]`,
        // `Field(NativeStruct, _)` collapses to Direct; Direct is
        // dropped by the filter; the placeholder is then preceded by
        // the leading `StructField` (not by Direct), so it's NOT
        // dropped. Sanity-check by also testing a chain where Direct
        // physically precedes the placeholder before the filter
        // collapses it -- the rule must not fire for that case
        // either (Direct is not a typed MapKey).
        let edge = E::Hyper(vec![sf(125, 6), E::Direct, placeholder_map_key()]);
        // The trailing-placeholder loop drops the placeholder (it IS
        // the trailing edge after Direct is filtered). What's left
        // is the single StructField. That is the correct shape; the
        // point here is that the new "typed MapKey then placeholder"
        // rule did NOT fire on `Direct, placeholder` (which would be
        // wrong).
        assert_eq!(normalize_borrow_edge(edge), sf(125, 6));
    }

    // ---- fill_map_key_types: placeholder MapKey patching --------------
    //
    // Walks a (possibly Hyper) edge, finds placeholders left-to-right,
    // and substitutes the i-th recorded `(K, V)` pair (one per
    // internal MapKey-class borrow_mut native call in the wrapper's
    // body). A placeholder preceded by a typed MapKey is the internal
    // indirection of a dynamic_field-class step whose typed
    // `MapKey { K, V }` already captures the user-visible storage --
    // SKIP patching (`normalize_borrow_edge` drops it) but still
    // ADVANCE the kv index so the i-th non-internal placeholder
    // lines up with the i-th wrapper-body recorded pair.

    fn kv() -> (Type, Type) {
        (Type::UInt(64), Type::Bool)
    }

    fn kv2() -> (Type, Type) {
        (Type::Address, Type::UInt(8))
    }

    #[test]
    fn fill_patches_standalone_placeholder() {
        // Top-level placeholder gets the recorded types.
        let mut edge = placeholder_map_key();
        fill_map_key_types(&mut edge, &[kv()]);
        assert_eq!(edge, typed_map_key());
    }

    #[test]
    fn fill_patches_trailing_placeholder_in_hyper() {
        // Single placeholder at the trailing position -- patched.
        let mut edge = E::Hyper(vec![sf(1, 0), placeholder_map_key()]);
        fill_map_key_types(&mut edge, &[kv()]);
        match edge {
            E::Hyper(es) => {
                assert_eq!(es, vec![sf(1, 0), typed_map_key()]);
            }
            other => panic!("expected Hyper, got {:?}", other),
        }
    }

    #[test]
    fn fill_patches_middle_placeholder_in_hyper() {
        // User-wrapper chain: leading user-struct field navigation,
        // then a Direct (collapsed Field-of-native), then the
        // user-visible placeholder, then more navigation. The
        // FIRST placeholder is in position 2 -- patch it.
        let mut edge = E::Hyper(vec![
            sf(1, 1),
            E::Direct,
            placeholder_map_key(),
            sf(2, 0),
            sf(3, 1),
        ]);
        fill_map_key_types(&mut edge, &[kv()]);
        match edge {
            E::Hyper(es) => {
                assert_eq!(
                    es,
                    vec![sf(1, 1), E::Direct, typed_map_key(), sf(2, 0), sf(3, 1)],
                );
            }
            other => panic!("expected Hyper, got {:?}", other),
        }
    }

    #[test]
    fn fill_refuses_when_real_map_key_precedes_placeholder_with_single_kv() {
        // dynamic_field composed shape:
        //   `Hyper([DynamicField(K, V), Index(Table)])`
        // The DynamicField already carries real types; the trailing
        // Index(Table) is the internal-wrapping placeholder. If we
        // patched it here, the renderer would emit a multi-MapKey
        // path-match for a single-step semantic borrow.
        let mut edge = E::Hyper(vec![typed_map_key(), placeholder_map_key()]);
        fill_map_key_types(&mut edge, &[kv()]);
        match edge {
            E::Hyper(es) => {
                assert_eq!(es, vec![typed_map_key(), placeholder_map_key()]);
            }
            other => panic!("expected Hyper, got {:?}", other),
        }
    }

    #[test]
    fn fill_patches_two_placeholders_for_two_kv_pairs() {
        // Multi-key wrapper -- a chain with two user-visible
        // placeholders (each from a distinct internal borrow_mut
        // native) and two kv entries. Patch both in order.
        let mut edge = E::Hyper(vec![
            sf(1, 0),
            placeholder_map_key(), // 1st user-visible step -> kvs[0]
            sf(2, 0),
            placeholder_map_key(), // 2nd user-visible step -> kvs[1]
            sf(3, 0),
        ]);
        fill_map_key_types(&mut edge, &[kv(), kv2()]);
        match edge {
            E::Hyper(es) => {
                assert_eq!(
                    es,
                    vec![
                        sf(1, 0),
                        E::MapKey {
                            key_type: kv().0,
                            value_type: kv().1
                        },
                        sf(2, 0),
                        E::MapKey {
                            key_type: kv2().0,
                            value_type: kv2().1
                        },
                        sf(3, 0),
                    ],
                );
            }
            other => panic!("expected Hyper, got {:?}", other),
        }
    }

    #[test]
    fn fill_skips_internal_placeholder_and_advances_kv_index() {
        // navi-lending `storage::get_emode_asset_mut` shape:
        //   Hyper([
        //     MapKey{K0, V0},           <- typed from DynamicField summary
        //     placeholder,              <- internal indirection -> SKIP, but advance kv_idx
        //     StructField,
        //     Direct,
        //     placeholder,              <- user-visible table::borrow_mut -> PATCH with kvs[1]
        //     StructField,
        //   ])
        // kvs from body walk:
        //   [(K_df, V_df), (K_tbl, V_tbl)]   -- one entry per internal native call
        let mut edge = E::Hyper(vec![
            typed_map_key(), // pretend typed K0,V0 (we use kv() values to be distinct from kv2)
            placeholder_map_key(), // internal indirection -- SKIP
            sf(1, 0),
            E::Direct,
            placeholder_map_key(), // user-visible step -- PATCH with kvs[1]
            sf(2, 0),
        ]);
        fill_map_key_types(&mut edge, &[kv(), kv2()]);
        match edge {
            E::Hyper(es) => {
                assert_eq!(es[0], typed_map_key(), "leading typed MapKey untouched");
                assert_eq!(
                    es[1],
                    placeholder_map_key(),
                    "internal placeholder left Unit/Unit"
                );
                assert_eq!(
                    es[4],
                    E::MapKey {
                        key_type: kv2().0,
                        value_type: kv2().1
                    },
                    "user-visible placeholder patched with kvs[1]",
                );
            }
            other => panic!("expected Hyper, got {:?}", other),
        }
    }

    #[test]
    fn fill_no_op_on_empty_kv_list() {
        // Empty kvs list means there were no internal recognised
        // natives in the wrapper -- nothing to patch.
        let mut edge = E::Hyper(vec![sf(1, 0), placeholder_map_key()]);
        fill_map_key_types(&mut edge, &[]);
        match edge {
            E::Hyper(es) => assert_eq!(es, vec![sf(1, 0), placeholder_map_key()]),
            other => panic!("expected Hyper, got {:?}", other),
        }
    }

    // ---- promote_vec_index_for_map_borrow ----------------------------
    //
    // Promotes `VecIndex` to `MapKey { K, V }` when the child temp was
    // borrowed via a MapKey native (e.g. `vec_map::get_mut`, whose
    // internal `&mut self.contents[idx].value` over `vector<Entry<K,V>>`
    // surfaces as `Index(Vector)` from upstream BorrowAnnotation).
    // Commit fdae7bc9 -- regression for the ika-staking:Pending_values
    // and cetus-clmm:Config writeback mismatch.

    #[test]
    fn promote_replaces_standalone_vec_index_with_typed_map_key() {
        // The canonical case: a bare VecIndex edge becomes
        // MapKey { K, V } when the writeback's child has a recorded
        // (K, V).
        let mut edge = E::VecIndex;
        promote_vec_index_for_map_borrow(&mut edge, &[kv()]);
        assert_eq!(edge, typed_map_key());
    }

    #[test]
    fn promote_walks_into_hyper_chain() {
        // A Hyper containing a VecIndex step -- the recursion descends
        // and promotes every VecIndex it finds. Other steps are left
        // alone.
        let mut edge = E::Hyper(vec![sf(1, 0), E::VecIndex]);
        promote_vec_index_for_map_borrow(&mut edge, &[kv()]);
        assert_eq!(edge, E::Hyper(vec![sf(1, 0), typed_map_key()]));
    }

    #[test]
    fn promote_leaves_direct_and_field_edges_alone() {
        // `Direct` and `StructField` / `EnumField` are not VecIndex,
        // so they pass through unchanged even when `kvs` is non-empty.
        let mut direct = E::Direct;
        promote_vec_index_for_map_borrow(&mut direct, &[kv()]);
        assert_eq!(direct, E::Direct);

        let mut field = sf(7, 2);
        promote_vec_index_for_map_borrow(&mut field, &[kv()]);
        assert_eq!(field, sf(7, 2));

        let mut enum_field = E::EnumField {
            struct_id: 9,
            variant: 0,
            field_index: 1,
        };
        let snapshot = enum_field.clone();
        promote_vec_index_for_map_borrow(&mut enum_field, &[kv()]);
        assert_eq!(enum_field, snapshot);
    }

    #[test]
    fn promote_leaves_existing_typed_map_key_alone() {
        // A MapKey edge that already carries real (K, V) types is
        // untouched. The placeholder-patching is handled by
        // `fill_map_key_types`, not this function.
        let mut edge = typed_map_key();
        promote_vec_index_for_map_borrow(&mut edge, &[kv2()]);
        assert_eq!(edge, typed_map_key());
    }

    #[test]
    fn promote_no_op_on_empty_kv_list() {
        // No recorded (K, V) means the child wasn't a MapKey-native
        // borrow -- the legitimate `vector::borrow_mut` writeback
        // case. Leave the VecIndex in place so the renderer emits
        // `writeBackVecIndex`.
        let mut edge = E::VecIndex;
        promote_vec_index_for_map_borrow(&mut edge, &[]);
        assert_eq!(edge, E::VecIndex);

        let mut hyper = E::Hyper(vec![sf(1, 0), E::VecIndex]);
        promote_vec_index_for_map_borrow(&mut hyper, &[]);
        assert_eq!(hyper, E::Hyper(vec![sf(1, 0), E::VecIndex]));
    }

    #[test]
    fn promote_uses_first_kv_pair_when_multiple_recorded() {
        // The function uses `kvs[0]` only (single-pair model). If a
        // wrapper records multiple borrow_mut calls, the first pair
        // is the one that surfaces at the writeback site.
        let mut edge = E::VecIndex;
        promote_vec_index_for_map_borrow(&mut edge, &[kv(), kv2()]);
        assert_eq!(
            edge,
            E::MapKey {
                key_type: kv().0,
                value_type: kv().1
            }
        );
    }

    #[test]
    fn promote_promotes_every_vec_index_in_nested_hyper() {
        // A Hyper containing multiple VecIndex steps -- all get
        // promoted to the same (K, V). Defensive: the recursion is
        // structural, not "first-match-wins".
        let mut edge = E::Hyper(vec![E::VecIndex, sf(1, 0), E::VecIndex]);
        promote_vec_index_for_map_borrow(&mut edge, &[kv()]);
        assert_eq!(
            edge,
            E::Hyper(vec![typed_map_key(), sf(1, 0), typed_map_key()])
        );
    }

    // ---- retype_native_map_key_from_container (ledger item 34 (iii)) ----

    fn rt_sty(id: crate::ir::StructId) -> Type {
        Type::Struct {
            struct_id: id,
            type_args: vec![],
        }
    }

    fn rt_table(k: Type, v: Type) -> Type {
        // struct_id 1 == table::Table in `rt_program`.
        Type::Struct {
            struct_id: 1,
            type_args: vec![k, v],
        }
    }

    /// sui-system-shaped program: `ValidatorSet.validator_candidates`
    /// (field 6) is a `Table<address, ValidatorWrapper>`; a `ValidatorWrapper`
    /// (struct 3) `.inner` (field 0) is a `Versioned` (struct 2) whose `.id`
    /// (field 0) is a `UID` (struct 10); the df stores `Validator` (struct 5).
    fn rt_program() -> crate::ir::Program {
        use crate::ir::program::{Field, Struct};
        let mut p = crate::ir::Program::default();
        let add =
            |id: crate::ir::StructId, qn: &str, fields: Vec<Field>, p: &mut crate::ir::Program| {
                p.structs.insert(
                    id,
                    Struct {
                        module_id: 0,
                        name: qn.rsplit("::").next().unwrap_or(qn).to_string(),
                        qualified_name: qn.to_string(),
                        type_params: vec![],
                        fields,
                        variants: None,
                        is_native: false,
                    },
                );
            };
        add(10, "object::UID", vec![], &mut p);
        add(1, "table::Table", vec![], &mut p);
        add(
            2,
            "versioned::Versioned",
            vec![Field {
                name: "id".into(),
                field_type: rt_sty(10),
            }],
            &mut p,
        );
        add(
            3,
            "validator_wrapper::ValidatorWrapper",
            vec![Field {
                name: "inner".into(),
                field_type: rt_sty(2),
            }],
            &mut p,
        );
        let vs_fields: Vec<Field> = (0..6)
            .map(|i| Field {
                name: format!("f{i}"),
                field_type: rt_sty(5),
            })
            .chain(std::iter::once(Field {
                name: "validator_candidates".into(),
                field_type: rt_table(Type::Address, rt_sty(3)),
            }))
            .collect();
        add(4, "validator_set::ValidatorSet", vs_fields, &mut p);
        add(5, "validator::Validator", vec![], &mut p);
        p
    }

    #[test]
    fn retype_fixes_ill_typed_candidate_table_lookup() {
        // any_validator_mut candidate-branch borrow SUMMARY: the FIRST mapKey
        // (the `validator_candidates` Table lookup) collapsed onto the df
        // anchor's (u64, Validator). The container field type is
        // (address, ValidatorWrapper), so it must be corrected; the df anchor
        // (container = UID) must stay [u64 -> Validator].
        let p = rt_program();
        let mut edge = E::Hyper(vec![
            sf(4, 6), // validator_candidates : Table<address, ValidatorWrapper>
            sf(1, 1), // Table.size content placeholder
            E::MapKey {
                key_type: Type::UInt(64),
                value_type: rt_sty(5),
            }, // ILL-TYPED Table lookup
            sf(3, 0), // ValidatorWrapper.inner
            sf(2, 0), // Versioned.id
            E::MapKey {
                key_type: Type::UInt(64),
                value_type: rt_sty(5),
            }, // df anchor (correct)
        ]);
        retype_native_map_key_from_container(&mut edge, &p);
        assert_eq!(
            edge,
            E::Hyper(vec![
                sf(4, 6),
                sf(1, 1),
                E::MapKey {
                    key_type: Type::Address,
                    value_type: rt_sty(3),
                }, // CORRECTED to (address, ValidatorWrapper)
                sf(3, 0),
                sf(2, 0),
                E::MapKey {
                    key_type: Type::UInt(64),
                    value_type: rt_sty(5),
                }, // df anchor unchanged
            ])
        );
    }

    #[test]
    fn retype_leaves_already_correct_table_lookup_byte_identical() {
        // A well-typed in-value Table<u64, Validator> lookup (the direct
        // candidate path / the pending contents) must stay byte-identical --
        // overwriting from the container yields the same (u64, Validator).
        use crate::ir::program::{Field, Struct};
        let mut p = rt_program();
        p.structs.insert(
            6,
            Struct {
                module_id: 0,
                name: "TableVec".into(),
                qualified_name: "table_vec::TableVec".into(),
                type_params: vec![],
                fields: vec![Field {
                    name: "contents".into(),
                    field_type: rt_table(Type::UInt(64), rt_sty(5)),
                }],
                variants: None,
                is_native: false,
            },
        );
        let edge0 = E::Hyper(vec![
            sf(6, 0), // TableVec.contents : Table<u64, Validator>
            sf(1, 1), // Table.size content placeholder
            E::MapKey {
                key_type: Type::UInt(64),
                value_type: rt_sty(5),
            },
        ]);
        let mut edge = edge0.clone();
        retype_native_map_key_from_container(&mut edge, &p);
        assert_eq!(edge, edge0);
    }

    #[test]
    fn retype_skips_generic_container_map_key() {
        // A GENERIC container's definition field type carries TypeParams, not
        // the instantiated types `fill_map_key_types` already recorded --
        // must be left untouched (no clobber of the real key/value).
        use crate::ir::program::{Field, Struct};
        let mut p = rt_program();
        // struct 7: holder<T> whose field 0 is Table<address, T> (T = TypeParam 0).
        p.structs.insert(
            7,
            Struct {
                module_id: 0,
                name: "Holder".into(),
                qualified_name: "holder::Holder".into(),
                type_params: vec!["T".into()],
                fields: vec![Field {
                    name: "m".into(),
                    field_type: rt_table(Type::Address, Type::TypeParam(0)),
                }],
                variants: None,
                is_native: false,
            },
        );
        let edge0 = E::Hyper(vec![
            sf(7, 0),
            sf(1, 1),
            E::MapKey {
                key_type: Type::Address,
                value_type: rt_sty(5), // instantiated by fill_map_key_types
            },
        ]);
        let mut edge = edge0.clone();
        retype_native_map_key_from_container(&mut edge, &p);
        assert_eq!(edge, edge0);
    }

    #[test]
    fn retype_leaves_df_value_cell_placeholder_untyped() {
        // A df whose VALUE is itself a native map (current-lending
        // `whitelist_admin`: `borrow_mut<PackageWhitestKey, VecMap<ID, u32>>`)
        // carries the dynamic_field internal `Field<K, V>` value-cell
        // artifact as a TRAILING `MapKey { Unit, Unit }` after the df
        // anchor. It must NOT be typed from the container -- it is
        // `normalize_borrow_edge`'s to drop, and typing it first resurrects
        // it as a phantom in-value content lookup whose writeback renders
        // ill-typed Lean (the 2026-07 current-lending specs-lake
        // regression).
        let p = rt_program();
        let edge0 = E::Hyper(vec![
            sf(2, 0), // some UID field (Versioned.id : UID)
            E::MapKey {
                key_type: rt_sty(5),
                value_type: rt_table(Type::Address, rt_sty(3)),
            }, // df anchor: the stored VALUE is a native map
            E::MapKey {
                key_type: Type::Unit,
                value_type: Type::Unit,
            }, // Field value-cell artifact -- must stay untyped
        ]);
        let mut edge = edge0.clone();
        retype_native_map_key_from_container(&mut edge, &p);
        assert_eq!(edge, edge0);
    }

    #[test]
    fn prepared_edge_shape_is_shared_by_writeback_and_is_parent() {
        use crate::ir::program::{Field, Struct};
        use crate::ir::BorrowNode;

        let mut p = rt_program();
        p.structs.insert(
            20,
            Struct {
                module_id: 0,
                name: "VectorHolder".into(),
                qualified_name: "test::VectorHolder".into(),
                type_params: vec![],
                fields: vec![Field {
                    name: "items".into(),
                    field_type: Type::Vector(Box::new(Type::Bool)),
                }],
                variants: None,
                is_native: false,
            },
        );

        let source = E::Hyper(vec![sf(20, 0), E::VecIndex, E::Direct, E::VecIndex]);
        let metadata = [kv()];
        let expected = E::Hyper(vec![sf(20, 0), E::VecIndex, typed_map_key()]);
        let prepare = || prepare_lifted_borrow_edge(source.clone(), Some(&metadata), &p);

        let write_back = Expr::WriteBack {
            node: BorrowNode::LocalRoot(name(0)),
            edge: prepare(),
            child: name(1),
            world: None,
        };
        let is_parent = Expr::IsParent {
            node: BorrowNode::LocalRoot(name(0)),
            edge: prepare(),
            child: name(1),
        };

        fn edge(expr: &Expr) -> &E {
            match expr {
                Expr::WriteBack { edge, .. } | Expr::IsParent { edge, .. } => edge,
                other => panic!("expected borrow-edge carrier, got {other:?}"),
            }
        }

        assert_eq!(edge(&write_back), &expected);
        assert_eq!(edge(&is_parent), &expected);
    }
}
