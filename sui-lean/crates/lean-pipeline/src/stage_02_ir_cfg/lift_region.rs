//! Per-Region structurer.
//!
//! Walks a [`BytecodeCfg`](crate::stage_01_bytecode_cfg::BytecodeCfg)
//! produced by stage 1 and lifts every node into IR. Each
//! [`Region`](crate::stage_01_bytecode_cfg::Region) becomes a
//! [`Block`] (potentially preceded by zero or more `Stmt`s pushed
//! into the surrounding block); each
//! [`Termination`](crate::stage_01_bytecode_cfg::Termination)
//! becomes the matching [`BlockTail`] variant.
//!
//! ## Natural-exit synthesis
//!
//! When a Region ends without an explicit `Term`, the surrounding
//! context fills in the tail:
//!
//! | Context | Synthesised tail |
//! |---|---|
//! | Function body tail | `BlockTail::Value(Unit)` (Move's implicit return-unit) |
//! | `Expr::While::body` tail | `BlockTail::Continue { level: 0, value: Unit }` |
//! | `Expr::If` / `Expr::Match` arm tail | `BlockTail::Value(Unit)` (the merge value comes from the arm's last expression; Unit when the arm has no value) |
//!
//! Stage 4's SSA pass refines arm-tail values into the actual phi
//! merge value; stage 6 strips the synthesised tails entirely.
//!
//! ## Implementation status
//!
//! - `Region::Basic` / `Region::Seq` / `Region::Term` / `Region::If`
//!   / `Region::Switch` / `Region::While` are all handled by this
//!   module. `Region::While` lifts (via `lift_while`) into the
//!   [`Expr::While`](crate::ir::Expr::While) `{ header, cond, body,
//!   iter_locals, live_out }` shape (§17): the stage-1
//!   `Region::While { header, cond_at, body }` maps directly, with the
//!   per-iteration header re-execution preserved.
//!
//! ## Borrow-state threading
//!
//! Each recursive call carries a [`BorrowState`] that flows
//! sequentially through `Region::Basic` / `Region::Seq` and is
//! **cloned at branch points** (`If` arms, `Switch` arms,
//! `While` body) so each branch sees the borrow state at the
//! split-point and forks independently. This matches the
//! basic-block successor structure of the underlying CFG.

use move_binary_format::file_format::CodeOffset;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::Bytecode;

use crate::ir::{Block, BlockTail, Expr, MatchArm, ProgramBuilder, Stmt};
use crate::stage_01_bytecode_cfg::{Region, Termination};

use super::translate_op::{temp_name, translate_basic_bytecode_stmts, TranslateCtx};
use super::Stage2Error;

/// The canonical "this region falls off the end" tail. Stage 2's
/// `lift_region` uses this whenever a Region produces no explicit
/// `Term`. Uniform across all positions (function body, while body,
/// if/match arm).
fn fall_through_tail() -> BlockTail {
    BlockTail::Value(Expr::Unit)
}

/// Lift a stage-1 [`Region`] tree into an IR [`Block`].
pub fn lift_region(
    region: &Region,
    code: &[Bytecode],
    target: &FunctionTarget,
    prog: &mut ProgramBuilder,
    borrow_mut_kv: &mut std::collections::BTreeMap<
        crate::ir::VarId,
        Vec<(crate::ir::Type, crate::ir::Type)>,
    >,
) -> Result<Block, Stage2Error> {
    match region {
        // ---- Basic: walk PC range -----------------------------------
        Region::Basic { lower, upper } => {
            let stmts = lift_basic_range(*lower, *upper, code, target, prog, borrow_mut_kv)?;
            Ok(Block {
                stmts,
                tail: fall_through_tail(),
            })
        }

        // ---- Seq: concatenate children -----------------------------
        Region::Seq(children) => lift_seq(children, code, target, prog, borrow_mut_kv),

        // ---- Term: explicit termination -----------------------------
        Region::Term(term) => Ok(Block {
            stmts: Vec::new(),
            tail: lift_termination(term),
        }),

        // ---- If: post-dom-recursed two-way -------------------------
        Region::If {
            cond_at,
            then_branch,
            else_branch,
        } => {
            let cond_temp = read_branch_cond(*cond_at, code)?;
            let then_block = lift_region(then_branch, code, target, prog, borrow_mut_kv)?;
            let else_block = lift_region(else_branch, code, target, prog, borrow_mut_kv)?;
            let if_expr = Expr::If {
                cond: Box::new(Expr::Var(temp_name(cond_temp))),
                then_branch: Box::new(then_block),
                else_branch: Box::new(else_block),
            };
            Ok(Block {
                stmts: vec![Stmt::Eval(if_expr)],
                tail: fall_through_tail(),
            })
        }

        Region::Switch {
            switch_at,
            branches,
        } => lift_switch(*switch_at, branches, code, target, prog, borrow_mut_kv),

        Region::While {
            header,
            cond_at,
            body,
            negate_cond,
        } => lift_while(
            header,
            *cond_at,
            body,
            *negate_cond,
            code,
            target,
            prog,
            borrow_mut_kv,
        ),

        // ---- LabeledBlock: lift to Expr::LabeledBlock ----------------
        //
        // The block is lifted recursively; its `Value(_)` tail gives
        // the natural-exit value (and dictates `result_ty`).
        // `Termination::ReturnFromBlock { level, temps }` inside lifts
        // to `BlockTail::ReturnFromBlock { level, value: value_from_temps(temps) }`
        // (handled in `lift_termination`).
        //
        // We don't statically infer `result_ty` here — the stage 02
        // postcondition could do that later by walking exits and
        // intersecting types. For now we leave it `Type::Unit` and
        // expect stage 07's helper extraction (which is the next
        // consumer that cares) to derive the type from the helper
        // function signature.
        Region::LabeledBlock { body } => {
            let body_block = lift_region(body, code, target, prog, borrow_mut_kv)?;
            let labeled = Expr::LabeledBlock {
                body: Box::new(body_block),
                result_ty: crate::ir::Type::Unit,
            };
            Ok(Block {
                stmts: vec![Stmt::Eval(labeled)],
                tail: fall_through_tail(),
            })
        }
    }
}

/// Walk a `Region::Seq` left-to-right, concatenating children's
/// stmts. The final tail is the last child's tail; if the last
/// child has no explicit term, the surrounding `ctx`'s natural
/// tail wins.
fn lift_seq(
    children: &[Region],
    code: &[Bytecode],
    target: &FunctionTarget,
    prog: &mut ProgramBuilder,
    borrow_mut_kv: &mut std::collections::BTreeMap<
        crate::ir::VarId,
        Vec<(crate::ir::Type, crate::ir::Type)>,
    >,
) -> Result<Block, Stage2Error> {
    let mut stmts = Vec::new();
    let mut tail = fall_through_tail();
    for child in children.iter() {
        let block = lift_region(child, code, target, prog, borrow_mut_kv)?;
        stmts.extend(block.stmts);
        tail = block.tail;
    }
    Ok(Block { stmts, tail })
}

/// Walk PCs `lower..=upper` and translate each Bytecode into 0+ IR
/// statements. Pure forward iteration through the Basic block range.
fn lift_basic_range(
    lower: CodeOffset,
    upper: CodeOffset,
    code: &[Bytecode],
    target: &FunctionTarget,
    prog: &mut ProgramBuilder,
    borrow_mut_kv: &mut std::collections::BTreeMap<
        crate::ir::VarId,
        Vec<(crate::ir::Type, crate::ir::Type)>,
    >,
) -> Result<Vec<Stmt>, Stage2Error> {
    let mut stmts = Vec::new();
    let mut ctx = TranslateCtx {
        target,
        prog,
        borrow_mut_kv,
    };
    for pc in lower..=upper {
        let bc = code.get(pc as usize).ok_or(Stage2Error::NotImplemented {
            reason: "lift_region::lookup_bytecode",
        })?;
        stmts.extend(translate_basic_bytecode_stmts(bc, &mut ctx)?);
    }
    Ok(stmts)
}

/// Translate a stage-1 `Termination` to an IR `BlockTail`.
pub fn lift_termination(term: &Termination) -> BlockTail {
    match term {
        Termination::Return { temps } => BlockTail::Return(Box::new(value_from_temps(temps))),
        Termination::Abort { code_temp } => BlockTail::Abort {
            code: Box::new(match code_temp {
                Some(t) => Expr::Var(temp_name(*t)),
                // Synthesised aborts use `Const::UInt(0)` per design
                // decision-log §5 ("synthesised aborts use
                // `Const::UInt 0` rather than `None`").
                None => Expr::Const(crate::ir::Const::UInt {
                    bits: 64,
                    value: ethnum::U256::ZERO,
                }),
            }),
        },
        Termination::Break { level } => BlockTail::Break {
            level: *level,
            value: Box::new(Expr::Unit),
        },
        Termination::Continue { level } => BlockTail::Continue {
            level: *level,
            value: Box::new(Expr::Unit),
        },
        Termination::ReturnFromBlock { level, temps } => BlockTail::ReturnFromBlock {
            level: *level,
            value: Box::new(value_from_temps(temps)),
        },
    }
}

/// Build the return value for a `Bytecode::Ret(temps)`:
///
/// - 0 temps -> `Expr::Unit`
/// - 1 temp  -> `Expr::Var($tN)`
/// - N temps -> `Expr::Tuple([Var($tN), ...])`
fn value_from_temps(temps: &[move_stackless_bytecode::ast::TempIndex]) -> Expr {
    match temps.len() {
        0 => Expr::Unit,
        1 => Expr::Var(temp_name(temps[0])),
        _ => Expr::Tuple(temps.iter().map(|t| Expr::Var(temp_name(*t))).collect()),
    }
}

/// Read the cond temp from the `Bytecode::Branch` at `pc`. The
/// stage-1 structurer guarantees `cond_at` points at a `Branch`.
fn read_branch_cond(pc: CodeOffset, code: &[Bytecode]) -> Result<usize, Stage2Error> {
    match code.get(pc as usize) {
        Some(Bytecode::Branch(_, _, _, cond)) => Ok(*cond),
        _ => Err(Stage2Error::NotImplemented {
            reason: "lift_region fallthrough",
        }),
    }
}

/// Lift a `Region::While` to `Expr::While { header, cond, body }`.
///
/// - `header`'s natural exit synthesises `BlockTail::Value(Unit)`,
///   which is exactly what the validator requires for a header. The
///   header
///   region from stage 1 is the per-iteration cond-computation
///   prefix; in well-formed shapes it never ends in an explicit
///   `Term`.
/// - `cond` is read directly from the `Bytecode::Branch` at
///   `cond_at`: the branch's condition temp becomes
///   `Expr::Var($t<cond_temp>)`.
/// - `body`'s natural exit synthesises `BlockTail::Value(Unit)` --
///   same as the header. Stage 5's `normalize_body_tail` installs the
///   loop_state Tuple at the body's outermost Value(Unit) tail.
///   Explicit `Term(Break/Continue)` regions inside the body still
///   lift to the matching `BlockTail`.
///
/// Borrow state is **cloned** at the loop boundary so changes inside
/// the loop don't leak into the post-loop block. (At loop exit the
/// outer state matches the pre-loop snapshot; refining this to track
/// values that survive through Break is stage 4's job.)
fn lift_while(
    header: &Region,
    cond_at: CodeOffset,
    body: &Region,
    negate_cond: bool,
    code: &[Bytecode],
    target: &FunctionTarget,
    prog: &mut ProgramBuilder,
    borrow_mut_kv: &mut std::collections::BTreeMap<
        crate::ir::VarId,
        Vec<(crate::ir::Type, crate::ir::Type)>,
    >,
) -> Result<Block, Stage2Error> {
    let header_block = lift_region(header, code, target, prog, borrow_mut_kv)?;
    let cond_temp = read_branch_cond(cond_at, code)?;
    let body_block = lift_region(body, code, target, prog, borrow_mut_kv)?;

    // `negate_cond` (the `loop { if C break }` shape): the deciding
    // branch's TRUE target is the loop EXIT, so the branch cond is the
    // BREAK guard. `Expr::While.cond` is the CONTINUE predicate -> emit
    // `!cond_temp`. The normal `while (c)` shape (TRUE -> body) keeps it.
    let cond_expr = if negate_cond {
        Expr::UnOp {
            op: crate::ir::UnOp::Not,
            operand: Box::new(Expr::Var(temp_name(cond_temp))),
        }
    } else {
        Expr::Var(temp_name(cond_temp))
    };
    let while_expr = Expr::While {
        iter_locals: Vec::new(),
        header: Box::new(header_block),
        cond: Box::new(cond_expr),
        body: Box::new(body_block),
        header_exit_locals: Vec::new(),
        live_out: Vec::new(),
    };
    Ok(Block {
        stmts: vec![Stmt::Eval(while_expr)],
        tail: fall_through_tail(),
    })
}

/// Lift a `Region::Switch` to `Expr::Match`. Reads the selector temp
/// from the `Bytecode::VariantSwitch` at `switch_at`, looks up the
/// enum's variants in the GlobalEnv, and translates each arm.
///
/// Per-arm bindings: try **UnpackVariant hoisting** first (the
/// common case where the bytecode optimiser emits an UnpackVariant
/// at the head of each arm matching the arm's variant). When the
/// arm has no unpack prefix, fall back to **synthetic bindings**
/// `_v0..._v{n-1}` matching the variant's field count. A present but
/// mismatched unpack prefix is malformed.
fn lift_switch(
    switch_at: CodeOffset,
    branches: &[Region],
    code: &[Bytecode],
    target: &FunctionTarget,
    prog: &mut ProgramBuilder,
    borrow_mut_kv: &mut std::collections::BTreeMap<
        crate::ir::VarId,
        Vec<(crate::ir::Type, crate::ir::Type)>,
    >,
) -> Result<Block, Stage2Error> {
    let selector_temp = match code.get(switch_at as usize) {
        Some(Bytecode::VariantSwitch(_, t, _)) => *t,
        _ => {
            return Err(Stage2Error::NotImplemented {
                reason: "lift_region::peel_enum non-enum type",
            })
        }
    };

    // Look up the enum from the selector temp's Move type. Move's
    // VariantSwitch operates on either `Enum` or `&Enum` / `&mut Enum`
    // (after upstream's memory instrumentation we usually see the
    // value form, but reference forms can survive).
    let selector_move_ty = target.get_local_type(selector_temp).clone();
    let (enum_module_id, enum_datatype_id) = peel_enum(&selector_move_ty)?;

    let env = target.global_env();
    let enum_module = env.get_module(enum_module_id);
    let enum_env = enum_module.into_enum(enum_datatype_id);
    let variant_layout = variant_layout_in_tag_order(
        enum_env
            .get_variants()
            .map(|variant| (variant.get_tag(), variant.get_fields().count()))
            .collect(),
    );
    let variant_count = variant_layout.len();
    if branches.len() != variant_count {
        return Err(Stage2Error::MalformedArity {
            op: "VariantSwitch".to_string(),
            slot: "branches".to_string(),
            expected: variant_count,
            actual: branches.len(),
            pc: switch_at,
        });
    }

    let mut cases = Vec::with_capacity(branches.len());
    for (branch_index, ((tag, field_count), branch)) in
        variant_layout.into_iter().zip(branches).enumerate()
    {
        let arm = lift_match_arm(
            branch,
            switch_at,
            branch_index,
            selector_temp,
            enum_module_id,
            enum_datatype_id,
            tag,
            field_count,
            code,
            target,
            prog,
            borrow_mut_kv,
        )?;
        cases.push(arm);
    }

    let qid = move_model::model::QualifiedId {
        module_id: enum_module_id,
        id: enum_datatype_id,
    };
    let struct_id = prog.struct_id(qid);
    let match_expr = Expr::Match {
        struct_id,
        selector: Box::new(Expr::Var(temp_name(selector_temp))),
        cases,
    };
    // Uniform: `Stmt::Eval(match)` + `Value(Unit)` tail. The
    // `canonicalize_terminators` pass hoists terminating-arm Match
    // into the surrounding block's `tail` slot.
    Ok(Block {
        stmts: vec![Stmt::Eval(match_expr)],
        tail: fall_through_tail(),
    })
}

fn variant_layout_in_tag_order(mut variants: Vec<(usize, usize)>) -> Vec<(usize, usize)> {
    variants.sort_unstable_by_key(|(tag, _)| *tag);
    variants
}

/// Lift a single arm of a `Region::Switch`.
///
/// Try UnpackVariant hoisting:
/// 1. Recurse into the branch to find the first `Region::Basic`.
/// 2. Look at the first PC in that Basic's range.
/// 3. If it's `UnpackVariant(_, _, _, _, _)` whose tag matches
///    `expected_tag`, hoist its dest temps as `MatchArm::bindings`
///    and skip that bytecode in the body lift.
///
/// When no UnpackVariant is present, synthesise bindings
/// `_v0..._v{n-1}` matching `expected_field_count`. A leading
/// UnpackVariant with the wrong enum, tag, source, or arity is malformed
/// rather than a synthetic-binding case.
fn lift_match_arm(
    branch: &Region,
    switch_at: CodeOffset,
    branch_index: usize,
    selector_temp: move_stackless_bytecode::ast::TempIndex,
    enum_module_id: move_model::model::ModuleId,
    enum_datatype_id: move_model::model::DatatypeId,
    expected_tag: usize,
    expected_field_count: usize,
    code: &[Bytecode],
    target: &FunctionTarget,
    prog: &mut ProgramBuilder,
    borrow_mut_kv: &mut std::collections::BTreeMap<
        crate::ir::VarId,
        Vec<(crate::ir::Type, crate::ir::Type)>,
    >,
) -> Result<MatchArm, Stage2Error> {
    let hoisted = try_hoist_unpack_variant(
        branch,
        selector_temp,
        enum_module_id,
        enum_datatype_id,
        expected_tag,
        expected_field_count,
        code,
        target,
    )
    .map_err(|()| Stage2Error::MalformedMatchArm {
        switch_at,
        branch_index,
    })?;
    let (bindings, body_branch) = match hoisted {
        Some((dest_temps, rewritten)) => {
            let bindings: Vec<crate::ir::VarId> =
                dest_temps.iter().map(|t| temp_name(*t)).collect();
            (bindings, rewritten)
        }
        None => {
            let bindings: Vec<crate::ir::VarId> = (0..expected_field_count)
                .map(|i| format!("_v{i}").into())
                .collect();
            (bindings, branch.clone())
        }
    };

    let body = lift_region(&body_branch, code, target, prog, borrow_mut_kv)?;
    Ok(MatchArm {
        variant: expected_tag,
        bindings,
        body: Box::new(body),
    })
}

/// Look through the branch's execution-transparent prefix for a
/// `Bytecode::Call(_, dests, UnpackVariant(_, _, vid, _, _), _, _)`
/// whose variant tag (looked up via the GlobalEnv) and destination arity
/// match the arm and whose source is the switch selector. On hit, return
/// `(dest_temps, rewritten_branch)` where
/// `rewritten_branch` has the UnpackVariant's PC excised from its first
/// Basic. A non-Unpack prefix returns `Ok(None)`; a mismatched Unpack
/// returns `Err(())` so the caller reports `MalformedMatchArm`.
///
fn try_hoist_unpack_variant(
    branch: &Region,
    expected_source: move_stackless_bytecode::ast::TempIndex,
    expected_module_id: move_model::model::ModuleId,
    expected_datatype_id: move_model::model::DatatypeId,
    expected_tag: usize,
    expected_field_count: usize,
    code: &[Bytecode],
    target: &FunctionTarget,
) -> Result<Option<(Vec<move_stackless_bytecode::ast::TempIndex>, Region)>, ()> {
    let HoistPrefix::Candidate(first_pc) = classify_hoist_prefix(branch, code) else {
        return Ok(None);
    };
    let expected_variant_id = target
        .global_env()
        .get_module(expected_module_id)
        .into_enum(expected_datatype_id)
        .get_variant_by_tag(expected_tag)
        .get_id();
    match code.get(first_pc as usize) {
        Some(Bytecode::Call(
            _,
            dests,
            move_stackless_bytecode::stackless_bytecode::Operation::UnpackVariant(
                module_id,
                datatype_id,
                variant_id,
                _,
                move_model::model::RefType::ByValue,
            ),
            srcs,
            _,
        )) => {
            let identity_matches = *module_id == expected_module_id
                && *datatype_id == expected_datatype_id
                && *variant_id == expected_variant_id;
            if !unpack_prefix_matches_arm(
                identity_matches,
                srcs.as_slice() == [expected_source],
                dests.len(),
                expected_field_count,
            ) {
                return Err(());
            }
            let dest_temps = dests.clone();
            let rewritten = excise_first_pc_in_first_basic(branch, first_pc, code).ok_or(())?;
            Ok(Some((dest_temps, rewritten)))
        }
        _ => Ok(None),
    }
}

fn unpack_prefix_matches_arm(
    identity_matches: bool,
    source_matches: bool,
    actual_field_count: usize,
    expected_field_count: usize,
) -> bool {
    identity_matches && source_matches && actual_field_count == expected_field_count
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HoistPrefix {
    Candidate(CodeOffset),
    Transparent,
    Barrier,
}

fn bytecode_is_hoist_transparent(bytecode: &Bytecode) -> bool {
    matches!(
        bytecode,
        Bytecode::Label(..) | Bytecode::Nop(_) | Bytecode::Prop(..) | Bytecode::SaveMem(..)
    )
}

/// Find the first bytecode with an IR effect behind only execution-transparent
/// prefixes. A control-flow node is a barrier: bytecode in its descendants is
/// not an arm prefix. An all-no-op Basic/Seq is transparent so a following
/// sibling may still contain the prefix operation.
fn classify_hoist_prefix(region: &Region, code: &[Bytecode]) -> HoistPrefix {
    match region {
        Region::Basic { lower, upper } if upper >= lower => {
            for pc in *lower..=*upper {
                let Some(bytecode) = code.get(pc as usize) else {
                    return HoistPrefix::Barrier;
                };
                if !bytecode_is_hoist_transparent(bytecode) {
                    return HoistPrefix::Candidate(pc);
                }
            }
            HoistPrefix::Transparent
        }
        Region::Basic { .. } => HoistPrefix::Transparent,
        Region::Seq(children) => {
            for child in children {
                match classify_hoist_prefix(child, code) {
                    HoistPrefix::Transparent => {}
                    prefix => return prefix,
                }
            }
            HoistPrefix::Transparent
        }
        Region::LabeledBlock { body } => classify_hoist_prefix(body, code),
        Region::If { .. } | Region::Switch { .. } | Region::While { .. } | Region::Term(_) => {
            HoistPrefix::Barrier
        }
    }
}

/// Produce a copy of `region` with its certified prefix candidate excised.
/// Transparent bytecodes before the candidate remain in place; an interior
/// candidate splits its Basic range into the preserved prefix and suffix.
fn excise_first_pc_in_first_basic(
    region: &Region,
    target_pc: CodeOffset,
    code: &[Bytecode],
) -> Option<Region> {
    match region {
        Region::Basic { lower, upper } => {
            if target_pc < *lower || target_pc > *upper {
                return None;
            }
            let mut pieces = Vec::with_capacity(2);
            if *lower < target_pc {
                pieces.push(Region::Basic {
                    lower: *lower,
                    upper: target_pc - 1,
                });
            }
            if target_pc < *upper {
                pieces.push(Region::Basic {
                    lower: target_pc + 1,
                    upper: *upper,
                });
            }
            match pieces.as_slice() {
                [] => Some(Region::Seq(Vec::new())),
                [only] => Some(only.clone()),
                _ => Some(Region::Seq(pieces)),
            }
        }
        Region::Seq(children) => {
            let mut out = Vec::with_capacity(children.len());
            let mut excised = false;
            for child in children {
                if !excised {
                    match classify_hoist_prefix(child, code) {
                        HoistPrefix::Transparent => {}
                        HoistPrefix::Candidate(pc) if pc == target_pc => {
                            let rewritten = excise_first_pc_in_first_basic(child, target_pc, code)?;
                            excised = true;
                            if !matches!(&rewritten, Region::Seq(v) if v.is_empty()) {
                                out.push(rewritten);
                            }
                            continue;
                        }
                        HoistPrefix::Candidate(_) | HoistPrefix::Barrier => return None,
                    }
                }
                out.push(child.clone());
            }
            if excised {
                Some(Region::Seq(out))
            } else {
                None
            }
        }
        Region::LabeledBlock { body } => match classify_hoist_prefix(body, code) {
            HoistPrefix::Candidate(pc) if pc == target_pc => {
                excise_first_pc_in_first_basic(body, target_pc, code).map(|rewritten| {
                    Region::LabeledBlock {
                        body: Box::new(rewritten),
                    }
                })
            }
            HoistPrefix::Candidate(_) | HoistPrefix::Transparent | HoistPrefix::Barrier => None,
        },
        Region::If { .. } | Region::Switch { .. } | Region::While { .. } | Region::Term(_) => None,
    }
}

/// Peel a Move type to its underlying enum identifier. Accepts:
/// - `Datatype(mid, did, _)` -- the value form
/// - `Reference(_, Datatype(mid, did, _))` -- `&Enum` / `&mut Enum`
///
/// Returns NotImplemented for any other shape (defensive guard
/// against upstream emitting a VariantSwitch on a non-enum).
fn peel_enum(
    ty: &move_model::ty::Type,
) -> Result<(move_model::model::ModuleId, move_model::model::DatatypeId), Stage2Error> {
    use move_model::ty::Type as MoveType;
    match ty {
        MoveType::Datatype(mid, did, _) => Ok((*mid, *did)),
        MoveType::Reference(_, inner) => peel_enum(inner),
        _ => Err(Stage2Error::NotImplemented {
            reason: "lift_region fallthrough",
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Const;
    use ethnum::U256;
    use move_binary_format::file_format::{
        basic_test_module_with_enum, EnumDefinitionIndex, IdentifierIndex, VariantDefinition,
        VariantHandle,
    };
    use move_model::{model::RefType, ty::Type as MoveType};
    use move_stackless_bytecode::ast::TempIndex;
    use move_stackless_bytecode::{
        stackless_bytecode::{AttrId, Bytecode as StacklessBytecode, Label, Operation},
        stackless_bytecode_generator::StacklessBytecodeGenerator,
    };

    fn prefix_test_code(last_pc: CodeOffset, candidate_pc: CodeOffset) -> Vec<Bytecode> {
        (0..=last_pc)
            .map(|pc| {
                if pc == candidate_pc {
                    StacklessBytecode::VariantSwitch(AttrId::new(pc as usize), 0, Vec::new())
                } else {
                    StacklessBytecode::Nop(AttrId::new(pc as usize))
                }
            })
            .collect()
    }

    #[test]
    fn variant_layout_uses_sparse_declared_tags_in_switch_label_order() {
        assert_eq!(
            variant_layout_in_tag_order(vec![(7, 2), (3, 1), (11, 0)]),
            vec![(3, 1), (7, 2), (11, 0)]
        );
    }

    #[test]
    fn unpack_prefix_requires_matching_identity_and_payload_arity() {
        assert!(unpack_prefix_matches_arm(true, true, 2, 2));
        assert!(!unpack_prefix_matches_arm(false, true, 2, 2));
        assert!(!unpack_prefix_matches_arm(true, false, 2, 2));
        assert!(!unpack_prefix_matches_arm(true, true, 1, 2));
    }

    #[test]
    fn mismatched_leading_unpack_variant_reports_arm_and_switch() {
        let mut module = basic_test_module_with_enum();
        module.enum_defs[0].variants.push(VariantDefinition {
            variant_name: IdentifierIndex::new(1),
            fields: Vec::new(),
        });
        module.variant_handles.push(VariantHandle {
            enum_def: EnumDefinitionIndex::new(0),
            variant: 1,
        });

        let env = move_model::run_bytecode_model_builder([&module]).expect("model");
        let module_env = env.get_modules().next().expect("module");
        let enum_env = module_env.get_enums().next().expect("enum");
        let module_id = module_env.get_id();
        let datatype_id = enum_env.get_id();
        let tag_zero = enum_env.get_variant_by_tag(0).get_id();
        let tag_one = enum_env.get_variant_by_tag(1).get_id();
        let func_env = module_env.get_functions().next().expect("function");

        let mut data = StacklessBytecodeGenerator::new(&func_env).generate_function();
        data.local_types = vec![
            MoveType::Datatype(module_id, datatype_id, Vec::new()),
            MoveType::Datatype(module_id, datatype_id, Vec::new()),
        ];
        data.code = vec![
            StacklessBytecode::VariantSwitch(AttrId::new(0), 0, vec![Label::new(0), Label::new(1)]),
            StacklessBytecode::Label(AttrId::new(1), Label::new(0)),
            StacklessBytecode::Call(
                AttrId::new(2),
                Vec::new(),
                Operation::UnpackVariant(
                    module_id,
                    datatype_id,
                    tag_zero,
                    Vec::new(),
                    RefType::ByValue,
                ),
                vec![0],
                None,
            ),
            StacklessBytecode::Label(AttrId::new(3), Label::new(1)),
            StacklessBytecode::Call(
                AttrId::new(4),
                Vec::new(),
                Operation::UnpackVariant(
                    module_id,
                    datatype_id,
                    tag_zero,
                    Vec::new(),
                    RefType::ByValue,
                ),
                vec![0],
                None,
            ),
        ];
        let region = Region::Switch {
            switch_at: 0,
            branches: vec![
                Region::Basic { lower: 1, upper: 2 },
                Region::Basic { lower: 3, upper: 4 },
            ],
        };
        let expected_error = Stage2Error::MalformedMatchArm {
            switch_at: 0,
            branch_index: 1,
        };
        {
            let target =
                move_stackless_bytecode::function_target::FunctionTarget::new(&func_env, &data);
            let mut prog = ProgramBuilder::new();
            let mut borrow_mut_kv = std::collections::BTreeMap::new();
            let error = lift_region(&region, &data.code, &target, &mut prog, &mut borrow_mut_kv)
                .expect_err("branch 1 must reject branch 0's UnpackVariant");
            assert_eq!(error, expected_error);
        }

        data.code[4] = StacklessBytecode::Call(
            AttrId::new(4),
            Vec::new(),
            Operation::UnpackVariant(
                module_id,
                datatype_id,
                tag_one,
                Vec::new(),
                RefType::ByValue,
            ),
            vec![1],
            None,
        );
        let target =
            move_stackless_bytecode::function_target::FunctionTarget::new(&func_env, &data);
        let mut prog = ProgramBuilder::new();
        let mut borrow_mut_kv = std::collections::BTreeMap::new();
        let error = lift_region(&region, &data.code, &target, &mut prog, &mut borrow_mut_kv)
            .expect_err("branch 1 must reject an UnpackVariant of a non-selector temp");
        assert_eq!(error, expected_error);
    }

    #[test]
    fn matching_label_headed_unpack_nested_under_labeled_block_is_hoisted() {
        let mut module = basic_test_module_with_enum();
        module.enum_defs[0].variants.push(VariantDefinition {
            variant_name: IdentifierIndex::new(1),
            fields: Vec::new(),
        });
        module.variant_handles.push(VariantHandle {
            enum_def: EnumDefinitionIndex::new(0),
            variant: 1,
        });

        let env = move_model::run_bytecode_model_builder([&module]).expect("model");
        let module_env = env.get_modules().next().expect("module");
        let enum_env = module_env.get_enums().next().expect("enum");
        let module_id = module_env.get_id();
        let datatype_id = enum_env.get_id();
        let tag_zero = enum_env.get_variant_by_tag(0).get_id();
        let tag_one = enum_env.get_variant_by_tag(1).get_id();
        let func_env = module_env.get_functions().next().expect("function");

        let mut data = StacklessBytecodeGenerator::new(&func_env).generate_function();
        data.local_types = vec![MoveType::Datatype(module_id, datatype_id, Vec::new())];
        data.code = vec![
            StacklessBytecode::VariantSwitch(AttrId::new(0), 0, vec![Label::new(0), Label::new(1)]),
            StacklessBytecode::Label(AttrId::new(1), Label::new(0)),
            StacklessBytecode::Call(
                AttrId::new(2),
                Vec::new(),
                Operation::UnpackVariant(
                    module_id,
                    datatype_id,
                    tag_zero,
                    Vec::new(),
                    RefType::ByValue,
                ),
                vec![0],
                None,
            ),
            StacklessBytecode::Label(AttrId::new(3), Label::new(1)),
            StacklessBytecode::Call(
                AttrId::new(4),
                Vec::new(),
                Operation::UnpackVariant(
                    module_id,
                    datatype_id,
                    tag_one,
                    Vec::new(),
                    RefType::ByValue,
                ),
                vec![0],
                None,
            ),
        ];
        let target =
            move_stackless_bytecode::function_target::FunctionTarget::new(&func_env, &data);
        let region = Region::Switch {
            switch_at: 0,
            branches: vec![
                Region::LabeledBlock {
                    body: Box::new(Region::Basic { lower: 1, upper: 2 }),
                },
                Region::Basic { lower: 3, upper: 4 },
            ],
        };
        let mut prog = ProgramBuilder::new();
        let mut borrow_mut_kv = std::collections::BTreeMap::new();

        let lifted = lift_region(&region, &data.code, &target, &mut prog, &mut borrow_mut_kv)
            .expect("nested matching UnpackVariant must be hoisted and excised");

        let [Stmt::Eval(Expr::Match { cases, .. })] = lifted.stmts.as_slice() else {
            panic!("expected lifted match")
        };
        assert_eq!(cases.len(), 2);
        assert!(matches!(
            cases[0].body.stmts.as_slice(),
            [Stmt::Eval(Expr::LabeledBlock { body, .. })]
                if body.stmts.is_empty()
        ));
    }

    #[test]
    fn branch_local_unpack_is_not_an_outer_arm_prefix() {
        let mut module = basic_test_module_with_enum();
        module.enum_defs[0].variants.push(VariantDefinition {
            variant_name: IdentifierIndex::new(1),
            fields: Vec::new(),
        });
        module.variant_handles.push(VariantHandle {
            enum_def: EnumDefinitionIndex::new(0),
            variant: 1,
        });

        let env = move_model::run_bytecode_model_builder([&module]).expect("model");
        let module_env = env.get_modules().next().expect("module");
        let enum_env = module_env.get_enums().next().expect("enum");
        let module_id = module_env.get_id();
        let datatype_id = enum_env.get_id();
        let tag_one = enum_env.get_variant_by_tag(1).get_id();
        let func_env = module_env.get_functions().next().expect("function");

        let mut data = StacklessBytecodeGenerator::new(&func_env).generate_function();
        data.local_types = vec![MoveType::Datatype(module_id, datatype_id, Vec::new())];
        data.code = vec![StacklessBytecode::Call(
            AttrId::new(0),
            Vec::new(),
            Operation::UnpackVariant(
                module_id,
                datatype_id,
                tag_one,
                Vec::new(),
                RefType::ByValue,
            ),
            vec![0],
            None,
        )];
        let target =
            move_stackless_bytecode::function_target::FunctionTarget::new(&func_env, &data);
        let nested = Region::Basic { lower: 0, upper: 0 };
        let regions = [
            Region::If {
                cond_at: 10,
                then_branch: Box::new(nested.clone()),
                else_branch: Box::new(Region::Seq(Vec::new())),
            },
            Region::Switch {
                switch_at: 10,
                branches: vec![nested.clone()],
            },
            Region::While {
                header: Box::new(nested),
                cond_at: 10,
                body: Box::new(Region::Seq(Vec::new())),
                negate_cond: false,
            },
        ];

        for region in regions {
            assert_eq!(
                classify_hoist_prefix(&region, &data.code),
                HoistPrefix::Barrier
            );
            assert_eq!(
                try_hoist_unpack_variant(
                    &region,
                    0,
                    module_id,
                    datatype_id,
                    0,
                    0,
                    &data.code,
                    &target,
                )
                .expect("branch-local mismatch is not an outer-arm error"),
                None
            );
        }
    }

    // ---- classify_hoist_prefix ---------------------------------------

    #[test]
    fn classify_hoist_prefix_finds_candidate_in_seq() {
        let r = Region::Seq(vec![
            Region::Basic {
                lower: 5,
                upper: 10,
            },
            Region::Term(Termination::Return { temps: vec![] }),
        ]);
        assert_eq!(
            classify_hoist_prefix(&r, &prefix_test_code(10, 5)),
            HoistPrefix::Candidate(5)
        );
    }

    #[test]
    fn classify_hoist_prefix_stops_at_term() {
        let r = Region::Term(Termination::Break { level: 0 });
        assert_eq!(classify_hoist_prefix(&r, &[]), HoistPrefix::Barrier);
    }

    #[test]
    fn classify_hoist_prefix_skips_transparent_seq_prefix() {
        let r = Region::Seq(vec![
            Region::Basic { lower: 0, upper: 1 },
            Region::Basic { lower: 7, upper: 9 },
        ]);
        assert_eq!(
            classify_hoist_prefix(&r, &prefix_test_code(9, 7)),
            HoistPrefix::Candidate(7)
        );
    }

    #[test]
    fn classify_hoist_prefix_stops_at_if() {
        let r = Region::If {
            cond_at: 0,
            then_branch: Box::new(Region::Basic { lower: 3, upper: 4 }),
            else_branch: Box::new(Region::Term(Termination::Continue { level: 0 })),
        };
        assert_eq!(
            classify_hoist_prefix(&r, &prefix_test_code(4, 3)),
            HoistPrefix::Barrier
        );
    }

    // ---- excise_first_pc_in_first_basic ------------------------------

    #[test]
    fn excise_at_pc_lower_of_basic_shrinks_range() {
        let r = Region::Basic {
            lower: 5,
            upper: 10,
        };
        let out = excise_first_pc_in_first_basic(&r, 5, &[]).unwrap();
        assert_eq!(
            out,
            Region::Basic {
                lower: 6,
                upper: 10
            }
        );
    }

    #[test]
    fn excise_at_lower_when_lower_equals_upper_drops_basic() {
        let r = Region::Basic { lower: 5, upper: 5 };
        let out = excise_first_pc_in_first_basic(&r, 5, &[]).unwrap();
        assert_eq!(out, Region::Seq(vec![]));
    }

    #[test]
    fn excise_interior_candidate_preserves_transparent_prefix_and_suffix() {
        let r = Region::Basic { lower: 0, upper: 3 };
        let out = excise_first_pc_in_first_basic(&r, 2, &prefix_test_code(3, 2)).unwrap();
        assert_eq!(
            out,
            Region::Seq(vec![
                Region::Basic { lower: 0, upper: 1 },
                Region::Basic { lower: 3, upper: 3 },
            ])
        );
    }

    #[test]
    fn excise_at_pc_outside_basic_returns_none() {
        let r = Region::Basic {
            lower: 5,
            upper: 10,
        };
        assert!(excise_first_pc_in_first_basic(&r, 4, &[]).is_none());
    }

    #[test]
    fn excise_in_seq_drops_basic_when_range_empty() {
        let r = Region::Seq(vec![
            Region::Basic { lower: 5, upper: 5 },
            Region::Term(Termination::Return { temps: vec![] }),
        ]);
        let code = prefix_test_code(5, 5);
        let out = excise_first_pc_in_first_basic(&r, 5, &code).unwrap();
        // Empty Basic dropped; only the Term remains.
        match out {
            Region::Seq(children) => {
                assert_eq!(children.len(), 1);
                assert_eq!(
                    children[0],
                    Region::Term(Termination::Return { temps: vec![] })
                );
            }
            other => panic!("expected Seq, got {other:?}"),
        }
    }

    #[test]
    fn excise_in_seq_shrinks_basic_keeping_remainder() {
        let r = Region::Seq(vec![
            Region::Basic {
                lower: 5,
                upper: 10,
            },
            Region::Term(Termination::Return { temps: vec![] }),
        ]);
        let code = prefix_test_code(10, 5);
        let out = excise_first_pc_in_first_basic(&r, 5, &code).unwrap();
        match out {
            Region::Seq(children) => {
                assert_eq!(children.len(), 2);
                assert_eq!(
                    children[0],
                    Region::Basic {
                        lower: 6,
                        upper: 10
                    }
                );
            }
            other => panic!("expected Seq, got {other:?}"),
        }
    }

    // ---- value_from_temps --------------------------------------------

    #[test]
    fn value_from_temps_empty_is_unit() {
        let v: Vec<TempIndex> = vec![];
        assert_eq!(value_from_temps(&v), Expr::Unit);
    }

    #[test]
    fn value_from_temps_single_is_var() {
        assert_eq!(value_from_temps(&[5]), Expr::Var("$t5".into()));
    }

    #[test]
    fn value_from_temps_multiple_is_tuple() {
        let got = value_from_temps(&[1, 2, 3]);
        match got {
            Expr::Tuple(es) => {
                assert_eq!(es.len(), 3);
                assert_eq!(es[0], Expr::Var("$t1".into()));
                assert_eq!(es[1], Expr::Var("$t2".into()));
                assert_eq!(es[2], Expr::Var("$t3".into()));
            }
            other => panic!("expected Tuple, got {other:?}"),
        }
    }

    // ---- lift_termination --------------------------------------------

    #[test]
    fn lift_term_return_with_one_temp() {
        let bt = lift_termination(&Termination::Return { temps: vec![3] });
        match bt {
            BlockTail::Return(e) => assert_eq!(*e, Expr::Var("$t3".into())),
            other => panic!("expected Return, got {other:?}"),
        }
    }

    #[test]
    fn lift_term_return_with_no_temps_returns_unit() {
        let bt = lift_termination(&Termination::Return { temps: vec![] });
        match bt {
            BlockTail::Return(e) => assert_eq!(*e, Expr::Unit),
            other => panic!("expected Return, got {other:?}"),
        }
    }

    #[test]
    fn lift_term_return_with_many_temps_returns_tuple() {
        let bt = lift_termination(&Termination::Return { temps: vec![1, 2] });
        match bt {
            BlockTail::Return(e) => {
                assert!(matches!(*e, Expr::Tuple(_)));
            }
            other => panic!("expected Return, got {other:?}"),
        }
    }

    #[test]
    fn lift_term_abort_with_code_temp_uses_var() {
        let bt = lift_termination(&Termination::Abort { code_temp: Some(7) });
        match bt {
            BlockTail::Abort { code } => assert_eq!(*code, Expr::Var("$t7".into())),
            other => panic!("expected Abort, got {other:?}"),
        }
    }

    #[test]
    fn lift_term_abort_with_no_code_temp_uses_zero_const() {
        let bt = lift_termination(&Termination::Abort { code_temp: None });
        match bt {
            BlockTail::Abort { code } => match *code {
                Expr::Const(Const::UInt { bits, value }) => {
                    assert_eq!(bits, 64);
                    assert_eq!(value, U256::ZERO);
                }
                other => panic!("expected u64 zero const, got {other:?}"),
            },
            other => panic!("expected Abort, got {other:?}"),
        }
    }

    #[test]
    fn lift_term_break_carries_level_and_unit_value() {
        let bt = lift_termination(&Termination::Break { level: 2 });
        match bt {
            BlockTail::Break { level, value } => {
                assert_eq!(level, 2);
                assert_eq!(*value, Expr::Unit);
            }
            other => panic!("expected Break, got {other:?}"),
        }
    }

    #[test]
    fn lift_term_continue_carries_level_and_unit_value() {
        let bt = lift_termination(&Termination::Continue { level: 0 });
        match bt {
            BlockTail::Continue { level, value } => {
                assert_eq!(level, 0);
                assert_eq!(*value, Expr::Unit);
            }
            other => panic!("expected Continue, got {other:?}"),
        }
    }

    #[test]
    fn fall_through_tail_is_value_unit() {
        assert_eq!(fall_through_tail(), BlockTail::Value(Expr::Unit));
    }
}
