// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Phase 3 of CFG reconstruction: walk the IR-free `Skeleton` produced by
//! `skeleton_recovery::recover` and translate each referenced basic
//! block's PCs to IR on demand via `ir_translator`, producing the
//! IR-bearing `Structure` consumed by `early_return`. No intermediate
//! flat-block table is materialised; per-block borrow tracking is reset
//! at each block boundary, matching the per-block contract that
//! `BorrowState` already enforces.
//!
//! `Skeleton::Seq` is folded right-to-left via `combine`: a leading plain
//! leaf becomes a body prefix on the suffix; a leading construct
//! (If/While/Switch) absorbs the suffix into its own continuation; a
//! leading terminating leaf swallows the suffix (it's unreachable).

use super::bytecode_cfg::{BlockCfg, Terminator};
use super::skeleton_recovery::{Skeleton, Termination};
use crate::program_builder::ProgramBuilder;
use crate::translation::borrow_tracking::BorrowState;
use crate::translation::ir_translator::{self, temp_id};
use intermediate_theorem_format::IRNode;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::Bytecode;

// ---------------------------------------------------------------------------
// IR-bearing structure (input to early_return — output of `translate`)
// ---------------------------------------------------------------------------

/// Recursive control flow structure with IR bodies. Produced by
/// `translate`; consumed by `early_return::emit`.
#[derive(Debug, Clone)]
pub enum Structure {
    /// A straight-line block of code, optionally terminated.
    /// No termination means it flows into the parent's continuation.
    Leaf {
        body: IRNode,
        termination: Option<Termination>,
    },
    /// If-else branch. `body` is code that executes before the condition.
    If {
        body: IRNode,
        cond: IRNode,
        then_branch: Box<Structure>,
        else_branch: Box<Structure>,
        continuation: Option<Box<Structure>>,
    },
    /// While loop. `body` is the one-shot code preceding the loop.
    /// `loop_body` is the per-iteration body. `continuation` is what
    /// comes after the loop exits.
    While {
        body: IRNode,
        loop_body: Box<Structure>,
        continuation: Option<Box<Structure>>,
    },
    /// Variant switch (match). `body` is code before the scrutinee.
    Switch {
        body: IRNode,
        scrutinee: IRNode,
        cases: Vec<Structure>,
        continuation: Option<Box<Structure>>,
    },
}

impl Structure {
    /// Returns true if every control-flow path through this structure
    /// ends in a `Return` or `Abort` leaf — i.e. nothing past it is
    /// ever reachable. Used by `early_return::emit_if` to decide which
    /// branches need a continuation merged in.
    pub fn always_returns(&self) -> bool {
        self.terminates_on_every_path(&|t| {
            matches!(t, Termination::Return | Termination::Abort { .. })
        })
    }

    /// Like `always_returns`, but only counts `Abort` leaves. Used by
    /// the body-side abort prune in `emit_if`.
    pub fn always_aborts(&self) -> bool {
        self.terminates_on_every_path(&|t| matches!(t, Termination::Abort { .. }))
    }

    /// Walk the tree and check whether every leaf either matches
    /// `leaf_pred` directly or sits behind a non-empty set of branches
    /// (which all terminate) and a continuation that also terminates.
    fn terminates_on_every_path(&self, leaf_pred: &impl Fn(&Termination) -> bool) -> bool {
        match self {
            Structure::Leaf { termination, .. } => termination.as_ref().is_some_and(leaf_pred),
            _ => {
                let branches = self.branches();
                if !branches.is_empty()
                    && branches
                        .iter()
                        .all(|b| b.terminates_on_every_path(leaf_pred))
                {
                    return true;
                }
                self.continuation()
                    .map(|c| c.terminates_on_every_path(leaf_pred))
                    .unwrap_or(false)
            }
        }
    }

    /// Direct branch children (then/else / loop_body / cases). Excludes
    /// the continuation, which is treated separately because it runs
    /// only after the branches converge.
    fn branches(&self) -> Vec<&Structure> {
        match self {
            Structure::Leaf { .. } => vec![],
            Structure::If {
                then_branch,
                else_branch,
                ..
            } => vec![then_branch, else_branch],
            Structure::While { loop_body, .. } => vec![loop_body],
            Structure::Switch { cases, .. } => cases.iter().collect(),
        }
    }

    /// The post-construct continuation, if any.
    fn continuation(&self) -> Option<&Structure> {
        match self {
            Structure::Leaf { .. } => None,
            Structure::If { continuation, .. }
            | Structure::While { continuation, .. }
            | Structure::Switch { continuation, .. } => continuation.as_deref(),
        }
    }
}

// ---------------------------------------------------------------------------
// Phase 3: Skeleton → IR-bearing Structure
// ---------------------------------------------------------------------------

/// Walk the structured CFG produced by `recover` and translate each
/// referenced bytecode block's PCs to IR. The result is the IR-bearing
/// `Structure` consumed by `early_return::emit`.
///
/// `Skeleton::Seq` is folded right-to-left via `combine`: a leading
/// plain leaf becomes a body prefix on the suffix; a leading construct
/// (If / While / Switch) absorbs the suffix into its own continuation; a
/// leading terminating leaf swallows the suffix (it's unreachable).
///
/// `Skeleton::While` carries a loop-body sub-tree whose first leaf is
/// the header block; that's where the loop guard (and any per-iteration
/// straight-line code) gets translated, mirroring the upstream
/// post-dom-driven loop shape.
pub fn translate(
    skel: &Skeleton,
    target: &FunctionTarget,
    builder: &mut ProgramBuilder,
) -> Structure {
    let borrow_field_parents =
        crate::translation::borrow_tracking::precompute_borrow_field_parents(target);
    translate_inner(skel, target, builder, &borrow_field_parents)
}

fn translate_inner(
    skel: &Skeleton,
    target: &FunctionTarget,
    builder: &mut ProgramBuilder,
    borrow_field_parents: &std::collections::BTreeSet<move_stackless_bytecode::ast::TempIndex>,
) -> Structure {
    match skel {
        Skeleton::Block(block) => Structure::Leaf {
            body: translate_block_body(block, target, builder, borrow_field_parents),
            termination: None,
        },
        Skeleton::Term(t) => Structure::Leaf {
            body: IRNode::unit(),
            termination: Some(t.clone()),
        },
        Skeleton::Seq(elems) => translate_seq(elems, target, builder, borrow_field_parents),
        Skeleton::If {
            cond_block,
            then_branch,
            else_branch,
        } => Structure::If {
            body: translate_block_body(cond_block, target, builder, borrow_field_parents),
            cond: cond_from_branch_block(cond_block, target),
            then_branch: Box::new(translate_inner(
                then_branch,
                target,
                builder,
                borrow_field_parents,
            )),
            else_branch: Box::new(translate_inner(
                else_branch,
                target,
                builder,
                borrow_field_parents,
            )),
            continuation: None,
        },
        Skeleton::While {
            header: _,
            loop_body,
        } => Structure::While {
            body: IRNode::unit(),
            loop_body: Box::new(translate_inner(
                loop_body,
                target,
                builder,
                borrow_field_parents,
            )),
            continuation: None,
        },
        Skeleton::Switch {
            scrutinee_block,
            cases,
        } => Structure::Switch {
            body: translate_block_body(scrutinee_block, target, builder, borrow_field_parents),
            scrutinee: scrutinee_from_switch_block(scrutinee_block, target),
            cases: cases
                .iter()
                .map(|c| translate_inner(c, target, builder, borrow_field_parents))
                .collect(),
            continuation: None,
        },
    }
}

fn translate_seq(
    elems: &[Skeleton],
    target: &FunctionTarget,
    builder: &mut ProgramBuilder,
    borrow_field_parents: &std::collections::BTreeSet<move_stackless_bytecode::ast::TempIndex>,
) -> Structure {
    if elems.is_empty() {
        return Structure::Leaf {
            body: IRNode::unit(),
            termination: None,
        };
    }
    let mut acc = translate_inner(
        &elems[elems.len() - 1],
        target,
        builder,
        borrow_field_parents,
    );
    for elem in elems[..elems.len() - 1].iter().rev() {
        let prefix = translate_inner(elem, target, builder, borrow_field_parents);
        acc = combine(prefix, acc);
    }
    acc
}

/// Combine a `prefix` Structure with a `suffix` Structure that runs
/// after it. Three cases:
///
/// * Plain leaf prefix (no termination): chain its body into `suffix`
///   via `prepend_body`.
/// * Terminating leaf prefix (Return / Abort / Continue / Break):
///   suffix is unreachable, return prefix unchanged.
/// * Construct prefix (If / While / Switch) with no continuation:
///   install `suffix` as the construct's continuation.
fn combine(prefix: Structure, suffix: Structure) -> Structure {
    match prefix {
        Structure::Leaf {
            body,
            termination: None,
        } => prepend_body(body, suffix),
        Structure::Leaf {
            termination: Some(_),
            ..
        } => prefix,
        Structure::If {
            body,
            cond,
            then_branch,
            else_branch,
            continuation: None,
        } => Structure::If {
            body,
            cond,
            then_branch,
            else_branch,
            continuation: Some(Box::new(suffix)),
        },
        Structure::While {
            body,
            loop_body,
            continuation: None,
        } => Structure::While {
            body,
            loop_body,
            continuation: Some(Box::new(suffix)),
        },
        Structure::Switch {
            body,
            scrutinee,
            cases,
            continuation: None,
        } => Structure::Switch {
            body,
            scrutinee,
            cases,
            continuation: Some(Box::new(suffix)),
        },
        // A construct with an existing continuation in the prefix
        // shouldn't happen — `translate` produces constructs with
        // `continuation: None`, and Seq folding sets continuations
        // exactly once.
        _ => panic!("combine: prefix Structure already has a continuation"),
    }
}

// ---------------------------------------------------------------------------
// Helpers: per-block IR translation + structure-prefix prepending
// ---------------------------------------------------------------------------

/// Translate one basic block's PCs into IR. Borrow tracking state is
/// constructed fresh for each block — it's per-block by contract (reset
/// at each terminator / label in the upstream `discover_cfg` model).
/// For `Return` terminators the return value is appended as the body's
/// trailing expression so the block IR matches the legacy fused-discover
/// output.
fn translate_block_body(
    block: &BlockCfg,
    target: &FunctionTarget,
    builder: &mut ProgramBuilder,
    borrow_field_parents: &std::collections::BTreeSet<move_stackless_bytecode::ast::TempIndex>,
) -> IRNode {
    let bytecode = target.get_bytecode();
    let mut body = IRNode::unit();
    let mut borrow_state = BorrowState::new();
    borrow_state.seed_borrow_field_seen(borrow_field_parents);
    for pc in block.start..block.end {
        let bc = &bytecode[pc];
        // Control-flow bytecodes are block boundaries — they live in
        // the terminator metadata, never in the block's body. The PC
        // range shouldn't include any (phase 1 is responsible for
        // slicing them out), but skip defensively in case it does.
        if matches!(
            bc,
            Bytecode::Label(..)
                | Bytecode::Branch(..)
                | Bytecode::Jump(..)
                | Bytecode::VariantSwitch(..)
                | Bytecode::Ret(..)
                | Bytecode::Abort(..)
        ) {
            continue;
        }
        let node = ir_translator::translate_one(target, builder, &borrow_state, bc);
        borrow_state.observe(bc);
        body = IRNode::assign(body, node);
    }
    if let Terminator::Return { temps } = &block.terminator {
        if !temps.is_empty() {
            let values: Vec<IRNode> = temps
                .iter()
                .map(|&t| IRNode::Var(temp_id(target, t)))
                .collect();
            let ret_val = if values.len() == 1 {
                values.into_iter().next().unwrap()
            } else {
                IRNode::Tuple(values)
            };
            body = IRNode::assign(body, ret_val);
        }
    }
    body
}

/// Lift the cond IRNode from a Branch-terminated block. Honors
/// `negate_cond` (set by `discover_cfg` when synthesising back-edge
/// blocks for branches whose then-arm was the back-edge).
fn cond_from_branch_block(block: &BlockCfg, target: &FunctionTarget) -> IRNode {
    match &block.terminator {
        Terminator::Branch {
            cond_temp,
            negate_cond,
            ..
        } => {
            let var = IRNode::Var(temp_id(target, *cond_temp));
            if *negate_cond {
                IRNode::UnOp {
                    op: intermediate_theorem_format::UnOp::Not,
                    operand: Box::new(var),
                }
            } else {
                var
            }
        }
        other => panic!("expected Branch terminator at If head, got {:?}", other),
    }
}

fn scrutinee_from_switch_block(block: &BlockCfg, target: &FunctionTarget) -> IRNode {
    match &block.terminator {
        Terminator::Switch { scrutinee_temp, .. } => IRNode::Var(temp_id(target, *scrutinee_temp)),
        other => panic!("expected Switch terminator at Switch head, got {:?}", other),
    }
}

/// Prepend a body IRNode to a structure by chaining into the node's
/// `body` field. Empty prefixes are skipped — `IRNode::assign` collapses
/// them.
fn prepend_body(prefix: IRNode, structure: Structure) -> Structure {
    if matches!(&prefix, IRNode::Tuple(e) if e.is_empty()) {
        return structure;
    }
    match structure {
        Structure::Leaf { body, termination } => Structure::Leaf {
            body: IRNode::assign(prefix, body),
            termination,
        },
        Structure::If {
            body,
            cond,
            then_branch,
            else_branch,
            continuation,
        } => Structure::If {
            body: IRNode::assign(prefix, body),
            cond,
            then_branch,
            else_branch,
            continuation,
        },
        Structure::While {
            body,
            loop_body,
            continuation,
        } => Structure::While {
            body: IRNode::assign(prefix, body),
            loop_body,
            continuation,
        },
        Structure::Switch {
            body,
            scrutinee,
            cases,
            continuation,
        } => Structure::Switch {
            body: IRNode::assign(prefix, body),
            scrutinee,
            cases,
            continuation,
        },
    }
}
