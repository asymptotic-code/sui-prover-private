// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Phase 1 of CFG reconstruction (IR-free).
//!
//! Walk the stackless bytecode and produce a `BytecodeCFG` of basic
//! blocks with PC ranges and IR-free terminator metadata. Loops are
//! detected via in-walk back-edge identification, and cross-level
//! back-edges (typical of the bytecode optimizer's "exit inner;
//! continue outer" pattern) get a synthetic block inserted for the
//! back-edge half.
//!
//! Phase 2 (`super::skeleton_recovery::recover`) consumes the
//! `BytecodeCFG` produced here. Phase 3
//! (`super::ir_translation::translate`) is the IR-bearing stage.

use move_stackless_bytecode::ast::TempIndex;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Label};
use std::collections::{BTreeMap, HashMap};

// ---------------------------------------------------------------------------
// Pre-translation CFG types
// ---------------------------------------------------------------------------

/// Loop metadata recorded during CFG discovery.
///
/// `header` and `backedges` are block indices. `exit_label` is the jump
/// target on the false branch of the loop header — the first block of
/// the loop's continuation (i.e., the semantic "after the loop" point).
/// `None` means the exit hasn't been resolved yet — the loop was
/// registered via an unconditional `Jump` back-edge which has no
/// header-level exit branch; the post-walk recovery pass scans for it.
#[derive(Debug, Clone)]
pub(super) struct LoopInfo {
    pub(super) header: usize,
    /// Every block index whose terminator is a back-edge to `header`.
    /// Multiple entries arise when the source has more than one
    /// `continue` path or back-edge to the same header. Consumers that
    /// need an "is this past every back-edge?" upper bound take
    /// `backedges.iter().max()` (always defined — `LoopInfo` is only
    /// constructed with at least one back-edge).
    pub(super) backedges: Vec<usize>,
    pub(super) exit_label: Option<Label>,
}

/// IR-free terminator captured during CFG discovery. Carries the bytecode
/// temp indices (and ret-value temps) that the IR-translation phase will
/// lift to `IRNode::Var`.
#[derive(Debug, Clone)]
pub(crate) enum Terminator {
    Branch {
        cond_temp: TempIndex,
        /// True when the original Branch was rewritten during synthesis
        /// with `then_is_backward`: the synthetic block goes on the else
        /// arm and the cond gets negated so the unchanged arm assignment
        /// retains the original "cond=true → exit" semantics.
        negate_cond: bool,
        then_label: Label,
        else_label: Label,
    },
    Switch {
        scrutinee_temp: TempIndex,
        cases: Vec<Label>,
    },
    /// Function-return with the temps holding the return value(s). The
    /// translation phase generates the trailing `current = assign(current,
    /// ret_val)` that makes the return value the block's tail expression.
    Return {
        temps: Vec<TempIndex>,
    },
    /// `code_temp` is the temp holding the abort code (Move's
    /// `Bytecode::Abort(_, code_temp)` second operand). For synthesised
    /// abort sites with no source-level code temp, `code_temp` is `None`.
    Abort {
        code_temp: Option<TempIndex>,
    },
    Fallthrough,
    /// Block-level back-edge: this block ends by continuing iteration of
    /// the loop whose header is `target_header`. Synthesised on Branch
    /// back-arms by `discover_cfg`; emitted directly for unconditional
    /// `Jump <header>` back-edges.
    Continue {
        target_header: usize,
    },
    Jump {
        target: Label,
    },
}

/// One basic block in the pre-translation CFG. The PC range covers the
/// bytecodes that fall inside this block (label, branch, jump, switch,
/// ret, and abort bytecodes are *not* in any block's PC range — they're
/// either markers or terminator-causing instructions).
///
/// Synthetic blocks (inserted for cross-level back-edges) have an empty
/// PC range (`start == end`) and exist purely for the structure builder
/// to classify a terminating leaf.
#[derive(Debug, Clone)]
pub(crate) struct BlockCfg {
    /// Inclusive lower bound on bytecode indices in this block.
    pub(crate) start: usize,
    /// Exclusive upper bound on bytecode indices in this block.
    pub(crate) end: usize,
    pub(crate) terminator: Terminator,
}

impl BlockCfg {
    fn new(start: usize, end: usize, terminator: Terminator) -> Self {
        Self {
            start,
            end,
            terminator,
        }
    }

    fn synthetic(at: usize, terminator: Terminator) -> Self {
        Self {
            start: at,
            end: at,
            terminator,
        }
    }
}

/// Output of `discover_cfg`: a fully-resolved IR-free CFG. Carries the
/// basic-block list, the label map, the back-edge-derived loop metadata,
/// and the successor map (one entry per block, listing successor block
/// indices). Successors aren't computed during the linear walk because
/// forward Branch/Jump/Switch targets aren't yet resolvable when their
/// containing block is pushed; they're filled in as a tail step once
/// `label_to_block` is final.
pub(super) struct BytecodeCFG {
    pub(super) blocks: Vec<BlockCfg>,
    pub(super) label_to_block: HashMap<Label, usize>,
    pub(super) loops: Vec<LoopInfo>,
    pub(super) successors: BTreeMap<usize, Vec<usize>>,
}

// ---------------------------------------------------------------------------
// Phase 1: bytecode → BytecodeCFG (no IR)
// ---------------------------------------------------------------------------

/// Walk the stackless bytecode and build a CFG of basic blocks with their
/// terminators and loop metadata. No IR translation happens here; the
/// IR-translation phase lifts terminator temps to `IRNode::Var` on demand.
pub(super) fn discover_cfg(target: &FunctionTarget) -> BytecodeCFG {
    let bytecode = target.get_bytecode();

    if std::env::var("PROBE_BYTECODE").is_ok() {
        let name = target
            .func_env
            .get_name()
            .display(target.global_env().symbol_pool())
            .to_string();
        if name == std::env::var("PROBE_BYTECODE").unwrap_or_default() {
            eprintln!("PROBE_BYTECODE function: {}", name);
            for (i, bc) in bytecode.iter().enumerate() {
                eprintln!("PROBE_BYTECODE  [{:3}] {:?}", i, bc);
            }
        }
    }

    let mut blocks: Vec<BlockCfg> = Vec::new();
    let mut label_to_block: HashMap<Label, usize> = HashMap::new();
    let mut loops: Vec<LoopInfo> = Vec::new();
    let mut current_start: usize = 0;
    // Synthetic labels for cross-level Branch back-arms count down from
    // `u16::MAX` to avoid colliding with real labels (which the source
    // assigns starting at 0).
    let mut synthetic_label_counter: u16 = u16::MAX;

    for (pc, bc) in bytecode.iter().enumerate() {
        match bc {
            Bytecode::Label(_, label) => {
                blocks.push(BlockCfg::new(current_start, pc, Terminator::Fallthrough));
                label_to_block.insert(*label, blocks.len());
                current_start = pc + 1;
            }
            Bytecode::Branch(_, then_label, else_label, cond_temp) => {
                let current_block = blocks.len();
                let then_is_backward = label_to_block
                    .get(then_label)
                    .map(|&b| b <= current_block)
                    .unwrap_or(false);
                let else_is_backward = label_to_block
                    .get(else_label)
                    .map(|&b| b <= current_block)
                    .unwrap_or(false);

                if then_is_backward || else_is_backward {
                    // Cross-level back-edge: synthesize a Continue block
                    // for the backward arm. Always place the synthetic on
                    // the else arm and negate the cond when needed,
                    // matching the legacy arm/cond convention so
                    // downstream structural shape is identical regardless
                    // of which arm was originally backward.
                    let loop_block_idx = current_block + 1;
                    let (loop_header, exit_label, negate_cond) = if then_is_backward {
                        (label_to_block[then_label], *else_label, true)
                    } else {
                        (label_to_block[else_label], *then_label, false)
                    };

                    if let Some(entry) = loops.iter_mut().find(|info| info.header == loop_header) {
                        entry.backedges.push(loop_block_idx);
                        entry.exit_label = Some(exit_label);
                    } else {
                        loops.push(LoopInfo {
                            header: loop_header,
                            backedges: vec![loop_block_idx],
                            exit_label: Some(exit_label),
                        });
                    }

                    let synthetic_label = Label::new(synthetic_label_counter as usize);
                    synthetic_label_counter = synthetic_label_counter.wrapping_sub(1);
                    label_to_block.insert(synthetic_label, loop_block_idx);

                    blocks.push(BlockCfg::new(
                        current_start,
                        pc,
                        Terminator::Branch {
                            cond_temp: *cond_temp,
                            negate_cond,
                            then_label: exit_label,
                            else_label: synthetic_label,
                        },
                    ));
                    blocks.push(BlockCfg::synthetic(
                        pc,
                        Terminator::Continue {
                            target_header: loop_header,
                        },
                    ));
                } else {
                    blocks.push(BlockCfg::new(
                        current_start,
                        pc,
                        Terminator::Branch {
                            cond_temp: *cond_temp,
                            negate_cond: false,
                            then_label: *then_label,
                            else_label: *else_label,
                        },
                    ));
                }
                current_start = pc + 1;
            }
            Bytecode::Jump(_, label) => {
                let current_block = blocks.len();
                let terminator = if let Some(&target_block) = label_to_block.get(label) {
                    if let Some(entry) = loops.iter_mut().find(|info| info.header == target_block) {
                        entry.backedges.push(current_block);
                    } else {
                        // Unconditional back-edge has no header-level
                        // exit branch — leave `exit_label` as `None`
                        // and let the post-walk recovery pass scan for
                        // the semantic exit by inspecting the loop's
                        // block range for a Branch with one in-loop
                        // and one out-of-loop target.
                        loops.push(LoopInfo {
                            header: target_block,
                            backedges: vec![current_block],
                            exit_label: None,
                        });
                    }
                    Terminator::Continue {
                        target_header: target_block,
                    }
                } else {
                    Terminator::Jump { target: *label }
                };
                blocks.push(BlockCfg::new(current_start, pc, terminator));
                current_start = pc + 1;
            }
            Bytecode::VariantSwitch(_, scrutinee_temp, labels) => {
                blocks.push(BlockCfg::new(
                    current_start,
                    pc,
                    Terminator::Switch {
                        scrutinee_temp: *scrutinee_temp,
                        cases: labels.to_vec(),
                    },
                ));
                current_start = pc + 1;
            }
            Bytecode::Ret(_, temps) => {
                blocks.push(BlockCfg::new(
                    current_start,
                    pc,
                    Terminator::Return {
                        temps: temps.clone(),
                    },
                ));
                current_start = pc + 1;
            }
            Bytecode::Abort(_, code_temp) => {
                blocks.push(BlockCfg::new(
                    current_start,
                    pc,
                    Terminator::Abort {
                        code_temp: Some(*code_temp),
                    },
                ));
                current_start = pc + 1;
            }
            _ => {
                // Non-control-flow bytecode — left in the current block's
                // PC range, to be translated in phase 3.
            }
        }
    }

    // If bytecode falls off the end without a Ret/Abort terminator, close
    // the tail with a Return.
    if !matches!(blocks.last(), Some(b) if matches!(b.terminator, Terminator::Return { .. })) {
        blocks.push(BlockCfg::new(
            current_start,
            bytecode.len(),
            Terminator::Return { temps: Vec::new() },
        ));
    }

    // Recover the semantic exit label for loops registered via an
    // unconditional Jump back-edge (those have `exit_label == None`).
    // We scan the loop's block range for a Branch whose one target is
    // inside the loop and the other is outside; the outside target is
    // the loop's continuation entry.
    for info in loops.iter_mut() {
        if info.exit_label.is_some() {
            continue;
        }
        let h = info.header;
        let b = *info
            .backedges
            .iter()
            .max()
            .expect("LoopInfo always has at least one backedge");
        for idx in h..=b.min(blocks.len().saturating_sub(1)) {
            if let Terminator::Branch {
                then_label,
                else_label,
                ..
            } = &blocks[idx].terminator
            {
                let t = label_to_block.get(then_label).copied();
                let e = label_to_block.get(else_label).copied();
                let in_loop = |x: Option<usize>| x.map(|y| y >= h && y <= b).unwrap_or(false);
                let out_of_loop = |x: Option<usize>| x.map(|y| y < h || y > b).unwrap_or(false);
                if in_loop(t) && out_of_loop(e) {
                    info.exit_label = Some(*else_label);
                    break;
                }
                if in_loop(e) && out_of_loop(t) {
                    info.exit_label = Some(*then_label);
                    break;
                }
            }
        }
    }

    // Compute the successor map now that `label_to_block` is finalised.
    let mut successors: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (idx, block) in blocks.iter().enumerate() {
        let succs = match &block.terminator {
            Terminator::Branch {
                then_label,
                else_label,
                ..
            } => vec![label_to_block[then_label], label_to_block[else_label]],
            Terminator::Switch { cases, .. } => cases.iter().map(|l| label_to_block[l]).collect(),
            Terminator::Fallthrough => {
                if idx + 1 < blocks.len() {
                    vec![idx + 1]
                } else {
                    vec![]
                }
            }
            Terminator::Continue { .. } => vec![],
            Terminator::Jump { target } => vec![label_to_block[target]],
            Terminator::Return { .. } | Terminator::Abort { .. } => vec![],
        };
        successors.insert(idx, succs);
    }

    BytecodeCFG {
        blocks,
        label_to_block,
        loops,
        successors,
    }
}
