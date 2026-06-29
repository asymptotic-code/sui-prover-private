// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Phase 2 of CFG reconstruction (IR-free).
//!
//! Consume a `BytecodeCFG` (from `super::bytecode_cfg::discover_cfg`)
//! and produce a `Skeleton` — a recursive control-flow tree (Block /
//! Seq / Term / If / While / Switch) whose every "body" position is a
//! basic block from phase 1. The skeleton holds no IR; phase 3
//! (`super::ir_translation::translate`) walks it and emits IR on
//! demand. Composition is via `Seq`; constructs (`If` / `While` /
//! `Switch`) carry no continuation, mirroring upstream
//! `move-stackless-bytecode::control_flow_reconstruction::StructuredBlock`.

use super::bytecode_cfg::{discover_cfg, BlockCfg, LoopInfo, Terminator};
use crate::translation::ir_translator::temp_id;
use intermediate_theorem_format::IRNode;
use move_stackless_bytecode::ast::TempIndex;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::Label;
use std::collections::{BTreeMap, HashMap};

// ---------------------------------------------------------------------------
// Termination markers (shared with IR translation / emission)
// ---------------------------------------------------------------------------

/// How a leaf block terminates.
#[derive(Debug, Clone)]
pub(crate) enum Termination {
    Return,
    /// Move `abort N`. `code` is the IR for the abort code (typically a
    /// `Var` referencing a u64 temp). Synthesised abort sites have
    /// `code = None`.
    Abort {
        code: Option<IRNode>,
    },
    /// Loop back-edge (continue). `level` is the depth of the targeted
    /// loop in the enclosing stack: 0 = innermost, 1 = the loop one level
    /// out, etc. Cross-level continues arise when the bytecode optimizer
    /// collapses "exit inner; outer-iteration-tail" into a direct jump
    /// from inside the inner loop to the outer loop's header.
    Continue {
        level: usize,
    },
    /// Loop exit (break / forward jump past loop). `level` is the depth
    /// of the targeted loop in the enclosing stack: 0 = innermost, etc.
    /// Mirrors `Continue`'s level — cross-level breaks arise from the
    /// bytecode optimizer fusing "break inner; break outer" into a single
    /// forward jump from inside the inner loop straight past the outer
    /// loop's exit.
    Break {
        level: usize,
    },
}

// ---------------------------------------------------------------------------
// IR-free structured CFG (output of `recover`)
// ---------------------------------------------------------------------------

/// Recursive structured CFG over a function's stackless bytecode blocks.
/// Produced by `recover` (phase 2); consumed by
/// `super::ir_translation::translate` (phase 3). Composition via `Seq` —
/// constructs (`If` / `While` / `Switch`) carry no prefix and no
/// continuation, mirroring upstream
/// `move-stackless-bytecode::control_flow_reconstruction::StructuredBlock`.
///
/// * `Block(b)` is one basic block; translates to `b`'s IR body.
/// * `Seq([...])` runs its elements in order. An empty Seq is the unit
///   (no IR).
/// * `Term(t)` is a standalone termination marker (Continue / Break /
///   Return / Abort) without an accompanying block — used for arm
///   classifications where the arm has no body of its own.
/// * `If { cond_block, then, else }` — `cond_block`'s terminator is the
///   Branch providing the cond; its body runs before the branch decision.
/// * `While { header, loop_body }` — `header` is the iteration entry
///   block (also at the front of `loop_body`); continues and breaks
///   within `loop_body` surface as `Term` leaves.
/// * `Switch { scrutinee_block, cases }` — `scrutinee_block`'s terminator
///   is the VariantSwitch.
#[derive(Debug, Clone)]
pub(crate) enum Skeleton {
    Block(BlockCfg),
    Seq(Vec<Skeleton>),
    Term(Termination),
    If {
        cond_block: BlockCfg,
        then_branch: Box<Skeleton>,
        else_branch: Box<Skeleton>,
    },
    While {
        /// The loop's iteration entry block — the block where iteration
        /// re-enters via the back-edge. The same block also appears at
        /// the structural front of `loop_body` (as the cond_block of the
        /// leading `If`, the first leaf of a `Seq`, or the scrutinee of
        /// a leading `Switch`, depending on its terminator). Multiple
        /// continues / breaks within the loop surface as
        /// `Term(Continue)` / `Term(Break)` leaves anywhere inside
        /// `loop_body`.
        header: BlockCfg,
        loop_body: Box<Skeleton>,
    },
    Switch {
        scrutinee_block: BlockCfg,
        cases: Vec<Skeleton>,
    },
}

// ---------------------------------------------------------------------------
// Phase 2: BytecodeCFG → Skeleton (CFG analysis only, no IR)
// ---------------------------------------------------------------------------

/// Recover the structured CFG from a function's stackless bytecode. Walks
/// the bytecode (via `discover_cfg`), identifies basic blocks + loops,
/// computes post-dominators / branch convergence, and produces a
/// recursive `Skeleton` tree whose leaves embed the basic blocks
/// directly. **No IR translation happens here apart from lifting abort
/// codes to `IRNode::Var`** — the resulting `Skeleton` is purely a
/// structural recovery over unchanged bytecode.
pub(crate) fn recover(target: &FunctionTarget) -> Skeleton {
    let cfg = discover_cfg(target);
    if std::env::var("PROBE_LOOPS").is_ok() {
        let name = target
            .func_env
            .get_name()
            .display(target.global_env().symbol_pool())
            .to_string();
        eprintln!(
            "PROBE_LOOPS fn={} num_blocks={} loops_pre={:?}",
            name,
            cfg.blocks.len(),
            cfg.loops
        );
    }
    // The outer loop's recorded backedge can be smaller than a nested
    // loop's extent — when the bytecode compiler merges a nested
    // loop's break with the outer's continue, the outer ends up with a
    // single backedge from inside the nested loop. `build_while` grows
    // its own `backedge` past any such nested loop range when it runs,
    // so we hand it the raw `cfg.loops` here without a pre-pass.
    let loops = cfg.loops.clone();
    // `discover_cfg` synthesises Continue-terminator blocks at every
    // back-edge and gives them empty successors, so `cfg.successors` is
    // already an acyclic graph — post-dom analysis works on it directly
    // with no back-edge cutting required.
    let cfg_succs = &cfg.successors;
    let num_blocks = cfg.blocks.len();
    let post_doms = compute_post_dominators(cfg_succs, num_blocks);

    let mut predecessors: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for i in 0..num_blocks {
        predecessors.insert(i, Vec::new());
    }
    for (&block, succs) in cfg_succs {
        for &succ in succs {
            if succ < num_blocks {
                predecessors
                    .get_mut(&succ)
                    .expect("predecessor entry must exist")
                    .push(block);
            }
        }
    }

    if std::env::var("PROBE_CFG_ACTIVE").is_ok() {
        eprintln!(
            "PROBE_CFG build: num_blocks={} loops={:?}",
            num_blocks, loops
        );
        eprintln!("PROBE_CFG label_to_block: {:?}", cfg.label_to_block);
        for i in 0..num_blocks {
            eprintln!(
                "PROBE_CFG   block {} term={:?} preds={:?} succs={:?}",
                i,
                cfg.blocks[i].terminator,
                predecessors.get(&i).unwrap(),
                cfg_succs.get(&i).unwrap_or(&vec![])
            );
        }
        eprintln!("PROBE_CFG   post_doms: {:?}", post_doms);
    }

    let ctx = BuildContext {
        target,
        blocks: &cfg.blocks,
        label_to_block: &cfg.label_to_block,
        loops: &loops,
        post_doms: &post_doms,
        predecessors: &predecessors,
    };
    ctx.build_from(0, num_blocks)
}

struct BuildContext<'a> {
    target: &'a FunctionTarget<'a>,
    blocks: &'a [BlockCfg],
    label_to_block: &'a HashMap<Label, usize>,
    loops: &'a [LoopInfo],
    post_doms: &'a BTreeMap<usize, usize>,
    predecessors: &'a BTreeMap<usize, Vec<usize>>,
}

/// One frame in the enclosing-loop stack while building. Stored
/// bottom-up: `enclosing[0]` is the outermost, `enclosing.last()` is
/// innermost. The `level` consumed by `Termination::Continue` /
/// `Termination::Break` is computed from the innermost (level 0 =
/// innermost), so a stack of length N maps index i ↔ level N-1-i.
#[derive(Clone, Copy, Debug)]
struct EnclosingLoop {
    header: usize,
    break_target: usize,
}

/// Returns (backedge, exit_block) for a given block, if it's a loop
/// header. `exit_block` is the loop's semantic continuation entry
/// (`None` if `LoopInfo.exit_label` is `None` because the loop's
/// semantic exit couldn't be recovered — e.g., an unconditional
/// back-edge loop where the post-walk scan didn't find a
/// distinguishing Branch).
fn loop_info(
    loops: &[LoopInfo],
    label_to_block: &HashMap<Label, usize>,
    block: usize,
) -> Option<(usize, Option<usize>)> {
    loops.iter().find(|info| info.header == block).map(|info| {
        let exit_block = info
            .exit_label
            .and_then(|label| label_to_block.get(&label).copied());
        let max_backedge = *info
            .backedges
            .iter()
            .max()
            .expect("LoopInfo always has at least one backedge");
        (max_backedge, exit_block)
    })
}

fn find_convergence(
    post_doms: &BTreeMap<usize, usize>,
    branch_block: usize,
    end: usize,
) -> Option<usize> {
    post_doms.get(&branch_block).copied().filter(|&c| c < end)
}

/// Walk the enclosing stack innermost-first and return the level
/// whose loop has `target_header` as its header. Returns 0
/// (innermost) as a defensive default if no enclosing loop matches;
/// that shouldn't happen on a reducible CFG.
fn continue_level_for(enclosing: &[EnclosingLoop], target_header: usize) -> usize {
    for (i, frame) in enclosing.iter().enumerate().rev() {
        if frame.header == target_header {
            return enclosing.len() - 1 - i;
        }
    }
    0
}

/// Classify a forward-jump target as a break of some enclosing-loop
/// level, or `None` if it isn't a break. The rule: the innermost
/// enclosing loop must be broken-past
/// (`target_block >= innermost.break_target`); given that, walk
/// outward and return the largest level whose `break_target` the
/// target also matches. The "innermost-must-match" guard
/// distinguishes a real break (control flow exits the innermost
/// loop) from a forward jump that happens to land past an outer's
/// exit while still being inside the innermost — the latter is
/// body-internal, not a break.
fn break_level_for(enclosing: &[EnclosingLoop], target_block: usize) -> Option<usize> {
    let innermost = enclosing.last()?;
    if target_block < innermost.break_target {
        return None;
    }
    let mut level = 0;
    for (i, frame) in enclosing.iter().enumerate().rev().skip(1) {
        if target_block >= frame.break_target {
            level = enclosing.len() - 1 - i;
        } else {
            break;
        }
    }
    Some(level)
}

/// Grow `backedge` past every nested loop whose header sits inside
/// the current `[header, backedge]` range, iterating to a fixpoint.
/// Each iteration may pull a new nested loop into range, so deeply
/// nested fusions converge after several passes.
///
/// This subsumes the historical `expand_loop_ranges` global pre-pass
/// — same fixpoint semantics, just per-loop-being-recovered.
fn widen_backedge_past_nested_loops(loops: &[LoopInfo], header: usize, backedge: usize) -> usize {
    let mut backedge = backedge;
    loop {
        let mut grew = false;
        for inner in loops {
            if inner.header == header {
                continue;
            }
            if inner.header < header || inner.header > backedge {
                continue;
            }
            let inner_max = *inner
                .backedges
                .iter()
                .max()
                .expect("LoopInfo always has at least one backedge");
            if inner_max > backedge {
                backedge = inner_max;
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    backedge
}

impl<'a> BuildContext<'a> {
    /// Lift a temp index to an `IRNode::Var` at the boundary between IR-free
    /// recovery and IR-bearing emission. A trivial operation (no
    /// `ir_translator`, no `ProgramBuilder` side effects) — the abort
    /// code's IR is materialised here so the leaf-position `Termination`
    /// can carry it through to emit.
    fn temp_to_var(&self, t: TempIndex) -> IRNode {
        IRNode::Var(temp_id(self.target, t))
    }

    /// Walk every block in the loop interior `[header, exit_block)`
    /// and check whether any forward exit (Branch arm, Jump, or Switch
    /// case) targets a block strictly past `exit_block` but still
    /// before `end`. Used by `build_while` to detect the fused
    /// multi-target-break pattern produced by the Move bytecode
    /// optimizer (see comment at the call site).
    fn has_exits_past_exit_block(&self, header: usize, exit_block: usize, end: usize) -> bool {
        for idx in header..exit_block {
            let block = &self.blocks[idx];
            match &block.terminator {
                Terminator::Branch {
                    then_label,
                    else_label,
                    ..
                } => {
                    let then_target = self.label_to_block[then_label];
                    let else_target = self.label_to_block[else_label];
                    if (then_target > exit_block && then_target < end)
                        || (else_target > exit_block && else_target < end)
                    {
                        return true;
                    }
                }
                Terminator::Jump { target } => {
                    let t = self.label_to_block[target];
                    if t > exit_block && t < end {
                        return true;
                    }
                }
                Terminator::Switch { cases, .. } => {
                    for label in cases {
                        let t = self.label_to_block[label];
                        if t > exit_block && t < end {
                            return true;
                        }
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn build_from(&self, start: usize, end: usize) -> Skeleton {
        self.build_from_in(start, end, &[])
    }

    fn build_from_in(&self, start: usize, end: usize, enclosing: &[EnclosingLoop]) -> Skeleton {
        if start >= end {
            return Skeleton::Seq(Vec::new());
        }

        if let Some((backedge, semantic_exit)) = loop_info(self.loops, self.label_to_block, start) {
            return self.build_while(start, backedge, end, semantic_exit, enclosing);
        }

        self.build_block(start, end, enclosing)
    }

    fn build_while(
        &self,
        header: usize,
        backedge: usize,
        end: usize,
        semantic_exit: Option<usize>,
        enclosing: &[EnclosingLoop],
    ) -> Skeleton {
        // The bytecode optimizer can fuse "exit inner; continue outer"
        // into a direct jump that registers as our backedge but lands
        // inside an inner loop, leaving our recorded backedge below
        // that inner loop's extent. `widen_backedge_past_nested_loops`
        // grows `backedge` past every nested loop whose header sits
        // inside our current range, iterating to a fixpoint.
        let backedge = widen_backedge_past_nested_loops(self.loops, header, backedge);
        let mut exit_block = backedge + 1;

        if std::env::var("PROBE_CFG_ACTIVE").is_ok() {
            eprintln!(
                "PROBE_CFG build_while header={} backedge={} end={} initial_exit={} semantic_exit={:?}",
                header, backedge, end, exit_block, semantic_exit
            );
        }

        // Absorb break-target blocks that lie between the backedge and
        // the loop's semantic exit point — blocks whose predecessors are
        // all within the loop interior, AND which are not the semantic
        // exit block itself.
        while exit_block < end {
            if semantic_exit == Some(exit_block) {
                break;
            }
            let preds = &self.predecessors[&exit_block];
            let all_from_loop = preds.iter().all(|&p| p >= header && p < exit_block);
            if all_from_loop {
                exit_block += 1;
            } else {
                break;
            }
        }

        // Multi-target break detection: the bytecode optimizer can fuse
        // an inner-break-with-trailing-computation into the post-loop
        // region. The result: some forward exits inside the loop body
        // target the formal semantic_exit (where the trailing
        // computation lives), while others jump past it (skipping the
        // trailing computation). Treating this as a single after-func
        // produces a body that unconditionally executes the trailing
        // computation — but the computation references SSA temps that
        // aren't bound on the bypass path, and Lake rejects it.
        //
        // When detected, continue absorbing past the formal
        // semantic_exit. The trailing computation lands inside the
        // loop body, where its SSA inputs are correctly scoped per
        // branch, and only the genuine common continuation remains as
        // the after-func.
        if self.has_exits_past_exit_block(header, exit_block, end) {
            while exit_block < end {
                let preds = &self.predecessors[&exit_block];
                let all_from_loop = preds.iter().all(|&p| p >= header && p < exit_block);
                if all_from_loop {
                    exit_block += 1;
                } else {
                    break;
                }
            }
        }

        if std::env::var("PROBE_CFG_ACTIVE").is_ok() {
            eprintln!("PROBE_CFG build_while final exit_block={}", exit_block);
        }

        let mut inner_enclosing: Vec<EnclosingLoop> = enclosing.to_vec();
        inner_enclosing.push(EnclosingLoop {
            header,
            break_target: exit_block,
        });
        let header_block = self.blocks[header].clone();
        let loop_body = self.build_block(header, exit_block, &inner_enclosing);
        let while_skel = Skeleton::While {
            header: header_block,
            loop_body: Box::new(loop_body),
        };

        if exit_block < end {
            Skeleton::Seq(vec![
                while_skel,
                self.build_from_in(exit_block, end, enclosing),
            ])
        } else {
            while_skel
        }
    }

    /// Classify a Branch/Switch arm whose target is `target_block` into
    /// either a terminating leaf (Continue or Break) or the result of
    /// recursively building the structure starting at `target_block`.
    fn classify_arm(
        &self,
        target_block: usize,
        sub_end: usize,
        enclosing: &[EnclosingLoop],
    ) -> Skeleton {
        if let Some((i, _)) = enclosing
            .iter()
            .enumerate()
            .rev()
            .find(|(_, frame)| frame.header == target_block)
        {
            return Skeleton::Term(Termination::Continue {
                level: enclosing.len() - 1 - i,
            });
        }
        if let Some(level) = break_level_for(enclosing, target_block) {
            return Skeleton::Term(Termination::Break { level });
        }
        self.build_from_in(target_block, sub_end, enclosing)
    }

    fn build_block(&self, idx: usize, end: usize, enclosing: &[EnclosingLoop]) -> Skeleton {
        if idx >= end {
            return Skeleton::Seq(Vec::new());
        }

        let block = &self.blocks[idx];

        match &block.terminator {
            Terminator::Return { .. } => Skeleton::Seq(vec![
                Skeleton::Block(block.clone()),
                Skeleton::Term(Termination::Return),
            ]),
            Terminator::Abort { code_temp } => {
                let code = code_temp.map(|t| self.temp_to_var(t));
                Skeleton::Seq(vec![
                    Skeleton::Block(block.clone()),
                    Skeleton::Term(Termination::Abort { code }),
                ])
            }
            Terminator::Continue { target_header } => {
                let level = continue_level_for(enclosing, *target_header);
                Skeleton::Seq(vec![
                    Skeleton::Block(block.clone()),
                    Skeleton::Term(Termination::Continue { level }),
                ])
            }
            Terminator::Fallthrough => {
                // A Fallthrough whose next block is the loop's exit
                // (or further) is an implicit break: control walks
                // off the end of an interior path and out of the
                // loop. Without this, the resulting Skeleton has a
                // body leaf with no termination, so emit produces a
                // while_func body that doesn't end in a Continue /
                // Break / Return on every path — Lake then sees a
                // type mismatch (or a missing call to after_func)
                // depending on the surrounding shape. This matters
                // specifically after `build_while` absorbs past the
                // formal semantic_exit on the multi-target-break
                // pattern: the absorbed body's last statement may
                // be a Fallthrough that crosses the new exit_block.
                if let Some(level) = break_level_for(enclosing, idx + 1) {
                    return Skeleton::Seq(vec![
                        Skeleton::Block(block.clone()),
                        Skeleton::Term(Termination::Break { level }),
                    ]);
                }
                let rest = self.build_from_in(idx + 1, end, enclosing);
                Skeleton::Seq(vec![Skeleton::Block(block.clone()), rest])
            }
            Terminator::Jump { target } => {
                let target_block = self.label_to_block[target];

                if let Some((i, _)) = enclosing
                    .iter()
                    .enumerate()
                    .rev()
                    .find(|(_, frame)| frame.header == target_block)
                {
                    return Skeleton::Seq(vec![
                        Skeleton::Block(block.clone()),
                        Skeleton::Term(Termination::Continue {
                            level: enclosing.len() - 1 - i,
                        }),
                    ]);
                }

                if let Some(level) = break_level_for(enclosing, target_block) {
                    return Skeleton::Seq(vec![
                        Skeleton::Block(block.clone()),
                        Skeleton::Term(Termination::Break { level }),
                    ]);
                }

                if target_block >= end {
                    // Forward jump past end (sub-range terminator) — the
                    // block runs but produces no termination of its own.
                    return Skeleton::Block(block.clone());
                }

                if target_block > idx {
                    let rest = self.build_from_in(target_block, end, enclosing);
                    return Skeleton::Seq(vec![Skeleton::Block(block.clone()), rest]);
                }

                // Backward jump that wasn't caught as a Continue above —
                // unreachable on well-formed Move bytecode; emit
                // innermost continue defensively.
                Skeleton::Seq(vec![
                    Skeleton::Block(block.clone()),
                    Skeleton::Term(Termination::Continue { level: 0 }),
                ])
            }
            Terminator::Branch {
                then_label,
                else_label,
                ..
            } => {
                let then_start = self.label_to_block[then_label];
                let else_start = self.label_to_block[else_label];
                let convergence = find_convergence(self.post_doms, idx, end);
                let branch_end = convergence.unwrap_or(end);

                let then_branch = self.classify_arm(then_start, branch_end, enclosing);
                let else_branch = self.classify_arm(else_start, branch_end, enclosing);

                let if_skel = Skeleton::If {
                    cond_block: block.clone(),
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                };

                if let Some(conv) = convergence {
                    Skeleton::Seq(vec![if_skel, self.build_from_in(conv, end, enclosing)])
                } else {
                    if_skel
                }
            }
            Terminator::Switch { cases, .. } => {
                let convergence = find_convergence(self.post_doms, idx, end);
                let branch_end = convergence.unwrap_or(end);

                let case_skeletons: Vec<Skeleton> = cases
                    .iter()
                    .map(|label| {
                        let case_start = self.label_to_block[label];
                        self.classify_arm(case_start, branch_end, enclosing)
                    })
                    .collect();

                let switch_skel = Skeleton::Switch {
                    scrutinee_block: block.clone(),
                    cases: case_skeletons,
                };

                if let Some(conv) = convergence {
                    Skeleton::Seq(vec![switch_skel, self.build_from_in(conv, end, enclosing)])
                } else {
                    switch_skel
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Post-dominator computation
// ---------------------------------------------------------------------------

type CFG = BTreeMap<usize, Vec<usize>>;

fn compute_post_dominators(cfg: &CFG, num_blocks: usize) -> BTreeMap<usize, usize> {
    if num_blocks == 0 {
        return BTreeMap::new();
    }

    use petgraph::algo::dominators::simple_fast;
    use petgraph::graph::{DiGraph, NodeIndex};

    let mut graph: DiGraph<usize, ()> = DiGraph::new();
    let mut block_to_node: BTreeMap<usize, NodeIndex> = BTreeMap::new();

    for i in 0..num_blocks {
        let n = graph.add_node(i);
        block_to_node.insert(i, n);
    }

    // Synthetic super-exit unifies multiple real exit blocks
    // (Return/Abort/etc.) into a single root for the reverse CFG.
    // Sentinel weight usize::MAX is distinguishable from any real block
    // index when reading dominators back.
    let super_exit = graph.add_node(usize::MAX);

    for i in 0..num_blocks {
        let from = block_to_node[&i];
        let succs = cfg.get(&i).map(|v| v.as_slice()).unwrap_or(&[]);
        if succs.is_empty() {
            // In the reverse graph, super_exit -> exit_block.
            graph.add_edge(super_exit, from, ());
        } else {
            for &j in succs {
                if j < num_blocks {
                    // Forward edge i -> j becomes reverse edge j -> i.
                    graph.add_edge(block_to_node[&j], from, ());
                }
            }
        }
    }

    let dominators = simple_fast(&graph, super_exit);

    let mut ipost_dom: BTreeMap<usize, usize> = BTreeMap::new();
    for i in 0..num_blocks {
        let Some(idom_node) = dominators.immediate_dominator(block_to_node[&i]) else {
            continue;
        };
        if idom_node == super_exit {
            continue;
        }
        let idom_block = graph[idom_node];
        if idom_block != usize::MAX {
            ipost_dom.insert(i, idom_block);
        }
    }

    ipost_dom
}

#[cfg(test)]
mod post_dom_tests {
    use super::*;

    fn cfg_from(edges: &[(usize, &[usize])]) -> CFG {
        let mut cfg: CFG = BTreeMap::new();
        for (block, succs) in edges {
            cfg.insert(*block, succs.to_vec());
        }
        cfg
    }

    #[test]
    fn empty() {
        assert!(compute_post_dominators(&cfg_from(&[]), 0).is_empty());
    }

    #[test]
    fn linear() {
        let cfg = cfg_from(&[(0, &[1]), (1, &[2]), (2, &[])]);
        let pd = compute_post_dominators(&cfg, 3);
        assert_eq!(pd.get(&0), Some(&1));
        assert_eq!(pd.get(&1), Some(&2));
        assert_eq!(pd.get(&2), None);
    }

    #[test]
    fn diamond() {
        let cfg = cfg_from(&[(0, &[1, 2]), (1, &[3]), (2, &[3]), (3, &[])]);
        let pd = compute_post_dominators(&cfg, 4);
        assert_eq!(pd.get(&0), Some(&3));
        assert_eq!(pd.get(&1), Some(&3));
        assert_eq!(pd.get(&2), Some(&3));
        assert_eq!(pd.get(&3), None);
    }

    #[test]
    fn loop_with_exit() {
        let cfg = cfg_from(&[(0, &[1]), (1, &[2, 3]), (2, &[1]), (3, &[])]);
        let pd = compute_post_dominators(&cfg, 4);
        assert_eq!(pd.get(&0), Some(&1));
        assert_eq!(pd.get(&1), Some(&3));
        assert_eq!(pd.get(&2), Some(&1));
        assert_eq!(pd.get(&3), None);
    }

    #[test]
    fn multi_exit() {
        let cfg = cfg_from(&[(0, &[1, 2]), (1, &[]), (2, &[])]);
        let pd = compute_post_dominators(&cfg, 3);
        assert_eq!(pd.get(&0), None);
        assert_eq!(pd.get(&1), None);
        assert_eq!(pd.get(&2), None);
    }

    #[test]
    fn nested_branch() {
        let cfg = cfg_from(&[
            (0, &[1, 4]),
            (1, &[2, 3]),
            (2, &[4]),
            (3, &[4]),
            (4, &[5]),
            (5, &[]),
        ]);
        let pd = compute_post_dominators(&cfg, 6);
        assert_eq!(pd.get(&0), Some(&4));
        assert_eq!(pd.get(&1), Some(&4));
        assert_eq!(pd.get(&2), Some(&4));
        assert_eq!(pd.get(&3), Some(&4));
        assert_eq!(pd.get(&4), Some(&5));
        assert_eq!(pd.get(&5), None);
    }
}

#[cfg(test)]
mod recovery_tests {
    use super::*;

    fn frame(header: usize, break_target: usize) -> EnclosingLoop {
        EnclosingLoop {
            header,
            break_target,
        }
    }

    fn loop_info_for(header: usize, backedges: Vec<usize>, exit: Option<u16>) -> LoopInfo {
        LoopInfo {
            header,
            backedges,
            exit_label: exit.map(|v| Label::new(v as usize)),
        }
    }

    // ---------------------------------------------------------------
    // continue_level_for
    // ---------------------------------------------------------------

    #[test]
    fn continue_level_empty_stack_defaults_to_zero() {
        assert_eq!(continue_level_for(&[], 7), 0);
    }

    #[test]
    fn continue_level_innermost_match() {
        // stack = [outer, inner]; innermost is index 1, level 0.
        let stack = [frame(0, 99), frame(10, 50)];
        assert_eq!(continue_level_for(&stack, 10), 0);
    }

    #[test]
    fn continue_level_outer_match() {
        // stack = [outer, inner]; outer is index 0, level 1.
        let stack = [frame(0, 99), frame(10, 50)];
        assert_eq!(continue_level_for(&stack, 0), 1);
    }

    #[test]
    fn continue_level_three_deep_middle_match() {
        // stack = [o1, o2, i]; matching o2 (index 1) gives level 1.
        let stack = [frame(0, 200), frame(10, 100), frame(20, 50)];
        assert_eq!(continue_level_for(&stack, 10), 1);
    }

    #[test]
    fn continue_level_no_match_defaults_to_innermost() {
        let stack = [frame(0, 99), frame(10, 50)];
        assert_eq!(continue_level_for(&stack, 999), 0);
    }

    // ---------------------------------------------------------------
    // break_level_for
    // ---------------------------------------------------------------

    #[test]
    fn break_level_empty_stack_is_none() {
        assert_eq!(break_level_for(&[], 5), None);
    }

    #[test]
    fn break_level_innermost_only() {
        // single loop, break-target = 50; jumping to 50 is a level-0 break.
        let stack = [frame(0, 50)];
        assert_eq!(break_level_for(&stack, 50), Some(0));
    }

    #[test]
    fn break_level_below_innermost_is_none() {
        // jump to 10, but innermost break_target is 50 — body-internal,
        // not a break.
        let stack = [frame(0, 50)];
        assert_eq!(break_level_for(&stack, 10), None);
    }

    #[test]
    fn break_level_innermost_only_when_outer_break_unmet() {
        // outer break_target = 200, inner break_target = 50.
        // Jump to 100: past innermost (50) but not past outer (200).
        // → level 0 (innermost only).
        let stack = [frame(0, 200), frame(10, 50)];
        assert_eq!(break_level_for(&stack, 100), Some(0));
    }

    #[test]
    fn break_level_walks_outward_to_largest_match() {
        // outer break_target = 200, inner break_target = 50.
        // Jump to 250: past both → level 1 (outer).
        let stack = [frame(0, 200), frame(10, 50)];
        assert_eq!(break_level_for(&stack, 250), Some(1));
    }

    #[test]
    fn break_level_skips_intermediate_when_target_outpasses_outermost() {
        // o1 break = 300, o2 break = 200, i break = 50.
        // Jump to 350: past all three → level 2 (outermost).
        let stack = [frame(0, 300), frame(10, 200), frame(20, 50)];
        assert_eq!(break_level_for(&stack, 350), Some(2));
    }

    #[test]
    fn break_level_innermost_must_match_first() {
        // i break = 50. Jump to 30: not past innermost → None,
        // even though it might be past some hypothetical outer.
        let stack = [frame(0, 100), frame(10, 50)];
        assert_eq!(break_level_for(&stack, 30), None);
    }

    // ---------------------------------------------------------------
    // widen_backedge_past_nested_loops
    // ---------------------------------------------------------------

    #[test]
    fn widen_no_nested_loops_is_noop() {
        let loops = vec![loop_info_for(0, vec![10], Some(11))];
        assert_eq!(widen_backedge_past_nested_loops(&loops, 0, 10), 10);
    }

    #[test]
    fn widen_unrelated_loop_is_noop() {
        // outer at 0..10, an unrelated loop at 100..110 — neither
        // contains the other.
        let loops = vec![
            loop_info_for(0, vec![10], Some(11)),
            loop_info_for(100, vec![110], Some(111)),
        ];
        assert_eq!(widen_backedge_past_nested_loops(&loops, 0, 10), 10);
    }

    #[test]
    fn widen_pulls_in_nested_loop_with_larger_max() {
        // Outer recorded backedge = 35 (a fused continue-outer from
        // inside inner). Inner's natural backedge = 41, larger.
        // Outer should grow to 41.
        let loops = vec![
            loop_info_for(0, vec![35], Some(60)),
            loop_info_for(20, vec![41], Some(50)),
        ];
        assert_eq!(widen_backedge_past_nested_loops(&loops, 0, 35), 41);
    }

    #[test]
    fn widen_iterates_to_fixpoint_for_three_deep() {
        // o1 backedge = 35 (only registered backedge: a fused jump from
        // inside i). o2 backedge = 60. i backedge = 41.
        // Iter 1: o1 sees o2 (header 10 in [0, 35], max 60 > 35) and i
        //         (header 20 in [0, 35], max 41 > 35). Grow to 60.
        // Iter 2: nothing new is in range with a larger max.
        // Final: 60.
        let loops = vec![
            loop_info_for(0, vec![35], Some(80)),
            loop_info_for(10, vec![60], Some(70)),
            loop_info_for(20, vec![41], Some(50)),
        ];
        assert_eq!(widen_backedge_past_nested_loops(&loops, 0, 35), 60);
    }

    #[test]
    fn widen_skips_self() {
        // The widen pass must skip the loop being widened itself,
        // otherwise it would count its own backedge as a "nested" one
        // and never terminate when there's only the one loop.
        let loops = vec![loop_info_for(0, vec![10, 20], Some(30))];
        assert_eq!(widen_backedge_past_nested_loops(&loops, 0, 10), 10);
    }

    #[test]
    fn widen_does_not_pull_outer_into_inner() {
        // Inner is being widened. Outer's max is past inner's range,
        // but outer's header is < inner's header — outer is not
        // nested in inner, so inner shouldn't grow.
        let loops = vec![
            loop_info_for(0, vec![100], Some(101)),
            loop_info_for(20, vec![50], Some(51)),
        ];
        assert_eq!(widen_backedge_past_nested_loops(&loops, 20, 50), 50);
    }

    // ---------------------------------------------------------------
    // loop_info
    // ---------------------------------------------------------------

    #[test]
    fn loop_info_resolves_exit_via_label_map() {
        let loops = vec![loop_info_for(0, vec![10], Some(7))];
        let mut label_to_block = HashMap::new();
        label_to_block.insert(Label::new(7), 11);
        assert_eq!(loop_info(&loops, &label_to_block, 0), Some((10, Some(11))),);
    }

    #[test]
    fn loop_info_returns_none_exit_when_label_not_in_map() {
        // exit_label is `None` (unconditional Jump back-edge whose
        // post-walk recovery didn't find a distinguishing Branch).
        let loops = vec![loop_info_for(0, vec![10], None)];
        let label_to_block = HashMap::new();
        assert_eq!(loop_info(&loops, &label_to_block, 0), Some((10, None)));
    }

    #[test]
    fn loop_info_takes_max_of_backedges() {
        // Multiple backedges → return the max.
        let loops = vec![loop_info_for(0, vec![5, 12, 7], Some(20))];
        let mut label_to_block = HashMap::new();
        label_to_block.insert(Label::new(20), 21);
        assert_eq!(loop_info(&loops, &label_to_block, 0), Some((12, Some(21))),);
    }

    #[test]
    fn loop_info_returns_none_when_block_is_not_a_header() {
        let loops = vec![loop_info_for(0, vec![10], Some(11))];
        let label_to_block = HashMap::new();
        assert_eq!(loop_info(&loops, &label_to_block, 5), None);
    }
}
