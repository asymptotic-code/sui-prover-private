//! Pre-structuring labeled-block analysis.
//!
//! Computes, for each Jump-edge in the function CFG, a classification:
//! `Continue` / `Break` / `ReturnFromBlock` / `Sequential`. Also
//! identifies labeled-block scopes (entry/exit/members) via
//! post-dominator analysis.
//!
//! The structurer (`structurer.rs`) consumes this side table instead
//! of computing detection inline during recursion. This decouples
//! detection from structuring and lets us catch labeled-block patterns
//! that the in-recursion heuristics miss (e.g., `find_index!`'s
//! macro shape where the natural exit_succ has a non-Jump terminator).

use std::collections::{BTreeMap, BTreeSet};

use move_stackless_bytecode::graph::NaturalLoop;
use move_stackless_bytecode::stackless_bytecode::Bytecode;
use move_stackless_bytecode::stackless_control_flow_graph::{
    BlockContent, BlockId, StacklessControlFlowGraph,
};

/// Side table produced by Pass 1; consumed by the structurer.
#[derive(Debug, Default, Clone)]
pub struct LabelMap {
    /// For each `(source_block, target_block)` outgoing edge from
    /// the source's terminator: how the structurer should classify
    /// this edge. Missing entries mean "treat as sequential / no
    /// special classification".
    pub edge_kinds: BTreeMap<(BlockId, BlockId), EdgeKind>,

    /// Labeled-block scopes by their exit BlockId.
    pub scopes_by_exit: BTreeMap<BlockId, LabelScope>,

    /// For each block B, the list of labeled-block exits whose scope
    /// contains B, ordered innermost-first. Computed by walking B's
    /// immediate-post-dominator chain.
    pub block_label_stack: BTreeMap<BlockId, Vec<BlockId>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EdgeKind {
    /// Target is the header of the `loop_level`-th enclosing loop.
    Continue { loop_level: u32 },
    /// Target is the natural exit_succ of the `loop_level`-th
    /// enclosing loop.
    Break { loop_level: u32 },
    /// Target is the exit of the `label_level`-th enclosing labeled-
    /// block scope.
    ReturnFromBlock { label_level: u32 },
}

#[derive(Debug, Clone)]
pub struct LabelScope {
    /// The labeled-block's exit BlockId — every Jump targeting this
    /// block from inside the scope is a ReturnFromBlock.
    pub exit: BlockId,
    /// The set of blocks B for which `exit` is in B's
    /// imm-post-dom chain (strict — excluding `exit` itself).
    pub members: BTreeSet<BlockId>,
}

/// Run the two-pass analysis. `loops` is the natural-loop list from
/// `find_natural_loops` (translated into the forward CFG's block-id
/// space already).
pub fn analyze(
    code: &[Bytecode],
    forward_cfg: &StacklessControlFlowGraph,
    backward_cfg: &StacklessControlFlowGraph,
    loops: &[NaturalLoop<BlockId>],
) -> LabelMap {
    // Emergency bypass: set FOXY_DISABLE_LABEL_ANALYSIS=1 to make
    // analyze() return an empty map. Useful to A/B-test whether
    // regressions are caused by label_analysis or upstream IR
    // pipeline changes.
    if std::env::var_os("FOXY_DISABLE_LABEL_ANALYSIS").is_some() {
        return LabelMap::default();
    }
    // -----------------------------------------------------------------
    // Pass A — gather Jump-edge raw targets, identify exit_succ per loop
    // -----------------------------------------------------------------
    //
    // For each loop, compute its natural exit_succ (the block reached
    // when the loop's deciding cond is false). We reuse the same
    // discovery the structurer does in `find_loop_decision`: walk the
    // post-dom chain from loop_header upward, look for an in-body
    // block with a Branch where one arm is in-body and the other is
    // out-of-body.
    let mut loop_exit_succ: BTreeMap<BlockId, BlockId> = BTreeMap::new();
    let mut loop_body_of: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();
    for l in loops {
        loop_body_of.insert(l.loop_header, l.loop_body.iter().copied().collect());
        if let Some(es) =
            find_exit_succ(l.loop_header, &l.loop_body, code, forward_cfg, backward_cfg)
        {
            loop_exit_succ.insert(l.loop_header, es);
        }
    }

    // -----------------------------------------------------------------
    // Pass B — for each block, compute loop_stack at that block.
    // loop_stack[B] = list of loops containing B (innermost first).
    // -----------------------------------------------------------------
    let mut loop_stack_at: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    let all_blocks: Vec<BlockId> = forward_cfg.blocks();
    for &b in &all_blocks {
        let mut stack: Vec<(usize, BlockId)> = Vec::new();
        for l in loops {
            if l.loop_body.contains(&b) {
                stack.push((l.loop_body.len(), l.loop_header));
            }
        }
        // Innermost = smallest body size.
        stack.sort_by_key(|(sz, _)| *sz);
        loop_stack_at.insert(b, stack.into_iter().map(|(_, h)| h).collect());
    }

    // -----------------------------------------------------------------
    // Pass C — collect candidate Jump edges and classify into
    // Continue / Break / (potentially) ReturnFromBlock.
    // -----------------------------------------------------------------
    //
    // "Edges" come from block terminators:
    //   - Bytecode::Jump(target_label) → one edge
    //   - Bytecode::Branch(then_label, else_label, _) → two edges
    //   - Bytecode::VariantSwitch(_, labels) → many edges
    //   - Bytecode::Ret / Bytecode::Abort → no edges classified here
    //     (they have their own Termination variants).
    //
    // For now we compute edges directly from the forward CFG's
    // successor relation — every successor of B is an edge target.
    //
    // We classify each (S, T) edge:
    //   - T == any loop header in S's loop_stack          → Continue
    //   - T == any loop's exit_succ in S's loop_stack     → Break
    //   - Otherwise, if T is outside S's innermost loop   → ReturnFromBlock candidate
    //   - Otherwise (same-loop forward goto)              → no entry (treated sequentially)
    let mut candidate_return_targets: BTreeSet<BlockId> = BTreeSet::new();
    let mut edge_classifications: BTreeMap<(BlockId, BlockId), EdgeKind> = BTreeMap::new();
    for &s in &all_blocks {
        if matches!(forward_cfg.content(s), BlockContent::Dummy) {
            continue;
        }
        let s_stack = loop_stack_at.get(&s).cloned().unwrap_or_default();
        for &t in forward_cfg.successors(s).iter() {
            if matches!(forward_cfg.content(t), BlockContent::Dummy) {
                continue;
            }
            // Continue?
            if let Some(level) = s_stack.iter().position(|h| *h == t) {
                edge_classifications.insert(
                    (s, t),
                    EdgeKind::Continue {
                        loop_level: level as u32,
                    },
                );
                continue;
            }
            // Break? T is the natural exit_succ of one of S's enclosing loops.
            if let Some(level) = s_stack
                .iter()
                .position(|h| loop_exit_succ.get(h) == Some(&t))
            {
                edge_classifications.insert(
                    (s, t),
                    EdgeKind::Break {
                        loop_level: level as u32,
                    },
                );
                continue;
            }
            // T is outside S's innermost loop AND not exit_succ → candidate
            // ReturnFromBlock. We apply the same criterion the original
            // emit_while detection used (which produced 313/326 stable):
            // bt's jump-only chain must share a block (!= exit_succ of
            // the enclosing loop) with exit_succ's fall-through chain.
            // The shared block is the labeled-block exit.
            //
            // This is strict on purpose -- the broader "walk to merge
            // point" rule produces too many false positives (synthetic
            // landing pads for multiple unlabeled breaks coalescing at
            // a common return point look identical to labeled-block
            // exits at the post-dom-only level).
            if !s_stack.is_empty() {
                let innermost = s_stack[0];
                let innermost_body = loop_body_of.get(&innermost);
                let inner_exit_succ = loop_exit_succ.get(&innermost).copied();
                if let (Some(body), Some(es)) = (innermost_body, inner_exit_succ) {
                    if !body.contains(&t) {
                        if let Some(exit) = find_label_exit_via_merge(t, es, code, forward_cfg) {
                            candidate_return_targets.insert(exit);
                        }
                    }
                }
            }
        }
    }

    // -----------------------------------------------------------------
    // Pass D — identify labeled-block scopes.
    // -----------------------------------------------------------------
    //
    // A block B is a member of scope X iff
    //   (1) X.exit is on B's imm-post-dom chain (B always reaches X),
    //         AND
    //   (2) X.entry forward-dominates B (B is inside the scope's
    //         control-flow region, not before its entry).
    //
    // X.entry is the deepest common forward-dominator of all forward
    // predecessors of X.exit. For find_index! that's the loop header;
    // for any other labeled construct it's whichever block dominates
    // every exit-jump source.
    //
    // Earlier versions only checked (1), which made every block on
    // the path TO the macro a scope member (the pre-macro asserts
    // also post-dominate to the macro's exit because they always
    // reach it before returning).
    // A genuine labeled-block scope (find_index!-style macro) is
    // anchored on its loop: the break source lives inside the loop and
    // the natural "not found" exit is the loop's exit_succ, so the
    // common forward-dominator of the scope's exit-predecessors is the
    // loop header. We use that below to reject false positives.
    let loop_headers: BTreeSet<BlockId> = loops.iter().map(|l| l.loop_header).collect();

    let mut scopes_by_exit: BTreeMap<BlockId, LabelScope> = BTreeMap::new();
    let mut scope_entry: BTreeMap<BlockId, BlockId> = BTreeMap::new();
    for &t in &candidate_return_targets {
        // Forward predecessors of t = backward_cfg.successors(t), but
        // backward_cfg uses ignore_return_abort=false, so its
        // successors are the real CFG predecessors. Filter out
        // dummies. Compute the deepest common forward-dominator of
        // those predecessors.
        let preds: Vec<BlockId> = backward_cfg
            .successors(t)
            .iter()
            .copied()
            .filter(|&p| !matches!(forward_cfg.content(p), BlockContent::Dummy))
            .collect();
        let Some(entry) = common_forward_dominator(&preds, forward_cfg) else {
            // No common dominator -> can't establish a well-formed
            // scope. Treat as ordinary control flow.
            continue;
        };
        // Anchor check: the scope entry must be a natural-loop header.
        // For a real find_index!-style labeled block the break (inside
        // the loop) and the natural exit (the loop's exit_succ) both
        // bottom out at the loop header, so their common dominator IS
        // the header. When the entry is some OTHER block -- e.g. an
        // `if`/`else` branch dominating two independent loops whose
        // exits both reach `t` (the post-if-else merge) -- there is no
        // labeled block: it is ordinary control flow after a
        // conditional. Wrapping it strands the loops' live-out
        // threading (each break / natural exit returns the post-merge
        // phi temp, which is unbound inside the extracted loop helpers
        // -> UnboundVariable). The plain loop-extraction path handles
        // that shape correctly, so leave it unclassified.
        if !loop_headers.contains(&entry) {
            continue;
        }
        scopes_by_exit.insert(
            t,
            LabelScope {
                exit: t,
                members: BTreeSet::new(),
            },
        );
        scope_entry.insert(t, entry);
    }

    // Precompute each non-dummy block's forward-dom set so the
    // member check is O(scope_count) per block instead of walking
    // the chain repeatedly. For each B, dom_set[B] = { B's forward
    // dominators, including B itself }.
    let mut dom_set: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();
    for &b in &all_blocks {
        if matches!(forward_cfg.content(b), BlockContent::Dummy) {
            continue;
        }
        let chain = forward_dom_chain(b, forward_cfg);
        dom_set.insert(b, chain.into_iter().collect());
    }

    let mut block_label_stack: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    for &b in &all_blocks {
        if matches!(forward_cfg.content(b), BlockContent::Dummy) {
            continue;
        }
        let b_doms = dom_set.get(&b).cloned().unwrap_or_default();
        // Walk imm-post-dom chain from b upward, collecting only
        // candidate exits whose entry forward-dominates b.
        let mut chain: Vec<BlockId> = Vec::new();
        let mut cursor = b;
        const MAX_CHAIN: usize = 1024;
        for _ in 0..MAX_CHAIN {
            let pd = match backward_cfg.find_immediate_dominator(cursor) {
                Some(p) => p,
                None => break,
            };
            if pd == cursor {
                break;
            }
            if matches!(forward_cfg.content(pd), BlockContent::Dummy) {
                break;
            }
            if candidate_return_targets.contains(&pd) {
                // Only include this scope if its entry dominates b.
                let entry_dominates = match scope_entry.get(&pd) {
                    Some(entry) => b_doms.contains(entry),
                    None => false,
                };
                if entry_dominates {
                    chain.push(pd);
                    if let Some(scope) = scopes_by_exit.get_mut(&pd) {
                        scope.members.insert(b);
                    }
                }
            }
            cursor = pd;
        }
        block_label_stack.insert(b, chain);
    }

    // -----------------------------------------------------------------
    // Pass E — assign label_level to each candidate ReturnFromBlock
    // edge using block_label_stack[S].
    //
    // A Jump (S, T) is a ReturnFromBlock iff:
    //   - T IS the scope exit X (direct exit jump), OR
    //   - T is a single-successor trampoline whose forward Jump-only
    //     chain leads to X (S effectively exits via the trampoline).
    //
    // T being a generic interior member of the scope is NOT enough --
    // a Branch arm landing on another member is sequential intra-scope
    // flow, not an exit. Earlier versions classified every
    // member-targeting edge as ReturnFromBlock; that misclassified the
    // "ok" arms of pre-macro assertions (e.g. `assert!(p, EBad)`
    // where the ok arm jumps to the next assertion's block, both of
    // which are scope members) and ended up emitting
    // Term(ReturnFromBlock) at the first assertion -- truncating the
    // labeled body to the first if.
    // -----------------------------------------------------------------

    // Resolve a target block T to a scope exit, if T is either the
    // exit directly OR a Jump-only trampoline ending at the exit.
    // Returns None for plain interior members / non-trampoline jumps.
    let resolve_to_exit = |t: BlockId| -> Option<BlockId> {
        if scopes_by_exit.contains_key(&t) {
            return Some(t);
        }
        let chain = jump_only_chain(t, code, forward_cfg);
        for &b in &chain {
            if scopes_by_exit.contains_key(&b) {
                return Some(b);
            }
        }
        None
    };

    for &s in &all_blocks {
        if matches!(forward_cfg.content(s), BlockContent::Dummy) {
            continue;
        }
        let s_label_stack = block_label_stack.get(&s).cloned().unwrap_or_default();
        for &t in forward_cfg.successors(s).iter() {
            if matches!(forward_cfg.content(t), BlockContent::Dummy) {
                continue;
            }
            // Skip if already classified (Continue/Break wins).
            if edge_classifications.contains_key(&(s, t)) {
                continue;
            }
            // Find the scope exit T resolves to (direct or via
            // trampoline). Interior members do NOT resolve.
            let Some(scope_exit) = resolve_to_exit(t) else {
                continue;
            };
            // The scope exit must be on S's label_stack (i.e., S is
            // inside that scope). Otherwise this Jump isn't a
            // ReturnFromBlock from S's perspective.
            if let Some(level) = s_label_stack.iter().position(|exit| *exit == scope_exit) {
                edge_classifications.insert(
                    (s, t),
                    EdgeKind::ReturnFromBlock {
                        label_level: level as u32,
                    },
                );
            }
        }
    }

    LabelMap {
        edge_kinds: edge_classifications,
        scopes_by_exit,
        block_label_stack,
    }
}

/// Forward-dominator chain from `b`, including `b` itself, up to the
/// CFG's entry. Each link is `forward_cfg.find_immediate_dominator`.
/// Stops on the root (self-dominator) or after `MAX_CHAIN` steps.
fn forward_dom_chain(b: BlockId, forward_cfg: &StacklessControlFlowGraph) -> Vec<BlockId> {
    const MAX_CHAIN: usize = 1024;
    let mut chain = vec![b];
    let mut cursor = b;
    for _ in 0..MAX_CHAIN {
        let d = match forward_cfg.find_immediate_dominator(cursor) {
            Some(d) => d,
            None => break,
        };
        if d == cursor {
            break;
        }
        chain.push(d);
        cursor = d;
    }
    chain
}

/// Deepest forward-dominator common to every block in `blocks` (i.e.
/// the meet in the dominator tree). Returns `None` if `blocks` is
/// empty or no common dominator exists.
fn common_forward_dominator(
    blocks: &[BlockId],
    forward_cfg: &StacklessControlFlowGraph,
) -> Option<BlockId> {
    let mut iter = blocks.iter().copied();
    let first = iter.next()?;
    let mut acc: BTreeSet<BlockId> = forward_dom_chain(first, forward_cfg).into_iter().collect();
    let last_first_chain: Vec<BlockId> = forward_dom_chain(first, forward_cfg);
    for b in iter {
        let b_set: BTreeSet<BlockId> = forward_dom_chain(b, forward_cfg).into_iter().collect();
        acc = acc.intersection(&b_set).copied().collect();
        if acc.is_empty() {
            return None;
        }
    }
    // Among the common ancestors, pick the deepest one (closest to
    // the original blocks in the dominator tree). Equivalently, the
    // first entry of `first`'s chain that's still in `acc`.
    last_first_chain.into_iter().find(|d| acc.contains(d))
}

/// Find the labeled-block exit reachable from `bt` (a break-target
/// outside the innermost loop body) via Jump-only chains, where the
/// exit is also reachable from `exit_succ` via fall-through chain.
/// Returns `Some(exit_block)` if a shared meeting point exists that
/// is NOT `exit_succ` itself. Mirrors the original `emit_while`
/// label-detection heuristic that was load-bearing for the 313/326
/// ember-vaults state.
fn find_label_exit_via_merge(
    bt: BlockId,
    exit_succ: BlockId,
    code: &[Bytecode],
    forward_cfg: &StacklessControlFlowGraph,
) -> Option<BlockId> {
    let exit_chain = fall_through_chain(exit_succ, forward_cfg);
    let exit_set: BTreeSet<BlockId> = exit_chain.iter().copied().collect();
    let bt_chain = jump_only_chain(bt, code, forward_cfg);
    bt_chain
        .iter()
        .find(|b| **b != exit_succ && exit_set.contains(b))
        .copied()
}

/// Jump-only forward chain starting at `start`. Each step requires the
/// cursor's terminator to be a `Jump`; disallows Branch/Ret/Abort/etc.
/// Mirrors `structurer::jump_only_chain`.
fn jump_only_chain(
    start: BlockId,
    code: &[Bytecode],
    forward_cfg: &StacklessControlFlowGraph,
) -> Vec<BlockId> {
    const MAX_CHAIN: usize = 64;
    let mut chain = vec![start];
    let mut current = start;
    for _ in 0..MAX_CHAIN {
        if matches!(forward_cfg.content(current), BlockContent::Dummy) {
            break;
        }
        let upper_pc = match forward_cfg.content(current) {
            BlockContent::Basic { upper, .. } => *upper,
            BlockContent::Dummy => break,
        };
        if !matches!(&code[upper_pc as usize], Bytecode::Jump(..)) {
            break;
        }
        let succs = forward_cfg.successors(current);
        let [next] = succs.as_slice() else {
            break;
        };
        if matches!(forward_cfg.content(*next), BlockContent::Dummy) {
            break;
        }
        chain.push(*next);
        current = *next;
    }
    chain
}

/// Single-successor fall-through chain starting at `start`. Stops at
/// multi-successor blocks, dummies, or after `MAX_CHAIN` steps.
/// Mirrors `structurer::fall_through_chain`.
fn fall_through_chain(start: BlockId, forward_cfg: &StacklessControlFlowGraph) -> Vec<BlockId> {
    const MAX_CHAIN: usize = 64;
    let mut chain = vec![start];
    let mut current = start;
    for _ in 0..MAX_CHAIN {
        let succs = forward_cfg.successors(current);
        if succs.len() != 1 {
            break;
        }
        let next = succs[0];
        if matches!(forward_cfg.content(next), BlockContent::Dummy) {
            break;
        }
        chain.push(next);
        current = next;
    }
    chain
}

/// Mirror of `structurer::find_loop_decision` — finds the loop's
/// natural exit_succ block (where control flows when the loop's
/// deciding Branch's exit-arm is taken).
fn find_exit_succ(
    loop_header: BlockId,
    loop_body: &BTreeSet<BlockId>,
    code: &[Bytecode],
    forward_cfg: &StacklessControlFlowGraph,
    backward_cfg: &StacklessControlFlowGraph,
) -> Option<BlockId> {
    let mut current = loop_header;
    const MAX_STEPS: usize = 1024;
    for _ in 0..MAX_STEPS {
        if loop_body.contains(&current) {
            if let Some((then_b, else_b)) = branch_arms_at(current, code, forward_cfg) {
                let in_then = loop_body.contains(&then_b);
                let in_else = loop_body.contains(&else_b);
                if in_then ^ in_else {
                    return Some(if in_then { else_b } else { then_b });
                }
            }
        }
        match backward_cfg.find_immediate_dominator(current) {
            Some(next) if next != current && loop_body.contains(&next) => current = next,
            _ => return None,
        }
    }
    None
}

fn branch_arms_at(
    block: BlockId,
    code: &[Bytecode],
    forward_cfg: &StacklessControlFlowGraph,
) -> Option<(BlockId, BlockId)> {
    let upper = match forward_cfg.content(block) {
        BlockContent::Basic { upper, .. } => *upper,
        BlockContent::Dummy => return None,
    };
    if let Bytecode::Branch(_, then_label, else_label, _) = &code[upper as usize] {
        let label_offsets =
            move_stackless_bytecode::stackless_bytecode::Bytecode::label_offsets(code);
        let then_pc = label_offsets.get(then_label).copied()?;
        let else_pc = label_offsets.get(else_label).copied()?;
        let then_b = forward_cfg.pc_to_block(then_pc)?;
        let else_b = forward_cfg.pc_to_block(else_pc)?;
        Some((then_b, else_b))
    } else {
        None
    }
}
