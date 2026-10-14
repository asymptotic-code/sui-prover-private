//! Loop detection for stage 1. See
//! `plans/lean-pipeline/stage-01-bytecode-cfg.md` "Algorithm" for how the
//! `LoopIndex` is consumed by the structurer.

use std::collections::{BTreeMap, BTreeSet};

use move_binary_format::file_format::CodeOffset;
use move_stackless_bytecode::graph::{Graph, NaturalLoop};
use move_stackless_bytecode::stackless_control_flow_graph::{
    BlockContent, BlockId, StacklessControlFlowGraph,
};

use super::Stage1Error;

/// Panic-free wrapper around `Graph::compute_reducible`. Returns
/// `IrreducibleCfg` instead of panicking on irreducible inputs.
pub fn find_natural_loops(
    cfg: &StacklessControlFlowGraph,
) -> Result<Vec<NaturalLoop<BlockId>>, Stage1Error> {
    let nodes = cfg.blocks();
    let edges: Vec<(BlockId, BlockId)> = nodes
        .iter()
        .flat_map(|b| cfg.successors(*b).iter().map(|s| (*b, *s)))
        .collect();
    Graph::new(cfg.entry_block(), nodes, edges)
        .compute_reducible()
        .ok_or(Stage1Error::IrreducibleCfg)
}

/// Translate loops detected in `src_cfg`'s BlockId space into `dst_cfg`'s
/// BlockId space via PC mapping.
///
/// The two CFGs (`new_forward_with_options` `ignore_return_abort=false`
/// for loop detection vs `=true` for structuring) have **different**
/// basic-block partitionings when the bytecode contains aborting Calls:
/// in the `=false` CFG, an aborting Call ends a basic block (its
/// successors include `DUMMY_EXIT`), while in the `=true` CFG the same
/// Call doesn't terminate the block (the abort-edge is replaced by a
/// synthetic fall-through). Same code, different BlockIds.
///
/// The structurer walks the forward CFG, so it queries `LoopIndex` with
/// forward-CFG BlockIds. Without this translation, `header_at(<forward
/// id>)` always misses (the index was keyed on loop-detection-CFG ids),
/// the loop goes unrecognized, and the structurer recurses through the
/// back-edge as if it were just another Branch -- stack overflow on any
/// loop that contains an aborting Call.
///
/// Translation: each `src` block maps to the `dst` block containing the
/// `src` block's `lower` PC. Multiple `src` body blocks may collapse to
/// the same `dst` body block (because `dst` blocks are larger when
/// aborting Calls no longer split them); set semantics dedupe.
pub fn translate_loops(
    loops: Vec<NaturalLoop<BlockId>>,
    src_cfg: &StacklessControlFlowGraph,
    dst_cfg: &StacklessControlFlowGraph,
) -> Vec<NaturalLoop<BlockId>> {
    let translate_block = |b: BlockId| -> Option<BlockId> {
        let lower: CodeOffset = match src_cfg.content(b) {
            BlockContent::Basic { lower, .. } => *lower,
            BlockContent::Dummy => return None,
        };
        dst_cfg.pc_to_block(lower)
    };
    let mut translated = Vec::with_capacity(loops.len());
    for l in loops {
        let Some(loop_header) = translate_block(l.loop_header) else {
            continue;
        };
        let Some(loop_latch) = translate_block(l.loop_latch) else {
            continue;
        };
        let loop_body: BTreeSet<BlockId> = l
            .loop_body
            .iter()
            .filter_map(|b| translate_block(*b))
            .collect();
        translated.push(NaturalLoop {
            loop_header,
            loop_latch,
            loop_body,
        });
    }
    translated
}

/// Per-`BlockId` index of natural loops. "Fat header" loops (multiple
/// back-edges to the same header) are merged into a single entry whose
/// `loop_body` is the UNION of the per-back-edge bodies. First-write-wins
/// is incorrect: a minimal-body back-edge registered first would hide the
/// blocks that only the descent path can reach, causing `is_break` to
/// misclassify mid-body merge labels as exits (and the structurer to
/// emit spurious `Term(Break)`). The latch field keeps the first
/// observed value since the structurer doesn't consume it directly --
/// only `header` and `loop_body` participate in continue/break
/// classification.
pub struct LoopIndex {
    headers: BTreeMap<BlockId, NaturalLoop<BlockId>>,
}

impl LoopIndex {
    pub fn build(loops: Vec<NaturalLoop<BlockId>>) -> Self {
        let mut headers: BTreeMap<BlockId, NaturalLoop<BlockId>> = BTreeMap::new();
        for l in loops {
            headers
                .entry(l.loop_header)
                .and_modify(|existing| {
                    existing.loop_body.extend(l.loop_body.iter().copied());
                })
                .or_insert(l);
        }
        Self { headers }
    }

    pub fn header_at(&self, block: BlockId) -> Option<&NaturalLoop<BlockId>> {
        self.headers.get(&block)
    }
}
