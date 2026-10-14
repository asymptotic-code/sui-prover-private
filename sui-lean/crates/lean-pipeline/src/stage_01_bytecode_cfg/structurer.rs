//! Recursive-descent structurer. See
//! `plans/lean-pipeline/stage-01-bytecode-cfg.md` for the design.

use std::collections::{BTreeMap, BTreeSet};

use move_binary_format::file_format::CodeOffset;
use move_stackless_bytecode::graph::NaturalLoop;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Label};
use move_stackless_bytecode::stackless_control_flow_graph::{
    BlockContent, BlockId, StacklessControlFlowGraph,
};

use super::loops::{find_natural_loops, translate_loops, LoopIndex};
use super::{BytecodeCfg, Region, Stage1Error, Termination};

/// Cap on `structure` recursion depth. Real human-written Move bodies
/// nest tens, not thousands, of `if` / `while` / `switch`. Hitting
/// this cap means the structurer is recursing without bound (e.g. a
/// post-dom cycle on malformed bytecode), which would otherwise blow
/// the host stack with no recovery -- the process aborts on stack
/// overflow before any panic / error path can run. Returning
/// `Stage1Error::RecursionLimit` instead lets the per-function driver
/// skip the function in permissive mode and continue with the rest of
/// the package. See `momentum-clmm` test-mode IR build for an example
/// trigger.
const MAX_RECURSION_DEPTH: u32 = 2048;

/// Debug helper: pretty-print the label_analysis output for one
/// function. Gated by `FOXY_DEBUG_LABEL_ANALYSIS` env var; called from
/// `mod.rs::run` before structuring.
pub fn debug_dump_label_analysis(code: &[Bytecode], qualified_name: &str) {
    use std::collections::BTreeSet;
    let forward_cfg = StacklessControlFlowGraph::new_forward_with_options(code, true);
    let backward_cfg = StacklessControlFlowGraph::new_backward_with_options(code, false, true);
    let loop_detection_cfg = StacklessControlFlowGraph::new_forward_with_options(code, false);
    let natural_loops_raw = match find_natural_loops(&loop_detection_cfg) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("[label_analysis][{qualified_name}] natural-loop detection failed: {e:?}");
            return;
        }
    };
    let natural_loops = translate_loops(natural_loops_raw, &loop_detection_cfg, &forward_cfg);
    let label_map =
        super::label_analysis::analyze(code, &forward_cfg, &backward_cfg, &natural_loops);

    eprintln!("===== label_analysis for {qualified_name} =====");
    eprintln!("bytecode:");
    for (pc, bytecode) in code.iter().enumerate() {
        eprintln!("  pc{pc}: {bytecode:?}");
    }
    eprintln!("blocks: {}", forward_cfg.blocks().len());
    eprintln!("natural loops:");
    for l in &natural_loops {
        let body: BTreeSet<BlockId> = l.loop_body.iter().copied().collect();
        eprintln!("  header B{}  body={:?}", l.loop_header, body);
    }
    eprintln!("scopes_by_exit ({}):", label_map.scopes_by_exit.len());
    for (exit, scope) in &label_map.scopes_by_exit {
        eprintln!("  exit B{exit}  members={:?}", scope.members);
    }
    eprintln!("block_label_stack (non-empty only):");
    for (b, stack) in &label_map.block_label_stack {
        if !stack.is_empty() {
            eprintln!("  B{b} -> innermost-first {stack:?}");
        }
    }
    eprintln!("edge_kinds ({}):", label_map.edge_kinds.len());
    for ((s, t), kind) in &label_map.edge_kinds {
        eprintln!("  B{s} -> B{t} : {kind:?}");
    }
    eprintln!("block PCs:");
    for b in forward_cfg.blocks() {
        match forward_cfg.content(b) {
            move_stackless_bytecode::stackless_control_flow_graph::BlockContent::Basic {
                lower,
                upper,
            } => {
                let tail = &code[*upper as usize];
                let succs: Vec<BlockId> = forward_cfg.successors(b).iter().copied().collect();
                eprintln!("  B{b} pc=[{lower}..={upper}] tail={tail:?} succs={succs:?}");
            }
            move_stackless_bytecode::stackless_control_flow_graph::BlockContent::Dummy => {
                eprintln!("  B{b} (Dummy)");
            }
        }
    }
    eprintln!("===== end label_analysis =====");
}

/// Internal entry: bytecode only. The public `run` delegates here
/// after dropping `FunctionTarget`; tests call this directly.
pub fn run_from_code(code: &[Bytecode]) -> Result<BytecodeCfg, Stage1Error> {
    // Return-only loops (`loop { ... return ... }` -- every escape is a
    // Ret/Abort, e.g. `cetus_dlmm::bin::prev_score_in_group`) are handled
    // natively by the `ignore_return_abort=true` mode: such a loop has no
    // post-dominator (returns are fall-throughs in that mode, the
    // back-edge only cycles), so `collect_blocks` gives the loop the
    // mode's standard early-return treatment -- the EXITING latch falls
    // through to the block after the loop, or anchors `DUMMY_EXIT` when
    // the back-edge is the function's final instruction (the Move
    // compiler drops the unreachable trailing expression, so that shape
    // is common). The latch block consequently has TWO forward
    // successors (header + fall-through/exit) -- the Jump dispatch below
    // resolves the walk target from the instruction, never from
    // successor count.

    // `ignore_return_abort=true`: mid-code Ret/Abort gets a synthetic
    // fall-through to `pc+1` (not to `DUMMY_EXIT`). The dispatch matches
    // on `Ret` / `Abort` before consulting successors, so the edge is
    // inert forward; in backward it makes the post-dom of an
    // early-return `if cond return; rest` be the start of `rest`, which
    // is what lets `rest` emerge as the outer continuation instead of
    // nesting into the else-arm. Natural-loop detection uses a separate
    // `=false` CFG to match upstream's `find_loops_headers` exactly --
    // the synthetic edges could in principle perturb back-edge
    // detection. Block IDs do NOT agree across the two CFGs when the
    // bytecode contains aborting Calls (Mod/Div/narrowing Cast/...): in
    // the `=false` CFG, an aborting Call ends a basic block (its
    // successors include `DUMMY_EXIT`), while in the `=true` CFG the
    // same Call doesn't terminate the block (the abort-edge is replaced
    // by the synthetic fall-through). `translate_loops` maps loop
    // BlockIds from the `=false` space into the `=true` space via PC
    // lookups; see `loops::translate_loops` for details.
    let forward_cfg = StacklessControlFlowGraph::new_forward_with_options(code, true);
    let backward_cfg = StacklessControlFlowGraph::new_backward_with_options(code, false, true);
    let loop_detection_cfg = StacklessControlFlowGraph::new_forward_with_options(code, false);
    let label_offsets = Bytecode::label_offsets(code);
    // Detect natural loops on the `ignore_return_abort=false` CFG, then
    // translate their BlockIds into the forward CFG's space. The two CFGs
    // partition basic blocks differently when aborting Calls are present
    // (see `translate_loops` doc) -- without translation `header_at` would
    // miss every loop containing an aborting Call (Mod, Div, narrowing
    // Cast, ...), and the structurer would recurse through the back-edge
    // as if it were a plain Branch -> stack overflow.
    let natural_loops_raw = find_natural_loops(&loop_detection_cfg)?;
    let natural_loops = translate_loops(natural_loops_raw, &loop_detection_cfg, &forward_cfg);

    // Pre-pass: classify every Jump-edge and identify labeled-block
    // scopes via post-dom analysis. The structurer queries this side
    // table instead of computing detection inline.
    let label_map =
        super::label_analysis::analyze(code, &forward_cfg, &backward_cfg, &natural_loops);

    let loop_index = LoopIndex::build(natural_loops);

    let ctx = Ctx {
        code,
        forward_cfg,
        backward_cfg,
        label_offsets,
        loop_index,
        label_map,
    };
    let entry = ctx.forward_cfg.entry_block();
    let root = structure(entry, None, &Vec::new(), &Vec::new(), false, &ctx, 0)?;
    Ok(BytecodeCfg { root })
}

struct Ctx<'a> {
    code: &'a [Bytecode],
    forward_cfg: StacklessControlFlowGraph,
    backward_cfg: StacklessControlFlowGraph,
    label_offsets: BTreeMap<Label, CodeOffset>,
    loop_index: LoopIndex,
    /// Pre-pass classification of every Jump-edge in the function and
    /// the labeled-block scopes derived from it.
    label_map: super::label_analysis::LabelMap,
}

impl Ctx<'_> {
    fn block_lower(&self, block: BlockId) -> CodeOffset {
        match self.forward_cfg.content(block) {
            BlockContent::Basic { lower, .. } => *lower,
            BlockContent::Dummy => panic!("block_lower called on Dummy block {block}"),
        }
    }

    fn block_upper(&self, block: BlockId) -> CodeOffset {
        match self.forward_cfg.content(block) {
            BlockContent::Basic { upper, .. } => *upper,
            BlockContent::Dummy => panic!("block_upper called on Dummy block {block}"),
        }
    }

    fn block_at_label(&self, label: Label) -> BlockId {
        let pc = self
            .label_offsets
            .get(&label)
            .copied()
            .unwrap_or_else(|| panic!("label {label:?} has no offset"));
        self.forward_cfg
            .pc_to_block(pc)
            .unwrap_or_else(|| panic!("no block at pc {pc} for label {label:?}"))
    }

    fn is_dummy(&self, block: BlockId) -> bool {
        matches!(self.forward_cfg.content(block), BlockContent::Dummy)
    }

    /// `(then_block, else_block)` if `block` ends in a `Branch`; else `None`.
    fn branch_arms_at(&self, block: BlockId) -> Option<(BlockId, BlockId)> {
        let upper = self.block_upper(block);
        let Bytecode::Branch(_, then_label, else_label, _) = &self.code[upper as usize] else {
            return None;
        };
        Some((
            self.block_at_label(*then_label),
            self.block_at_label(*else_label),
        ))
    }

    /// Basic covering the whole block; `None` for Dummy.
    fn basic_including_terminator(&self, block: BlockId) -> Option<Region> {
        match self.forward_cfg.content(block) {
            BlockContent::Basic { lower, upper } => Some(Region::Basic {
                lower: *lower,
                upper: *upper,
            }),
            BlockContent::Dummy => None,
        }
    }

    /// Basic with the terminator opcode omitted. `None` if the block
    /// is dummy or has no body before the terminator (`lower == upper`).
    fn basic_excluding_terminator(&self, block: BlockId) -> Option<Region> {
        match self.forward_cfg.content(block) {
            BlockContent::Basic { lower, upper } if *upper > *lower => Some(Region::Basic {
                lower: *lower,
                upper: *upper - 1,
            }),
            _ => None,
        }
    }

    fn basic_before(&self, block: BlockId, upper: CodeOffset) -> Option<Region> {
        match self.forward_cfg.content(block) {
            BlockContent::Basic { lower, .. } if upper > *lower => Some(Region::Basic {
                lower: *lower,
                upper: upper - 1,
            }),
            _ => None,
        }
    }

    /// Recover the real terminator of a block whose `Jump` sits INTERIOR to it.
    ///
    /// Upstream splits basic blocks only at `Bytecode::branch_dests` targets
    /// (`StacklessControlFlowGraph::record_block_ids`), so a `Jump` that is not
    /// immediately followed by a referenced `Label` stays inside its block and
    /// the CFG reports the block's last instruction as the tail. Debug and
    /// mutable-reference instrumentation both produce that shape: an orphaned
    /// label plus its trace / `WriteBack` / `Destroy` epilogue emitted after a
    /// jump that already left the block.
    ///
    /// Everything after such a `Jump` is unreachable BY CONSTRUCTION. A pc is
    /// entered only by falling through from `pc - 1` or as a `branch_dests`
    /// target (`AbortAction` carries no label -- it is a bare `Check`), the
    /// `Jump` makes fall-through impossible, and a `branch_dests` target would
    /// have ended the block at the preceding pc. So the suffix is dead code and
    /// the `Jump` is the block's true terminator, whatever the dead
    /// instructions happen to be. The `Label` guard below states that argument
    /// as a fail-closed check rather than trusting it: a suffix label that IS
    /// somebody's branch target would mean the suffix is live, and we decline
    /// instead of dropping reachable code.
    fn interior_jump_before_unreachable_suffix(
        &self,
        block: BlockId,
    ) -> Option<(CodeOffset, BlockId)> {
        let BlockContent::Basic { lower, upper } = self.forward_cfg.content(block) else {
            return None;
        };
        let [cfg_successor] = self.forward_cfg.successors(block).as_slice() else {
            return None;
        };
        for pc in *lower..*upper {
            let Bytecode::Jump(_, target_label) = &self.code[pc as usize] else {
                continue;
            };
            let target = self.block_at_label(*target_label);
            if target != *cfg_successor {
                continue;
            }
            let suffix = &self.code[(pc as usize + 1)..=(*upper as usize)];
            if suffix.iter().all(|op| match op {
                Bytecode::Label(_, label) => !self
                    .code
                    .iter()
                    .flat_map(Bytecode::branch_dests)
                    .any(|target| target == *label),
                _ => true,
            }) {
                return Some((pc, target));
            }
        }
        None
    }

    /// Basic for a fall-through block; `Jump` terminator excluded
    /// (sequencing is expressed by the surrounding `Seq`).
    fn basic_for_fall_through(&self, block: BlockId) -> Option<Region> {
        let upper = match self.forward_cfg.content(block) {
            BlockContent::Basic { upper, .. } => *upper,
            BlockContent::Dummy => return None,
        };
        if matches!(&self.code[upper as usize], Bytecode::Jump(..)) {
            self.basic_excluding_terminator(block)
        } else {
            self.basic_including_terminator(block)
        }
    }
}

/// Wrap a list of regions: empty -> `Seq(vec![])`, singleton -> the
/// element itself, multi -> `Seq(blocks)`.
fn seq_or_single(mut blocks: Vec<Region>) -> Region {
    match blocks.len() {
        0 => Region::Seq(Vec::new()),
        1 => blocks.pop().unwrap(),
        _ => Region::Seq(blocks),
    }
}

/// Append `extra` to `head`, flattening nested `Seq`s.
fn combine_seq(head: Region, extra: Region) -> Region {
    if matches!(&extra, Region::Seq(v) if v.is_empty()) {
        return head;
    }
    if matches!(&head, Region::Seq(v) if v.is_empty()) {
        return extra;
    }
    let mut out = match head {
        Region::Seq(v) => v,
        other => vec![other],
    };
    match extra {
        Region::Seq(v) => out.extend(v),
        other => out.push(other),
    }
    seq_or_single(out)
}

/// True if `pd` is outside the innermost enclosing loop's body. When
/// this fires for an `If` / `Switch` post-dominator both arms must have
/// already terminated; iterating onto `pd` would emit a spurious break.
fn pd_outside_innermost_loop(loop_stack: &[&NaturalLoop<BlockId>], pd: BlockId) -> bool {
    match loop_stack.last() {
        Some(innermost) => !innermost.loop_body.contains(&pd),
        None => false,
    }
}

/// `Some(level)` if `target` is the header of the `level`-th enclosing
/// loop (innermost = 0); else `None`.
fn is_continue(loop_stack: &[&NaturalLoop<BlockId>], target: BlockId) -> Option<u32> {
    loop_stack
        .iter()
        .rev()
        .position(|l| l.loop_header == target)
        .map(|i| i as u32)
}

/// `Some(level)` if `target` is outside the `level`-th enclosing loop
/// (innermost out); `None` if it stays inside the innermost loop's body.
fn is_break(loop_stack: &[&NaturalLoop<BlockId>], target: BlockId) -> Option<u32> {
    let count = loop_stack
        .iter()
        .rev()
        .take_while(|l| !l.loop_body.contains(&target))
        .count() as u32;
    (count > 0).then(|| count - 1)
}

/// `Some(level)` if `target` matches the `level`-th enclosing labeled
/// block's exit (innermost = 0). `None` if no enclosing labeled block
/// names `target` as its exit.
fn is_return_from_block(label_stack: &[BlockId], target: BlockId) -> Option<u32> {
    label_stack
        .iter()
        .rev()
        .position(|&exit| exit == target)
        .map(|i| i as u32)
}

/// Like `fall_through_chain` but stricter: each step requires the
/// cursor's terminator to be a `Jump` (cleanly excludable from emitted
/// Basic). Disallows Branch, Ret, Abort, VariantSwitch, and
/// non-control-flow terminators (block-ends-because-next-is-labeled
/// blocks — those produced too many misfires when relaxed).
fn jump_only_chain(start: BlockId, ctx: &Ctx) -> Vec<BlockId> {
    const MAX_CHAIN: usize = 64;
    let mut chain = vec![start];
    let mut current = start;
    for _ in 0..MAX_CHAIN {
        if ctx.is_dummy(current) {
            break;
        }
        let upper_pc = ctx.block_upper(current);
        if !matches!(&ctx.code[upper_pc as usize], Bytecode::Jump(..)) {
            break;
        }
        let succs = ctx.forward_cfg.successors(current);
        let [next] = succs.as_slice() else {
            break;
        };
        if ctx.is_dummy(*next) {
            break;
        }
        chain.push(*next);
        current = *next;
    }
    chain
}

/// Follow single-successor fall-through chain starting at `start`.
/// Stops at multi-successor blocks, multi-predecessor blocks
/// (merge points), dummies, or after `MAX_CHAIN` steps.
fn fall_through_chain(start: BlockId, ctx: &Ctx) -> Vec<BlockId> {
    const MAX_CHAIN: usize = 64;
    let mut chain = vec![start];
    let mut current = start;
    for _ in 0..MAX_CHAIN {
        let succs = ctx.forward_cfg.successors(current);
        if succs.len() != 1 {
            break;
        }
        let next = succs[0];
        if ctx.is_dummy(next) {
            break;
        }
        chain.push(next);
        current = next;
    }
    chain
}

/// Collect block IDs that are direct Jump/Branch targets from inside
/// `loop_body` AND lie outside the body, excluding `exit_succ` (the
/// loop's natural fallthrough). These are candidate labeled-return
/// targets.
fn collect_break_targets(
    loop_body: &BTreeSet<BlockId>,
    exit_succ: BlockId,
    ctx: &Ctx,
) -> BTreeSet<BlockId> {
    let mut targets = BTreeSet::new();
    for &block in loop_body {
        for &succ in ctx.forward_cfg.successors(block).iter() {
            if !loop_body.contains(&succ) && !ctx.is_dummy(succ) && succ != exit_succ {
                targets.insert(succ);
            }
        }
    }
    targets
}

/// Recursively structure the CFG from `start` until `stop` is reached.
///
/// `body_of_while=true` for the body and header recursions of
/// `emit_while` (whose `stop` is structural -- `loop_header` /
/// `cond_at`). It suppresses natural-tail-injection at the recursion
/// exit; stage 2 fills the implicit continue from the surrounding-While
/// context. Every other recursion injects an explicit
/// `Term(Continue { level })` when the loop guard terminates at a `stop`
/// that's an enclosing loop's header.
fn structure(
    start: BlockId,
    stop: Option<BlockId>,
    loop_stack: &[&NaturalLoop<BlockId>],
    label_stack: &[BlockId],
    body_of_while: bool,
    ctx: &Ctx,
    depth: u32,
) -> Result<Region, Stage1Error> {
    if depth > MAX_RECURSION_DEPTH {
        return Err(Stage1Error::RecursionLimit { depth });
    }
    let mut blocks: Vec<Region> = Vec::new();
    let mut current = start;

    while Some(current) != stop {
        // Dummy entrance / exit: thread through.
        if ctx.is_dummy(current) {
            let succs = ctx.forward_cfg.successors(current);
            match succs.as_slice() {
                [next] => {
                    current = *next;
                    continue;
                }
                [] => break,
                _ => return Err(Stage1Error::UnsupportedGoto { at: 0 }),
            }
        }

        // Labeled-block entry: if `current`'s required label stack
        // (from the pre-pass post-dom analysis) has more entries than
        // our current `label_stack`, we are entering a new labeled
        // scope. Push the next outermost label onto the stack and
        // recurse with `stop = that label's exit`. When the recursion
        // returns, wrap its result in `Region::LabeledBlock` and
        // continue from the scope's exit.
        //
        // Labels are orthogonal to loops: the wrap happens around the
        // natural shape of the body (whatever the inner recursion
        // produced -- loops, ifs, sequences). emit_while does not
        // need to know about labels.
        {
            let labels_innermost_first: Vec<BlockId> = ctx
                .label_map
                .block_label_stack
                .get(&current)
                .cloned()
                .unwrap_or_default();
            // Convert to outermost-first to match our push order.
            let labels_outermost_first: Vec<BlockId> =
                labels_innermost_first.iter().rev().copied().collect();
            if labels_outermost_first.len() > label_stack.len() {
                // The next label to push is the one immediately after
                // our current stack's depth.
                let next_label_exit = labels_outermost_first[label_stack.len()];
                let mut new_label_stack: Vec<BlockId> = label_stack.to_vec();
                new_label_stack.push(next_label_exit);
                let body = structure(
                    current,
                    Some(next_label_exit),
                    loop_stack,
                    &new_label_stack,
                    false,
                    ctx,
                    depth + 1,
                )?;
                blocks.push(Region::LabeledBlock {
                    body: Box::new(body),
                });
                current = next_label_exit;
                continue;
            }
        }

        // Loop-header detection.
        if let Some(loop_) = ctx.loop_index.header_at(current) {
            let already_in = loop_stack.iter().any(|l| std::ptr::eq(*l, loop_));
            if !already_in {
                let (region, exit_succ) =
                    emit_while(current, loop_, loop_stack, label_stack, ctx, depth + 1)?;
                blocks.push(region);
                current = exit_succ;
                continue;
            }
        }

        // First-iteration skip: in `emit_while`'s header / body
        // recursion, the new loop is on the stack so without this guard
        // `is_continue` would fire `Some(0)` on iteration 1 and emit a
        // spurious `Term(Continue)` before the header is built (header
        // rec) or the body's first basic is structured (body rec where
        // body_succ happens to coincide with the header in a degenerate
        // self-loop). Gated on `body_of_while`: a non-`body_of_while`
        // recursion entering at a loop header is necessarily a continue
        // edge from a Branch arm (the only way to land on the header
        // mid-structuring) and MUST emit `Term(Continue)`, not be
        // suppressed -- without the gate, the structurer recurses
        // through the back-edge as if it were a plain Branch (post-dom
        // cycle: header -> ... -> latch -> header again), which is what
        // `MAX_RECURSION_DEPTH` was originally added to catch.
        let skip_loop_checks =
            body_of_while && current == start && is_continue(loop_stack, current).is_some();

        if !skip_loop_checks {
            // Jump-only bridge to a continue target: step through so the
            // next iteration's `is_continue` sees the header directly,
            // instead of `is_break` firing on the bridge block first.
            let upper_pc = ctx.block_upper(current);
            if matches!(&ctx.code[upper_pc as usize], Bytecode::Jump(..)) {
                if let [next] = *ctx.forward_cfg.successors(current).as_slice() {
                    if is_continue(loop_stack, next).is_some() {
                        blocks.extend(ctx.basic_for_fall_through(current));
                        current = next;
                        continue;
                    }
                }
            }

            // Continue: innermost-level-0 at body tail is suppressed
            // by the loop guard (it terminates the recursion before we
            // reach this check); everywhere else it's emitted.
            if let Some(level) = is_continue(loop_stack, current) {
                blocks.push(Region::Term(Termination::Continue { level }));
                break;
            }

            // Note: `is_break` is intentionally NOT checked at
            // top-of-iter. A block outside the innermost loop body can
            // still carry meaningful logic (e.g. a multi-stage break
            // landing pad whose Branch dispatches to different break
            // sites, or a single-stage break pad whose Basic content is
            // the break's side effects). Emitting `Term(Break)` here
            // would swallow the block's terminator and pre-terminator
            // content. Instead, descend normally; the leaf single-
            // successor dispatch below emits `Term(Break)` when the
            // fall-through target is outside the loop body. See
            // `rand_level` in `move_stl::skip_list_u128` for the wild
            // multi-stage-break case.
        }

        // Dispatch on terminator.
        let cfg_upper = ctx.block_upper(current);
        let interior_jump = ctx.interior_jump_before_unreachable_suffix(current);
        let upper = interior_jump.map_or(cfg_upper, |(pc, _)| pc);
        let succs = ctx.forward_cfg.successors(current);
        match (&ctx.code[upper as usize], succs.as_slice()) {
            (Bytecode::Ret(_, temps), _) => {
                blocks.extend(ctx.basic_excluding_terminator(current));
                blocks.push(Region::Term(Termination::Return {
                    temps: temps.clone(),
                }));
                break;
            }
            (Bytecode::Abort(_, code_temp), _) => {
                blocks.extend(ctx.basic_excluding_terminator(current));
                blocks.push(Region::Term(Termination::Abort {
                    code_temp: Some(*code_temp),
                }));
                break;
            }
            (Bytecode::VariantSwitch(_, _, labels), _) => {
                blocks.extend(ctx.basic_excluding_terminator(current));
                let pd = ctx
                    .backward_cfg
                    .find_immediate_dominator(current)
                    .ok_or(Stage1Error::UnsupportedGoto { at: upper })?;
                let branches: Result<Vec<Region>, _> = labels
                    .iter()
                    .map(|l| {
                        structure(
                            ctx.block_at_label(*l),
                            Some(pd),
                            loop_stack,
                            label_stack,
                            false,
                            ctx,
                            depth + 1,
                        )
                    })
                    .collect();
                blocks.push(Region::Switch {
                    switch_at: upper,
                    branches: branches?,
                });
                if pd_outside_innermost_loop(loop_stack, pd) {
                    break;
                }
                current = pd;
            }
            (Bytecode::Branch(_, then_label, else_label, _), _) => {
                let then_b = ctx.block_at_label(*then_label);
                let else_b = ctx.block_at_label(*else_label);
                if then_b == else_b {
                    // Degenerate `if (cond) {}` with both arms identical.
                    blocks.extend(ctx.basic_excluding_terminator(current));
                    current = then_b;
                    continue;
                }
                blocks.extend(ctx.basic_excluding_terminator(current));
                let pd = ctx
                    .backward_cfg
                    .find_immediate_dominator(current)
                    .ok_or(Stage1Error::UnsupportedGoto { at: upper })?;
                let then_arm = structure(
                    then_b,
                    Some(pd),
                    loop_stack,
                    label_stack,
                    false,
                    ctx,
                    depth + 1,
                )?;
                let else_arm = structure(
                    else_b,
                    Some(pd),
                    loop_stack,
                    label_stack,
                    false,
                    ctx,
                    depth + 1,
                )?;
                blocks.push(Region::If {
                    cond_at: upper,
                    then_branch: Box::new(then_arm),
                    else_branch: Box::new(else_arm),
                });
                if pd_outside_innermost_loop(loop_stack, pd) {
                    break;
                }
                current = pd;
            }
            (term, succs_slice) if matches!(term, Bytecode::Jump(..)) || succs_slice.len() == 1 => {
                // A Jump's target is authoritative from the instruction
                // itself: a function-final back-edge block carries a
                // second, synthetic `DUMMY_EXIT` successor (the
                // `ignore_return_abort=true` CFG anchors the exit at the
                // last pc), so successor count alone can't drive the walk
                // for Jump-terminated blocks.
                let next_block = match term {
                    Bytecode::Jump(_, label) => ctx.block_at_label(*label),
                    _ => succs_slice[0],
                };
                blocks.extend(match interior_jump {
                    Some((jump_pc, _)) => ctx.basic_before(current, jump_pc),
                    None => ctx.basic_for_fall_through(current),
                });
                // ReturnFromBlock: use pre-pass edge classification.
                // This catches direct Jump-to-exit AND trampoline-via-
                // scope-member cases that the simple label_stack lookup
                // would miss.
                if let Some(super::label_analysis::EdgeKind::ReturnFromBlock { label_level }) =
                    ctx.label_map.edge_kinds.get(&(current, next_block))
                {
                    blocks.push(Region::Term(Termination::ReturnFromBlock {
                        level: *label_level,
                        temps: Vec::new(),
                    }));
                    break;
                }
                // Legacy fallback for any case the edge map missed
                // (defensive — should not fire once analysis is solid).
                if let Some(level) = is_return_from_block(label_stack, next_block) {
                    blocks.push(Region::Term(Termination::ReturnFromBlock {
                        level,
                        temps: Vec::new(),
                    }));
                    break;
                }
                // If the fall-through target is outside the innermost
                // loop body, emit `Term(Break)` here. Deferred until the
                // leaf so any pre-Jump Basic content (assignments, side
                // effects) is preserved before the break fires.
                if let Some(level) = is_break(loop_stack, next_block) {
                    blocks.push(Region::Term(Termination::Break { level }));
                    break;
                }
                current = next_block;
            }
            (_, []) => break,
            (_, _) => {
                return Err(Stage1Error::UnsupportedGoto { at: upper });
            }
        }
    }

    // Natural-tail injection: if we exited via the loop guard at a
    // `stop` that's an enclosing loop's header, that's a `continue` of
    // that loop. Skip when `body_of_while` (stage 2 fills it in) or when
    // the last region is already a `Term` (we exited via `break`).
    if !body_of_while && !matches!(blocks.last(), Some(Region::Term(_))) {
        if let Some(stop_id) = stop {
            if let Some(level) = is_continue(loop_stack, stop_id) {
                blocks.push(Region::Term(Termination::Continue { level }));
            }
        }
    }

    Ok(seq_or_single(blocks))
}

/// Emit `Region::While` for a loop whose header is `loop_header`. Returns
/// the While region plus the BlockId where control continues after the
/// loop exits.
///
/// Labels are orthogonal to loops -- emit_while neither detects nor
/// pushes labeled-block scopes. The outer `structure()` recursion
/// already pushed any enclosing label_exit onto `label_stack` before
/// arriving at this loop_header, so the body / header recursions just
/// thread `label_stack` through unchanged. Jumps to labeled-block
/// exits inside the body get classified as ReturnFromBlock via the
/// pre-pass edge map (see `structure`'s leaf dispatch).
fn emit_while<'a>(
    loop_header: BlockId,
    loop_: &'a NaturalLoop<BlockId>,
    loop_stack: &[&'a NaturalLoop<BlockId>],
    label_stack: &[BlockId],
    ctx: &'a Ctx,
    depth: u32,
) -> Result<(Region, BlockId), Stage1Error> {
    let (cond_at, body_succ, exit_succ, cond_continues) =
        find_loop_decision(loop_header, &loop_.loop_body, ctx)?;

    let mut new_stack: Vec<&NaturalLoop<BlockId>> = loop_stack.to_vec();
    new_stack.push(loop_);

    // Header: structure from loop_header to cond_at, then append the
    // cond_at block's pre-Branch Basic. New loop is on the stack so the
    // re-entry guard in `structure` bails; first-iteration skip prevents
    // a spurious continue at start.
    let header_pre = structure(
        loop_header,
        Some(cond_at),
        &new_stack,
        label_stack,
        true,
        ctx,
        depth + 1,
    )?;
    let header = match ctx.basic_excluding_terminator(cond_at) {
        Some(basic) => combine_seq(header_pre, basic),
        None => header_pre,
    };

    // Body: stop at loop_header. The back-edge becomes the implicit
    // innermost continue, filled in by stage 2.
    let body = structure(
        body_succ,
        Some(loop_header),
        &new_stack,
        label_stack,
        true,
        ctx,
        depth + 1,
    )?;

    Ok((
        Region::While {
            header: Box::new(header),
            cond_at: ctx.block_upper(cond_at),
            body: Box::new(body),
            negate_cond: !cond_continues,
        },
        exit_succ,
    ))
}

/// Find the deciding Branch of a natural loop and return
/// `(cond_at, body_succ, exit_succ)`. Walks the post-dom chain from
/// `loop_header` upward, returning the first in-body block whose tail
/// Branch has exactly one in-body and one out-of-body arm.
fn find_loop_decision(
    loop_header: BlockId,
    loop_body: &BTreeSet<BlockId>,
    ctx: &Ctx,
) -> Result<(BlockId, BlockId, BlockId, bool), Stage1Error> {
    let mut current = loop_header;
    loop {
        if loop_body.contains(&current) {
            if let Some((then_b, else_b)) = ctx.branch_arms_at(current) {
                let in_then = loop_body.contains(&then_b);
                let in_else = loop_body.contains(&else_b);
                if in_then ^ in_else {
                    let (body_succ, exit_succ) = if in_then {
                        (then_b, else_b)
                    } else {
                        (else_b, then_b)
                    };
                    // `in_then` = TRUE target is the loop body, so the
                    // branch cond IS the continue predicate (normal
                    // `while`). When false, TRUE -> exit
                    // (`loop { if C break }`); the continue predicate is
                    // `!cond` and stage 2 negates.
                    return Ok((current, body_succ, exit_succ, in_then));
                }
            }
        }
        match ctx.backward_cfg.find_immediate_dominator(current) {
            Some(next) if next != current && loop_body.contains(&next) => current = next,
            _ => {
                return Err(Stage1Error::UnsupportedLoop {
                    loop_header_pc: ctx.block_lower(loop_header),
                });
            }
        }
    }
}
