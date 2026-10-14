//! Stage-5 traversal context: scope, counter, loop stack.
//!
//! See `plans/lean-pipeline/stage-05-ssa.md` "Single recursive walk
//! with two threaded states" and "Naming convention".
//!
//! `Ctx` is threaded through every recursive call. Arm visits clone
//! `scope` so arm-local bindings don't leak; the `counter` is shared
//! per-function to keep fresh names unique. The `loop_stack` is pushed
//! on every `Expr::While` entry; cross-level `Break` / `Continue`
//! resolve through it.

use std::collections::BTreeMap;

use crate::ir::{FunId, Type, VarId};

use super::Stage5Error;

/// Per-function traversal state.
#[derive(Debug, Clone)]
pub struct Ctx {
    /// Current `FunId` -- threaded into errors.
    pub function: FunId,
    /// Source name (the name the IR carries pre-stage-5) -> current
    /// SSA name (`name_<counter>`) within the active scope. Cloned
    /// at every `If` / `Match` / `While` arm entry so arm-local
    /// bindings don't leak.
    pub scope: BTreeMap<VarId, VarId>,
    /// Per-base-name counter for fresh-name allocation. Shared
    /// across all scopes within a function so a name introduced in
    /// one arm doesn't collide with one in a sibling arm.
    pub counter: BTreeMap<VarId, u32>,
    /// Active loop nest. `loop_stack[len-1]` is innermost.
    pub loop_stack: Vec<LoopFrame>,
    /// Best-effort source-name -> Type map for this function (built
    /// pre-walk by `var_types::collect`). Used only by the
    /// `UninitFromZeroIterLoop` path to synthesize a typed `default`
    /// init for a loop-carried var with no pre-loop value.
    pub var_types: std::collections::BTreeMap<VarId, Type>,
    /// Abort companions retain conservative header loop-state discovery.
    /// Their generated continuation sum types are formed before stage 5 and
    /// rely on the full lowered header state remaining ABI-stable.
    pub conservative_header_state: bool,
}

/// One frame of the active loop nest. Each `LoopFrame` corresponds to
/// one in-progress `Expr::While`. Stage 5 pushes a frame on entry to
/// each `While::body` and pops it on exit.
#[derive(Debug, Clone)]
pub struct LoopFrame {
    /// Source-level vars whose values flow as a single tuple through
    /// every `Break { level: <this loop>, .. }`, every
    /// `Continue { level: <this loop>, .. }`, and the cond-false
    /// fall-through. Computed by the pre-pass before lifting body.
    /// Determinstic order (sorted by source name).
    pub loop_state: Vec<VarId>,
}

impl Ctx {
    /// New empty Ctx for `function`.
    pub fn new(function: FunId) -> Self {
        Ctx {
            function,
            scope: BTreeMap::new(),
            counter: BTreeMap::new(),
            loop_stack: Vec::new(),
            var_types: BTreeMap::new(),
            conservative_header_state: false,
        }
    }

    /// Allocate a fresh SSA name based on `base`. Advances the
    /// counter; returns `base_N` where `N` is the current count.
    pub fn fresh(&mut self, base: &VarId) -> VarId {
        let n = self.counter.entry(base.clone()).or_insert(0);
        let name: VarId = format!("{base}_{n}").into();
        *n += 1;
        name
    }

    /// Resolve `v` to its current SSA name.
    pub fn lookup(&self, v: &VarId) -> Result<VarId, Stage5Error> {
        self.scope
            .get(v)
            .cloned()
            .ok_or_else(|| Stage5Error::UnboundReference {
                function: self.function,
                var: v.clone(),
            })
    }

    /// Update `scope` so `source` maps to `fresh`. Used at every
    /// binder introduction (`Stmt::Let` pattern position,
    /// `MatchArm::bindings`, `Quantifier::binder`, function param).
    pub fn bind(&mut self, source: VarId, fresh: VarId) {
        self.scope.insert(source, fresh);
    }

    /// Push a `LoopFrame` onto the stack.
    pub fn push_loop(&mut self, frame: LoopFrame) {
        self.loop_stack.push(frame);
    }

    /// Pop the innermost loop frame.
    pub fn pop_loop(&mut self) -> Option<LoopFrame> {
        self.loop_stack.pop()
    }

    /// Lookup the `LoopFrame` `level` levels out from innermost.
    /// `level = 0` is innermost. Returns `None` if `level` exceeds
    /// the stack depth.
    pub fn loop_at(&self, level: u32) -> Option<&LoopFrame> {
        let len = self.loop_stack.len();
        let idx = (len as i64) - 1 - (level as i64);
        if idx < 0 {
            None
        } else {
            self.loop_stack.get(idx as usize)
        }
    }
}
