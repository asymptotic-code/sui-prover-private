//! New Lean-backend pipeline.
//!
//! Translates Move stackless bytecode to Lean via a sequence of small,
//! single-purpose stages. See `plans/lean-pipeline/` in the agent repo for the
//! design docs:
//!
//! - `../lean-pipeline-rebuild.md` -- umbrella plan (one level up, in `plans/`)
//! - `ir.md` -- IR shapes (re-exported here as `crate::ir`)
//! - `testing-strategy.md` -- test conventions
//! - `stage-NN-*.md` -- per-stage design notes
//!
//! Stages do not all share the same input/output type:
//!
//! | Stage | `run` signature                                                                          |
//! |-------|------------------------------------------------------------------------------------------|
//! | 1     | `fn run(code: &[Bytecode], target: &FunctionTarget) -> Result<BytecodeCfg, Stage1Error>` |
//! | 2     | `fn run(cfg: BytecodeCfg, target: &FunctionTarget, prog: &mut ProgramBuilder) -> ...`    |
//! | 3+    | mutate `&mut Program`; fallibility varies by pass (see each module)                      |
//!
//! See each stage module's docs for the concrete signature and what it
//! introduces / eliminates.

pub mod global_threading;
pub mod ir;
pub mod render;

pub use global_threading::thread_globals;

pub mod stage_01_bytecode_cfg;
pub mod stage_02_ir_cfg;
pub mod stage_03_demut;
pub mod stage_03_mut_to_let;
pub mod stage_04_effects;
pub mod stage_04_erase_mut;
pub mod stage_04_ghost;
pub mod stage_04_writeback;
pub mod stage_05_chain_complete;
pub mod stage_05_ssa;
pub mod stage_06_let_inline;
pub mod stage_07_dejumps;
pub mod stage_08_loops;
pub mod stage_10_bounded_nat;
pub mod stage_12_obligations;

// Active in the default flow (execution order is semantic, not numeric -- see
// `run_pipeline` / `stage_02_ir_cfg::pipeline`):
//   1 (bytecode CFG), 2 (bytecode -> IR; absorbs the stage-9 dyn-fields
//   design), 3 mut_to_let, 4 effects, 5 (SSA), 5 chain_complete
//   (writeback chain completion), 4 writeback (in-stage WriteBack
//   lowering), 7 (dejumps: .aborts variant + control-flow extraction),
//   6 (let-inline + DCE), 8 (final World-write closure), and 12 (obligations).
//   Bounded-nat lowering has two semantic boundaries: before stage 7 so
//   abort companions see partial arithmetic, and after cleanup so final
//   auto-dereference normalization reaches renderable form.
// Retained prototypes (not active in `run_pipeline`):
//   3 demut, 4 erase_mut.
// Not implemented:
//   11 (builtins).

/// Run the full pipeline end-to-end over a Move-model `GlobalEnv`
/// plus a `FunctionTargetsHolder`. Returns a fully-assembled
/// [`ir::Program`] with the per-stage transformations applied.
///
/// Order of steps (post-translation; matches the `--dump-ir-stages`
/// subdirectories): post-translation IR
/// → stage 3 (mut_to_let) → stage 4 (effects) → stage 5 (SSA) →
/// writeback completion/lowering → aborting-operand normalization → stage 10
/// (bounded_nat pre-stage-7) → stage 7 (dejumps + spec companion extraction)
/// → stage 6 (let-inline + DCE) → stage 8 (final World-write closure)
/// → full operand normalization → stage 10 (bounded_nat final) → stage 12 (proof
/// obligations). Execution order is intentionally not numeric.
///
/// `package_name_for_module` lets the caller (sui-lean) wire its
/// `Move.toml`-walking package-name lookup. The returned string is
/// stored in `Module::package_name` and is consulted by the per-thing
/// native classification predicates
/// (`stage_02_ir_cfg::natives::{is_native_struct, is_native_function,
/// is_native_function_module}`) to decide which modules / structs /
/// functions live in the prelude versus get translated.
pub use stage_02_ir_cfg::run_pipeline;
