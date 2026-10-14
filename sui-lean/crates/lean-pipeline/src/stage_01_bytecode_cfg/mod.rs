//! Stage 1 -- Bytecode -> Structured CFG. Reconstructs Move stackless
//! bytecode (`Label` / `Branch` / `Jump`) as a tree of
//! `while` / `if` / `switch` / `break` / `continue` / `return` / `abort`
//! regions. IR-free: terminators carry bytecode metadata only; stage 2
//! lifts to `Block` / `Stmt` / `BlockTail`.
//!
//! See `plans/lean-pipeline/stage-01-bytecode-cfg.md` for the design.

mod label_analysis;
mod loops;
mod structurer;
#[cfg(test)]
pub mod test_support;
#[cfg(test)]
mod tests;

use move_binary_format::file_format::CodeOffset;
use move_stackless_bytecode::ast::TempIndex;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::Bytecode;

/// Errors produced by stage 1.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stage1Error {
    /// Loop has no `cond_at`: no in-body block has a Branch with one
    /// in-body and one out-of-body arm. Fires for Move's `loop {}` and
    /// other loops with no clean exit decision.
    UnsupportedLoop { loop_header_pc: CodeOffset },

    /// `Graph::compute_reducible` returned `None`. Defensive guard;
    /// Move source generally produces reducible CFGs.
    IrreducibleCfg,

    /// Unstructurable shape (missing post-dom, >2 successors on a
    /// non-VariantSwitch, etc.) at `at`.
    UnsupportedGoto { at: CodeOffset },

    /// `structurer::structure` recursion exceeded the safety cap. The
    /// cap (`structurer::MAX_RECURSION_DEPTH`) is set high enough to
    /// admit any human-written Move function; hitting it indicates a
    /// pathological CFG (e.g. malformed bytecode that lets the
    /// post-dom walker cycle) that would otherwise blow the host
    /// stack. Recovered into a clean error so the per-function driver
    /// in `stage_02_ir_cfg::pipeline` can skip the function and keep
    /// going.
    RecursionLimit { depth: u32 },
}

/// The structured CFG produced by stage 1.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BytecodeCfg {
    pub root: Region,
}

/// A node in the structured CFG. Stage 2 lifts each variant into IR.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Region {
    /// Non-control-flow PC range, inclusive. Consumed terminators
    /// (`Branch` / `Jump` / `Ret` / `Abort` / `VariantSwitch`) are
    /// excluded; a block whose only content is a consumed terminator
    /// emits no `Basic`.
    Basic {
        lower: CodeOffset,
        upper: CodeOffset,
    },

    /// Sequence. `Seq(vec![])` is the canonical empty region.
    Seq(Vec<Region>),

    /// Two-way conditional, post-dom-recursed.
    If {
        cond_at: CodeOffset,
        then_branch: Box<Region>,
        else_branch: Box<Region>,
    },

    /// N-way switch; `branches` order matches the `Bytecode::VariantSwitch`
    /// `labels` vec.
    Switch {
        switch_at: CodeOffset,
        branches: Vec<Region>,
    },

    /// Loop. `header` is re-evaluated every iteration (may contain
    /// nested If / Switch for complex while-conds). `cond_at` is the
    /// deciding `Bytecode::Branch`. `body` is `Seq(vec![])` for
    /// header-only loops.
    While {
        header: Box<Region>,
        cond_at: CodeOffset,
        body: Box<Region>,
        /// `true` when the deciding branch's TRUE target is the loop
        /// EXIT (the loop continues on `cond == false`) -- the
        /// `loop { ...; if C { break }; body }` shape. Stage 2's
        /// `lift_while` then emits `Expr::While.cond = !cond_temp`.
        /// `false` for the normal `while (c)` shape (TRUE -> body),
        /// where the branch cond IS the continue predicate.
        negate_cond: bool,
    },

    /// Labeled scope. `body` may contain `Region::Term(Termination::ReturnFromBlock)`
    /// with `level: k` referring to the k-th enclosing LabeledBlock
    /// (innermost = 0). Stage 02 lifts this to `Expr::LabeledBlock`.
    /// See `plans/lean-pipeline/labeled-block-ir.md`.
    LabeledBlock { body: Box<Region> },

    /// Explicit termination. Innermost `Continue { level: 0 }` at the
    /// natural tail of a while body is implicit; everything else is
    /// emitted.
    Term(Termination),
}

/// Explicit termination of a `Region`. `level = 0` is innermost.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Termination {
    /// `Bytecode::Ret(temps)`.
    Return {
        temps: Vec<TempIndex>,
    },
    /// `Bytecode::Abort`. `code_temp = None` for synthesised aborts.
    Abort {
        code_temp: Option<TempIndex>,
    },
    Break {
        level: u32,
    },
    /// Cross-level `continue` (level > 0) -- innermost continues are
    /// implicit at the natural tail of a while body.
    Continue {
        level: u32,
    },
    /// Return from the `level`-th enclosing LabeledBlock (innermost = 0),
    /// carrying the value computed from `temps`. Counted independently
    /// from Break/Continue (which count loops, not labeled blocks).
    /// See `plans/lean-pipeline/labeled-block-ir.md`.
    ReturnFromBlock {
        level: u32,
        temps: Vec<TempIndex>,
    },
}

/// Reconstruct a structured CFG from Move stackless bytecode. `target`
/// carries the function identity for opt-in debug dumps (env var
/// `FOXY_DEBUG_LABEL_ANALYSIS=module::function` or `=*`).
pub fn run(code: &[Bytecode], target: &FunctionTarget) -> Result<BytecodeCfg, Stage1Error> {
    let env = target.func_env.module_env.env;
    let pool = env.symbol_pool();
    let module_name = pool
        .string(target.func_env.module_env.get_name().name())
        .to_string();
    let func_name = pool.string(target.func_env.get_name()).to_string();
    let qualified = format!("{}::{}", module_name, func_name);
    if std::env::var_os("FOXY_DEBUG_LABEL_ANALYSIS_TRACE").is_some() {
        eprintln!("[stage1::run] {qualified}");
    }
    if let Ok(want) = std::env::var("FOXY_DEBUG_LABEL_ANALYSIS") {
        if want == "*" || want == qualified || want == func_name {
            structurer::debug_dump_label_analysis(code, &qualified);
        }
    }
    structurer::run_from_code(code)
}

/// Tree-style pretty-printer for `Region`. Output is one node per line,
/// indented by depth, with PCs and termination targets inline. Companion
/// to the `Debug` impl which is exhaustive but hard to read at a glance.
pub fn pretty_region(cfg: &BytecodeCfg) -> String {
    let mut out = String::new();
    pp_region(&cfg.root, 0, &mut out);
    out
}

fn pp_region(r: &Region, depth: usize, out: &mut String) {
    let pad = "  ".repeat(depth);
    match r {
        Region::Basic { lower, upper } if lower == upper => {
            out.push_str(&format!("{pad}Basic pc={lower}\n"));
        }
        Region::Basic { lower, upper } => {
            out.push_str(&format!("{pad}Basic pc={lower}..{upper}\n"));
        }
        Region::Seq(parts) if parts.is_empty() => {
            out.push_str(&format!("{pad}Seq []\n"));
        }
        Region::Seq(parts) => {
            out.push_str(&format!("{pad}Seq\n"));
            for p in parts {
                pp_region(p, depth + 1, out);
            }
        }
        Region::If {
            cond_at,
            then_branch,
            else_branch,
        } => {
            out.push_str(&format!("{pad}If cond_at={cond_at}\n"));
            out.push_str(&format!("{pad}  then:\n"));
            pp_region(then_branch, depth + 2, out);
            out.push_str(&format!("{pad}  else:\n"));
            pp_region(else_branch, depth + 2, out);
        }
        Region::Switch {
            switch_at,
            branches,
        } => {
            out.push_str(&format!("{pad}Switch switch_at={switch_at}\n"));
            for (i, br) in branches.iter().enumerate() {
                out.push_str(&format!("{pad}  arm[{i}]:\n"));
                pp_region(br, depth + 2, out);
            }
        }
        Region::While {
            header,
            cond_at,
            body,
            negate_cond,
        } => {
            out.push_str(&format!(
                "{pad}While cond_at={cond_at} negate_cond={negate_cond}\n"
            ));
            out.push_str(&format!("{pad}  header:\n"));
            pp_region(header, depth + 2, out);
            out.push_str(&format!("{pad}  body:\n"));
            pp_region(body, depth + 2, out);
        }
        Region::LabeledBlock { body } => {
            out.push_str(&format!("{pad}LabeledBlock\n"));
            pp_region(body, depth + 1, out);
        }
        Region::Term(t) => {
            let s = match t {
                Termination::Return { temps } => format!("Return temps={temps:?}"),
                Termination::Abort { code_temp } => format!("Abort code_temp={code_temp:?}"),
                Termination::Break { level } => format!("Break level={level}"),
                Termination::Continue { level } => format!("Continue level={level}"),
                Termination::ReturnFromBlock { level, temps } => {
                    format!("ReturnFromBlock level={level} temps={temps:?}")
                }
            };
            out.push_str(&format!("{pad}Term({s})\n"));
        }
    }
}
