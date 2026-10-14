//! Render-side mapping for stage-10 `BoundedU{N}_<op>` natives.
//!
//! Stage 10 ([`crate::stage_10_bounded_nat`]) registers synthetic
//! per-width natives with IR-side names like `BoundedU64_add` and
//! their `.aborts` companions like `BoundedU64_add_aborts`. The
//! Lean prelude (`lemmas/Prelude/BoundedNat.lean`) exposes a single
//! generic family parameterised by the `bound : Nat` -- Lean's
//! typeclass inference picks the right `bound` from the operand
//! types. So the renderer maps every `BoundedU{N}_<op>` call to its
//! width-agnostic Lean shape:
//!
//! | IR-side name                | Lean expression                                |
//! |-----------------------------|------------------------------------------------|
//! | `BoundedU{N}_add`           | `BoundedNat.add <a> <b>`                       |
//! | `BoundedU{N}_sub`           | `BoundedNat.sub <a> <b>`                       |
//! | `BoundedU{N}_mul`           | `BoundedNat.mul <a> <b>`                       |
//! | `BoundedU{N}_wrapping_*`    | `BoundedNat.wrapping_* <a> <b>`                |
//! | `BoundedU{N}_sadd/ssub/smul`| `BoundedNat.sadd/ssub/smul <a> <b>`            |
//! | `BoundedU{N}_div`           | `BoundedNat.div <a> <b>`                       |
//! | `BoundedU{N}_mod`           | `BoundedNat.mod <a> <b>`                       |
//! | `BoundedU{N}_sdiv/smod`     | `BoundedNat.sdiv/smod <a> <b>`                 |
//! | `BoundedU{N}_band`          | `BoundedNat.land <a> <b>`                      |
//! | `BoundedU{N}_bor`           | `BoundedNat.lor <a> <b>`                       |
//! | `BoundedU{N}_bxor`          | `BoundedNat.bxor <a> <b>`                      |
//! | `BoundedU{N}_shl_u{K}`      | `(<a> <<< <b>)`            (HShiftLeft inst.)  |
//! | `BoundedU{N}_shr_u{K}`      | `(<a> >>> <b>)`            (HShiftRight inst.) |
//! | `BoundedU{N}_lshr_u{K}`     | `(<a> >>> <b>)`            (HShiftRight inst.) |
//! | `BoundedU{N}_ashr_u{K}`     | `BoundedNat.ashr <a> <b>`                      |
//! | `BoundedU{N}_eq`            | `BoundedNat.eq <a> <b>`                        |
//! | `BoundedU{N}_neq`           | `BoundedNat.neq <a> <b>`                       |
//! | `BoundedU{N}_lt`            | `BoundedNat.lt <a> <b>`                        |
//! | `BoundedU{N}_le`            | `BoundedNat.le <a> <b>`                        |
//! | `BoundedU{N}_gt`            | `BoundedNat.gt <a> <b>`                        |
//! | `BoundedU{N}_ge`            | `BoundedNat.ge <a> <b>`                        |
//! | `BoundedU{N}_slt/sle/sgt/sge` | matching signed `BoundedNat` helper          |
//! | `BoundedU{N}_bnot`          | `BoundedNat.bnot <a>`                          |
//! | `BoundedU{N}_to_u{M}`       | `((BoundedNat.convert <a>) : BoundedU{M})`     |
//!
//! Abort companion mappings:
//!
//! | IR-side name                       | Lean expression                                       |
//! |------------------------------------|-------------------------------------------------------|
//! | `BoundedU{N}_add_aborts`           | `BoundedNat.add_aborts <a> <b>`                       |
//! | `BoundedU{N}_sub_aborts`           | `BoundedNat.sub_aborts <a> <b>`                       |
//! | `BoundedU{N}_mul_aborts`           | `BoundedNat.mul_aborts <a> <b>`                       |
//! | `BoundedU{N}_div_aborts`           | `BoundedNat.div_aborts <a> <b>`                       |
//! | `BoundedU{N}_mod_aborts`           | `BoundedNat.mod_aborts <a> <b>`                       |
//! | `BoundedU{N}_shl_u{K}_aborts`      | `BoundedNat.shl_bounded_aborts <a> <b>`               |
//! | `BoundedU{N}_shr_u{K}_aborts`      | `BoundedNat.shr_bounded_aborts <a> <b>`               |
//! | `BoundedU{N}_to_u{M}_aborts`       | `(BoundedNat.convert_aborts (bound_to := 2^{M}) <a>)` |
//!
//! Bitwise (`band`/`bor`/`bxor`/`bnot`) and comparison ops never
//! have an aborts companion -- the stage-10 [`prelude_fids`] module
//! omits them, and the stage 10 native registrations classify them
//! as `AbortBit::Total`, so stage 7's abort-companion derivation
//! contributes `Bool(false)`.

use std::fmt::Write;

use crate::ir::expr::Expr;

use super::expr::{render_with_parens_if_needed, ExprCtx};
use super::writer::LeanWriter;
use super::RenderResult;

/// Parsed form of an IR-side `BoundedU...` name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Parsed<'a> {
    /// `BoundedU{N}_{op}` where `op` is one of the base names.
    Main { src: u32, op: &'a str },
    /// `BoundedU{N}_{op}_aborts`.
    MainAborts { src: u32, op: &'a str },
    /// `BoundedU{N}_to_u{M}`.
    Cast { src: u32, dst: u32 },
    /// `BoundedU{N}_to_u{M}_aborts`.
    CastAborts { src: u32, dst: u32 },
    /// `BoundedU{N}_shl_u{K}` or `_shr_u{K}`.
    Shift { src: u32, op: ShiftDir, rhs: u32 },
    /// `BoundedU{N}_shl_u{K}_aborts` or `_shr_u{K}_aborts`.
    ShiftAborts { src: u32, op: ShiftDir, rhs: u32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ShiftDir {
    Shl,
    Shr,
    LShr,
    AShr,
}

/// Parse an IR-side name into its semantic shape. Returns `None` for
/// non-BoundedU names.
fn parse_name(name: &str) -> Option<Parsed<'_>> {
    let rest = name.strip_prefix("BoundedU")?;
    // Split off the source width.
    let (src_str, tail) = split_at_underscore(rest)?;
    let src = src_str.parse::<u32>().ok()?;
    // `to_u{M}` (with optional `_aborts`).
    if let Some(after_to) = tail.strip_prefix("to_u") {
        let aborts_stripped = after_to.strip_suffix("_aborts");
        let dst_str = aborts_stripped.unwrap_or(after_to);
        let dst = dst_str.parse::<u32>().ok()?;
        return Some(if aborts_stripped.is_some() {
            Parsed::CastAborts { src, dst }
        } else {
            Parsed::Cast { src, dst }
        });
    }
    // Width-tagged shifts (with optional `_aborts`). `shr` is the
    // pre-existing Move spelling; `lshr`/`ashr` are explicit LLVM forms.
    for (prefix, dir) in [
        ("shl_u", ShiftDir::Shl),
        ("shr_u", ShiftDir::Shr),
        ("lshr_u", ShiftDir::LShr),
        ("ashr_u", ShiftDir::AShr),
    ] {
        if let Some(after) = tail.strip_prefix(prefix) {
            let aborts_stripped = after.strip_suffix("_aborts");
            let rhs_str = aborts_stripped.unwrap_or(after);
            let rhs = rhs_str.parse::<u32>().ok()?;
            return Some(if aborts_stripped.is_some() {
                Parsed::ShiftAborts { src, op: dir, rhs }
            } else {
                Parsed::Shift { src, op: dir, rhs }
            });
        }
    }
    // Plain `<op>` or `<op>_aborts`.
    if let Some(op) = tail.strip_suffix("_aborts") {
        return Some(Parsed::MainAborts { src, op });
    }
    Some(Parsed::Main { src, op: tail })
}

pub(super) fn is_intrinsic_name(name: &str) -> bool {
    match parse_name(name) {
        Some(Parsed::Main { src, op }) => valid_width(src) && valid_main_op(op),
        Some(Parsed::MainAborts { src, op }) => valid_width(src) && valid_aborting_op(op),
        Some(Parsed::Cast { src, dst }) => valid_width(src) && valid_width(dst),
        Some(Parsed::CastAborts { src, dst }) => valid_width(src) && valid_width(dst) && dst < src,
        Some(Parsed::Shift { src, rhs, .. } | Parsed::ShiftAborts { src, rhs, .. }) => {
            valid_width(src) && valid_width(rhs)
        }
        None => false,
    }
}

pub(super) fn is_intrinsic_decl(
    fid: crate::ir::FunId,
    decl: &crate::ir::NativeDecl,
    program: &crate::ir::Program,
) -> bool {
    if !decl.is_framework
        || decl.user_native.is_some()
        || !decl.explicit_pure
        || !decl.signature.type_params.is_empty()
    {
        return false;
    }
    let Some(parsed) = parse_name(&decl.name).filter(|_| is_intrinsic_name(&decl.name)) else {
        return false;
    };
    let (param_types, return_type, is_aborts, main_can_abort) = match parsed {
        Parsed::Main { src, op } => {
            let params = if op == "bnot" {
                vec![crate::ir::Type::UInt(src)]
            } else {
                vec![crate::ir::Type::UInt(src), crate::ir::Type::UInt(src)]
            };
            let result = if matches!(
                op,
                "eq" | "neq" | "lt" | "le" | "gt" | "ge" | "slt" | "sle" | "sgt" | "sge"
            ) {
                crate::ir::Type::Bool
            } else {
                crate::ir::Type::UInt(src)
            };
            (
                params,
                result,
                false,
                matches!(
                    op,
                    "add"
                        | "sub"
                        | "mul"
                        | "sadd"
                        | "ssub"
                        | "smul"
                        | "div"
                        | "mod"
                        | "sdiv"
                        | "smod"
                ),
            )
        }
        Parsed::MainAborts { src, .. } => (
            vec![crate::ir::Type::UInt(src), crate::ir::Type::UInt(src)],
            crate::ir::Type::Bool,
            true,
            false,
        ),
        Parsed::Cast { src, dst } => (
            vec![crate::ir::Type::UInt(src)],
            crate::ir::Type::UInt(dst),
            false,
            dst < src,
        ),
        Parsed::CastAborts { src, .. } => (
            vec![crate::ir::Type::UInt(src)],
            crate::ir::Type::Bool,
            true,
            false,
        ),
        Parsed::Shift { src, rhs, .. } => (
            vec![crate::ir::Type::UInt(src), crate::ir::Type::UInt(rhs)],
            crate::ir::Type::UInt(src),
            false,
            true,
        ),
        Parsed::ShiftAborts { src, rhs, .. } => (
            vec![crate::ir::Type::UInt(src), crate::ir::Type::UInt(rhs)],
            crate::ir::Type::Bool,
            true,
            false,
        ),
    };
    let params = param_types
        .into_iter()
        .enumerate()
        .map(|(index, ty)| {
            let name = match index {
                0 => "a",
                1 => "b",
                _ => return None,
            };
            Some(crate::ir::Param {
                name: name.to_string(),
                var: name.into(),
                ty,
            })
        })
        .collect::<Option<Vec<_>>>();
    let Some(params) = params else {
        return false;
    };
    let expected_signature = crate::ir::Signature {
        type_params: Vec::new(),
        params,
        return_type,
    };
    let expected_effects = if !is_aborts && main_can_abort {
        crate::ir::Effects {
            aborts: crate::ir::AbortBit::Partial,
            det: crate::ir::DetBit::Det,
            mutation: crate::ir::MutLevel::NoMut,
            world_writes: false,
        }
    } else {
        crate::ir::Effects::PURE
    };
    if decl.signature != expected_signature || decl.effects != expected_effects {
        return false;
    }
    if !is_aborts {
        return decl.spec_target.is_none();
    }
    let Some(target_fid) = decl.spec_target else {
        return false;
    };
    target_fid != fid
        && program
            .natives
            .decls
            .get(&target_fid)
            .is_some_and(|target| {
                target.module == decl.module
                    && target.name == decl.name.trim_end_matches("_aborts")
                    && is_intrinsic_decl(target_fid, target, program)
            })
}

fn valid_width(width: u32) -> bool {
    matches!(width, 8 | 16 | 32 | 64 | 128 | 256)
}

fn valid_main_op(op: &str) -> bool {
    matches!(
        op,
        "add"
            | "sub"
            | "mul"
            | "wrapping_add"
            | "wrapping_sub"
            | "wrapping_mul"
            | "sadd"
            | "ssub"
            | "smul"
            | "div"
            | "mod"
            | "sdiv"
            | "smod"
            | "band"
            | "bor"
            | "bxor"
            | "eq"
            | "neq"
            | "lt"
            | "le"
            | "gt"
            | "ge"
            | "slt"
            | "sle"
            | "sgt"
            | "sge"
            | "bnot"
    )
}

fn valid_aborting_op(op: &str) -> bool {
    matches!(
        op,
        "add" | "sub" | "mul" | "sadd" | "ssub" | "smul" | "div" | "mod" | "sdiv" | "smod"
    )
}

fn split_at_underscore(s: &str) -> Option<(&str, &str)> {
    let i = s.find('_')?;
    Some((&s[..i], &s[i + 1..]))
}

/// Attempt to render a Call against a `BoundedU{...}` native. Returns
/// `Ok(true)` when the callee was a BoundedNat helper (and was
/// emitted); `Ok(false)` when the declaration is not an exact
/// stage-10 intrinsic (caller falls through to the generic path);
/// `Err` on render failure.
pub fn try_render_call<W: Write>(
    fid: crate::ir::FunId,
    decl: &crate::ir::NativeDecl,
    args: &[Expr],
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<bool> {
    if !is_intrinsic_decl(fid, decl, ctx.program) {
        return Ok(false);
    }
    let Some(parsed) = parse_name(&decl.name) else {
        return Ok(false);
    };
    match parsed {
        Parsed::Main { op, .. } => {
            // Width-agnostic `BoundedNat.<op>`. Lean infers bound from arg types.
            let Some(lean_op) = lean_op_name(op) else {
                return Ok(false);
            };
            render_prefix_call(&format!("BoundedNat.{lean_op}"), args, ctx, w)?;
        }
        Parsed::MainAborts { op, .. } => {
            let Some(lean_op) = lean_op_name(op) else {
                return Ok(false);
            };
            render_prefix_call(&format!("BoundedNat.{lean_op}_aborts"), args, ctx, w)?;
        }
        Parsed::Cast { dst, .. } => {
            // `((BoundedNat.convert <a>) : BoundedU{dst})`.
            // The type ascription pins `bound_to` so Lean can resolve
            // the convert -- the input type fixes `bound_from`.
            if args.len() != 1 {
                return Ok(false);
            }
            w.write("((BoundedNat.convert ");
            render_with_parens_if_needed(&args[0], ctx, w)?;
            w.write(&format!(") : BoundedU{dst})"));
        }
        Parsed::CastAborts { dst, .. } => {
            // `(BoundedNat.convert_aborts (bound_to := 2^{dst}) <a>)`.
            if args.len() != 1 {
                return Ok(false);
            }
            w.write(&format!(
                "(BoundedNat.convert_aborts (bound_to := 2^{dst}) "
            ));
            render_with_parens_if_needed(&args[0], ctx, w)?;
            w.write(")");
        }
        Parsed::Shift { op, .. } => {
            // `(<a> <<< <b>)` / `(<a> >>> <b>)` via the HShiftLeft /
            // HShiftRight instances on `BoundedNat`. Both operand
            // types determine the bounds.
            if args.len() != 2 {
                return Ok(false);
            }
            if op == ShiftDir::AShr {
                render_prefix_call("BoundedNat.ashr", args, ctx, w)?;
            } else {
                w.write("(");
                render_with_parens_if_needed(&args[0], ctx, w)?;
                w.write(match op {
                    ShiftDir::Shl => " <<< ",
                    ShiftDir::Shr | ShiftDir::LShr => " >>> ",
                    ShiftDir::AShr => unreachable!("handled above"),
                });
                render_with_parens_if_needed(&args[1], ctx, w)?;
                w.write(")");
            }
        }
        Parsed::ShiftAborts { op, .. } => {
            let lean_fn = match op {
                ShiftDir::Shl => "BoundedNat.shl_bounded_aborts",
                ShiftDir::Shr => "BoundedNat.shr_bounded_aborts",
                ShiftDir::LShr => "BoundedNat.lshr_bounded_aborts",
                ShiftDir::AShr => "BoundedNat.ashr_bounded_aborts",
            };
            render_prefix_call(lean_fn, args, ctx, w)?;
        }
    }
    Ok(true)
}

/// Map a stage-10 IR op-name segment to its Lean function name. The
/// only renames are bitwise (`band`/`bor` -> `land`/`lor`) -- everything
/// else matches one-for-one.
fn lean_op_name(op: &str) -> Option<&'static str> {
    Some(match op {
        "add" => "add",
        "sub" => "sub",
        "mul" => "mul",
        "wrapping_add" => "wrapping_add",
        "wrapping_sub" => "wrapping_sub",
        "wrapping_mul" => "wrapping_mul",
        "sadd" => "sadd",
        "ssub" => "ssub",
        "smul" => "smul",
        "div" => "div",
        "mod" => "mod",
        "sdiv" => "sdiv",
        "smod" => "smod",
        "band" => "land",
        "bor" => "lor",
        "bxor" => "bxor",
        "eq" => "eq",
        "neq" => "neq",
        "lt" => "lt",
        "le" => "le",
        "gt" => "gt",
        "ge" => "ge",
        "slt" => "slt",
        "sle" => "sle",
        "sgt" => "sgt",
        "sge" => "sge",
        "bnot" => "bnot",
        _ => return None,
    })
}

fn render_prefix_call<W: Write>(
    head: &str,
    args: &[Expr],
    ctx: &ExprCtx<'_>,
    w: &mut LeanWriter<W>,
) -> RenderResult<()> {
    if args.is_empty() {
        w.write(head);
        return Ok(());
    }
    w.write("(");
    w.write(head);
    for a in args {
        w.write(" ");
        render_with_parens_if_needed(a, ctx, w)?;
    }
    w.write(")");
    Ok(())
}

// ---------------------------------------------------------------------------
// Tests for the name parser
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_arithmetic_main() {
        assert_eq!(
            parse_name("BoundedU64_add"),
            Some(Parsed::Main { src: 64, op: "add" })
        );
        assert_eq!(
            parse_name("BoundedU8_div"),
            Some(Parsed::Main { src: 8, op: "div" })
        );
    }

    #[test]
    fn parses_arithmetic_aborts() {
        assert_eq!(
            parse_name("BoundedU64_add_aborts"),
            Some(Parsed::MainAborts { src: 64, op: "add" })
        );
        assert_eq!(
            parse_name("BoundedU128_mod_aborts"),
            Some(Parsed::MainAborts {
                src: 128,
                op: "mod"
            })
        );
    }

    #[test]
    fn parses_cast() {
        assert_eq!(
            parse_name("BoundedU64_to_u8"),
            Some(Parsed::Cast { src: 64, dst: 8 })
        );
        assert_eq!(
            parse_name("BoundedU64_to_u8_aborts"),
            Some(Parsed::CastAborts { src: 64, dst: 8 })
        );
    }

    #[test]
    fn parses_shift_both_directions() {
        assert_eq!(
            parse_name("BoundedU64_shl_u8"),
            Some(Parsed::Shift {
                src: 64,
                op: ShiftDir::Shl,
                rhs: 8
            })
        );
        assert_eq!(
            parse_name("BoundedU32_shr_u8_aborts"),
            Some(Parsed::ShiftAborts {
                src: 32,
                op: ShiftDir::Shr,
                rhs: 8
            })
        );
    }

    #[test]
    fn parses_comparison() {
        assert_eq!(
            parse_name("BoundedU64_eq"),
            Some(Parsed::Main { src: 64, op: "eq" })
        );
        assert_eq!(
            parse_name("BoundedU64_lt"),
            Some(Parsed::Main { src: 64, op: "lt" })
        );
    }

    #[test]
    fn parses_bitwise() {
        assert_eq!(
            parse_name("BoundedU64_band"),
            Some(Parsed::Main {
                src: 64,
                op: "band"
            })
        );
        assert_eq!(
            parse_name("BoundedU64_bnot"),
            Some(Parsed::Main {
                src: 64,
                op: "bnot"
            })
        );
    }

    #[test]
    fn rejects_non_bounded_names() {
        assert!(parse_name("vector_length").is_none());
        assert!(parse_name("foo").is_none());
    }

    #[test]
    fn intrinsic_classification_rejects_unknown_ops_and_widths() {
        assert!(is_intrinsic_name("BoundedU64_add"));
        assert!(is_intrinsic_name("BoundedU256_to_u8_aborts"));
        assert!(!is_intrinsic_name("BoundedU64_unknown"));
        assert!(!is_intrinsic_name("BoundedU64_eq_aborts"));
        assert!(!is_intrinsic_name("BoundedU7_add"));
        assert!(!is_intrinsic_name("BoundedU64_to_u7"));
        assert!(!is_intrinsic_name("BoundedU8_to_u64_aborts"));
    }

    #[test]
    fn intrinsic_classification_requires_exact_stage10_declaration() {
        let mut program = crate::ir::Program::default();
        program.modules.insert(
            0,
            crate::ir::Module {
                name: "math".to_string(),
                package_name: "P".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        let main = crate::stage_10_bounded_nat::prelude_fids::ensure_main_fid(
            &mut program,
            crate::stage_10_bounded_nat::prelude_fids::Op::Add,
            64,
        );
        let aborts = crate::stage_10_bounded_nat::prelude_fids::ensure_aborts_fid(
            &mut program,
            crate::stage_10_bounded_nat::prelude_fids::Op::Add,
            64,
        )
        .unwrap();
        assert!(is_intrinsic_decl(
            main,
            &program.natives.decls[&main],
            &program
        ));
        assert!(is_intrinsic_decl(
            aborts,
            &program.natives.decls[&aborts],
            &program
        ));

        let mut reserved_lookalike = program.natives.decls[&main].clone();
        reserved_lookalike.is_framework = false;
        assert!(!is_intrinsic_decl(main, &reserved_lookalike, &program));
        reserved_lookalike.is_framework = true;
        reserved_lookalike.signature.return_type = crate::ir::Type::Bool;
        assert!(!is_intrinsic_decl(main, &reserved_lookalike, &program));
    }
}
