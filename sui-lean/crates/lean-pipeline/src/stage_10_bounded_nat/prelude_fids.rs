//! Stage 10 -- lazy idempotent registration of `BoundedU{N}_<op>`
//! synthetic natives.
//!
//! Stage 10 lowers every `BinOp` / `UnOp::Cast` on `Type::UInt(N)`
//! into a `Call` against a synthetic native. This module owns the
//! lookup-or-allocate step for the FunIds of those natives plus
//! their `.aborts` companions.
//!
//! ## Naming convention
//!
//! Main function names embed the source operand width:
//!
//! - `BoundedU{N}_add`, `_sub`, `_mul`, `_div`, `_mod`            (Move/unsigned arith)
//! - `_wrapping_{add,sub,mul}`, `_s{add,sub,mul,div,mod}`          (C/LLVM arith)
//! - `BoundedU{N}_band`, `_bor`, `_bxor`                          (bitwise)
//! - `BoundedU{N}_{shl,shr,lshr,ashr}_u{K}` (rhs may differ)       (shifts)
//! - `BoundedU{N}_eq`, `_neq`, `_lt`... and `_slt`...              (cmp)
//! - `BoundedU{N}_bnot`                                           (bitwise NOT)
//! - `BoundedU{N}_to_u{M}`                                        (casts)
//!
//! `.aborts` companion names append `_aborts`. The renderer maps
//! these IR-side names to Lean expressions
//! (`BoundedU64_add` -> `BoundedNat.add`, etc.) -- Lean infers the
//! `bound` parameter from operand types.
//!
//! ## Idempotency
//!
//! Both `ensure_main_fid` and `ensure_aborts_fid` reuse only an exact
//! synthetic declaration. A same-named user or malformed native is left
//! intact while the intrinsic receives a distinct FunId. A second call
//! returns the exact synthetic FunId.
//!
//! ## Stage-7 integration
//!
//! Aborts companions are registered as `NativeDecl` entries in
//! `program.natives.decls` with `spec_target: Some(<main fid>)`.
//! Stage 7's `aborts_map` collection iterates both `program.functions`
//! (translated aborts) AND `program.natives.decls` (synth-native
//! aborts), so our companions are picked up automatically.

use crate::ir::function::{Param, Signature};
use crate::ir::ty::Type;
use crate::ir::{Effects, FunId, NativeDecl, Program};

/// Move's six unsigned integer widths.
pub const WIDTHS: [u32; 6] = [8, 16, 32, 64, 128, 256];

/// Operation kinds stage 10 lowers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Op {
    Add,
    Sub,
    Mul,
    WrappingAdd,
    WrappingSub,
    WrappingMul,
    SAdd,
    SSub,
    SMul,
    Div,
    Mod,
    SDiv,
    SMod,
    BitAnd,
    BitOr,
    BitXor,
    Shl { rhs_width: u32 },
    Shr { rhs_width: u32 },
    LShr { rhs_width: u32 },
    AShr { rhs_width: u32 },
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    SLt,
    SLe,
    SGt,
    SGe,
    BitNot,
    Cast { dst: u32 },
}

impl Op {
    pub fn arity(self) -> usize {
        match self {
            Op::BitNot | Op::Cast { .. } => 1,
            _ => 2,
        }
    }

    pub fn return_type(self, src_width: u32) -> Type {
        match self {
            Op::Eq
            | Op::Neq
            | Op::Lt
            | Op::Le
            | Op::Gt
            | Op::Ge
            | Op::SLt
            | Op::SLe
            | Op::SGt
            | Op::SGe => Type::Bool,
            Op::Cast { dst } => Type::UInt(dst),
            _ => Type::UInt(src_width),
        }
    }

    pub fn can_abort_at(self, src_width: u32) -> bool {
        match self {
            Op::Add
            | Op::Sub
            | Op::Mul
            | Op::SAdd
            | Op::SSub
            | Op::SMul
            | Op::Div
            | Op::Mod
            | Op::SDiv
            | Op::SMod => true,
            Op::Shl { .. } | Op::Shr { .. } | Op::LShr { .. } | Op::AShr { .. } => true,
            Op::Cast { dst } => dst < src_width,
            _ => false,
        }
    }

    pub fn main_effects(self, src_width: u32) -> crate::ir::Effects {
        use crate::ir::{AbortBit, DetBit, Effects, MutLevel};
        if self.can_abort_at(src_width) {
            Effects {
                aborts: AbortBit::Partial,
                det: DetBit::Det,
                mutation: MutLevel::NoMut,
                world_writes: false,
            }
        } else {
            Effects::PURE
        }
    }
}

pub fn main_name(op: Op, src_width: u32) -> String {
    let prefix = format!("BoundedU{src_width}");
    match op {
        Op::Add => format!("{prefix}_add"),
        Op::Sub => format!("{prefix}_sub"),
        Op::Mul => format!("{prefix}_mul"),
        Op::WrappingAdd => format!("{prefix}_wrapping_add"),
        Op::WrappingSub => format!("{prefix}_wrapping_sub"),
        Op::WrappingMul => format!("{prefix}_wrapping_mul"),
        Op::SAdd => format!("{prefix}_sadd"),
        Op::SSub => format!("{prefix}_ssub"),
        Op::SMul => format!("{prefix}_smul"),
        Op::Div => format!("{prefix}_div"),
        Op::Mod => format!("{prefix}_mod"),
        Op::SDiv => format!("{prefix}_sdiv"),
        Op::SMod => format!("{prefix}_smod"),
        Op::BitAnd => format!("{prefix}_band"),
        Op::BitOr => format!("{prefix}_bor"),
        Op::BitXor => format!("{prefix}_bxor"),
        Op::Shl { rhs_width } => format!("{prefix}_shl_u{rhs_width}"),
        Op::Shr { rhs_width } => format!("{prefix}_shr_u{rhs_width}"),
        Op::LShr { rhs_width } => format!("{prefix}_lshr_u{rhs_width}"),
        Op::AShr { rhs_width } => format!("{prefix}_ashr_u{rhs_width}"),
        Op::Eq => format!("{prefix}_eq"),
        Op::Neq => format!("{prefix}_neq"),
        Op::Lt => format!("{prefix}_lt"),
        Op::Le => format!("{prefix}_le"),
        Op::Gt => format!("{prefix}_gt"),
        Op::Ge => format!("{prefix}_ge"),
        Op::SLt => format!("{prefix}_slt"),
        Op::SLe => format!("{prefix}_sle"),
        Op::SGt => format!("{prefix}_sgt"),
        Op::SGe => format!("{prefix}_sge"),
        Op::BitNot => format!("{prefix}_bnot"),
        Op::Cast { dst } => format!("{prefix}_to_u{dst}"),
    }
}

pub fn aborts_name(op: Op, src_width: u32) -> String {
    format!("{}_aborts", main_name(op, src_width))
}

pub fn is_aborting_native_pair(target: &NativeDecl, companion: &NativeDecl) -> bool {
    let Some((op, src_width)) = aborting_op_for_name(&target.name) else {
        return false;
    };
    target.module == companion.module
        && target.is_framework
        && companion.is_framework
        && target.user_native.is_none()
        && companion.user_native.is_none()
        && target.explicit_pure
        && companion.explicit_pure
        && target.spec_target.is_none()
        && companion.name == aborts_name(op, src_width)
        && target.effects == op.main_effects(src_width)
        && companion.effects == Effects::PURE
        && target.signature.type_params.is_empty()
        && companion.signature.type_params.is_empty()
        && target.signature.params == build_params(&main_param_types(op, src_width))
        && companion.signature.params == build_params(&main_param_types(op, src_width))
        && target.signature.return_type == op.return_type(src_width)
        && companion.signature.return_type == Type::Bool
}

fn aborting_op_for_name(name: &str) -> Option<(Op, u32)> {
    for src_width in WIDTHS {
        for op in [
            Op::Add,
            Op::Sub,
            Op::Mul,
            Op::SAdd,
            Op::SSub,
            Op::SMul,
            Op::Div,
            Op::Mod,
            Op::SDiv,
            Op::SMod,
        ] {
            if main_name(op, src_width) == name {
                return Some((op, src_width));
            }
        }
        for rhs_width in WIDTHS {
            for op in [
                Op::Shl { rhs_width },
                Op::Shr { rhs_width },
                Op::LShr { rhs_width },
                Op::AShr { rhs_width },
            ] {
                if main_name(op, src_width) == name {
                    return Some((op, src_width));
                }
            }
        }
        for dst in WIDTHS {
            let op = Op::Cast { dst };
            if dst < src_width && main_name(op, src_width) == name {
                return Some((op, src_width));
            }
        }
    }
    None
}

fn main_param_types(op: Op, src_width: u32) -> Vec<Type> {
    let src = Type::UInt(src_width);
    match op {
        Op::BitNot | Op::Cast { .. } => vec![src],
        Op::Shl { rhs_width }
        | Op::Shr { rhs_width }
        | Op::LShr { rhs_width }
        | Op::AShr { rhs_width } => {
            vec![src, Type::UInt(rhs_width)]
        }
        _ => vec![src.clone(), src],
    }
}

/// Look up or allocate the main FunId for `(op, src_width)`.
/// Idempotent across repeated calls.
pub fn ensure_main_fid(program: &mut Program, op: Op, src_width: u32) -> FunId {
    let module = program.first_module_id();
    let params = build_params(&main_param_types(op, src_width));
    let return_type = op.return_type(src_width);
    program.insert_synthetic_native(
        &main_name(op, src_width),
        Signature {
            type_params: Vec::new(),
            params,
            return_type,
        },
        crate::ir::SyntheticNativeOpts {
            module,
            effects: op.main_effects(src_width),
            explicit_pure: true,
            spec_target: None,
        },
    )
}

/// Look up or allocate the `.aborts` companion FunId for `(op,
/// src_width)`. Returns `None` when the op cannot abort.
pub fn ensure_aborts_fid(program: &mut Program, op: Op, src_width: u32) -> Option<FunId> {
    if !op.can_abort_at(src_width) {
        return None;
    }
    let main_fid = ensure_main_fid(program, op, src_width);
    let module = program.first_module_id();
    let params = build_params(&main_param_types(op, src_width));
    // Back-reference: stage 7's aborts_map will collect this
    // (target -> companion) pair when iterating natives.decls.
    let fid = program.insert_synthetic_native(
        &aborts_name(op, src_width),
        Signature {
            type_params: Vec::new(),
            params,
            return_type: Type::Bool,
        },
        crate::ir::SyntheticNativeOpts {
            module,
            effects: crate::ir::Effects::PURE,
            explicit_pure: true,
            spec_target: Some(main_fid),
        },
    );
    Some(fid)
}

fn build_params(types: &[Type]) -> Vec<Param> {
    types
        .iter()
        .enumerate()
        .map(|(i, ty)| {
            let name = match i {
                0 => "a",
                1 => "b",
                _ => "c",
            };
            Param {
                name: name.to_string(),
                var: name.into(),
                ty: ty.clone(),
            }
        })
        .collect()
}
