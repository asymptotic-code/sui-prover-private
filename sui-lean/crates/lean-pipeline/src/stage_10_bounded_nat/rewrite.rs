//! Stage 10 -- the IR rewrite.
//!
//! Lowers every `BinOp` on UInt operands and `UnOp::Cast` on a UInt
//! operand into a `Call` against the registered `BoundedU{N}_<op>`
//! synthetic native.
//!
//! Walks every non-native function body. Skips native and synthetic
//! stub functions (in particular, the BoundedU helpers we just
//! registered).
//!
//! ## Algorithm
//!
//! Three passes:
//!
//! 1. **Collect.** Walk each function body building a `Scope` from
//!    params + `Stmt::Let` bindings; for every `BinOp`/`Cast` site
//!    on UInt operands, record the `(op, src_width)` registration
//!    need. Read-only on `Program`.
//! 2. **Register.** Call [`super::prelude_fids::ensure_main_fid`] +
//!    [`super::prelude_fids::ensure_aborts_fid`] for every collected
//!    pair and retain the returned exact synthetic `FunId`. Idempotent.
//! 3. **Rewrite.** Walk each function body again with `&mut`; for
//!    every match-site, replace the `BinOp`/`Cast` with a `Call`
//!    against the FunId in the prepared `(Op, width) -> FunId`
//!    lookup table.
//!
//! Splitting collect-then-register-then-rewrite avoids holding a
//! mutable borrow on `Program` while the rewriter needs `type_of`
//! to inspect callee signatures.
//!
//! Both walks share the typed-scope walker in
//! [`crate::ir::analysis::scope`]: the collector is a read-only
//! [`TypedScopeVisitor`], the rewriter an in-place
//! [`TypedScopeMutVisitor`] (post-order, so nested arithmetic sees its
//! inner sites already lowered to `Call`s). Binder types come from the
//! canonical `bind_pattern` -- a malformed Let is a hard `TypeOfError`,
//! propagated with the function and rewrite phase.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::analysis::scope::{
    walk_typed_block, walk_typed_block_mut, TypedScope, TypedScopeMutVisitor, TypedScopeVisitor,
};
use crate::ir::analysis::type_of::{type_of, TypeOfError};
use crate::ir::expr::Expr;
use crate::ir::ops::{BinOp, UnOp};
use crate::ir::ty::Type;
use crate::ir::{FunId, Program, VarId};

use super::prelude_fids::{ensure_aborts_fid, ensure_main_fid, Op};
use super::{Stage10Error, Stage10FunctionFailure, Stage10RewritePhase};

type Scope = BTreeMap<VarId, Type>;

/// `(op, src_width) -> main FunId` lookup for pass 3.
type FidMap = BTreeMap<(Op, u32), FunId>;

pub fn run(program: &mut Program) -> Result<(), Stage10Error> {
    // Functions we will walk: non-native, real-bodied. Capture the
    // ids up front so we can mutate the program (registering new
    // BoundedU FunIds) without invalidating the iteration.
    let target_fids: Vec<FunId> = program.functions.iter().map(|(id, _)| *id).collect();

    // Pass 1: collect (Op, src_width) registration needs across the
    // whole program.
    //
    // A per-function TypeOf failure does not prevent other functions
    // from being lowered, but it is returned to the driver after the
    // pass so neither driver mode can silently accept the failed body.
    let mut needs: BTreeSet<(Op, u32)> = BTreeSet::new();
    let mut failed: BTreeSet<FunId> = BTreeSet::new();
    let mut failures = Vec::new();
    for fid in &target_fids {
        if let Err(err) = collect_needs_function(program, *fid, &mut needs) {
            failed.insert(*fid);
            failures.push(Stage10FunctionFailure {
                function: *fid,
                phase: Stage10RewritePhase::CollectNeeds,
                err,
            });
        }
    }

    // Pass 2: register every needed main + aborts FunId and retain the
    // exact main id returned by registration. Looking it back up by name
    // would alias an unrelated same-named user native.
    let mut fid_map: FidMap = BTreeMap::new();
    for (op, w) in &needs {
        let fid = ensure_main_fid(program, *op, *w);
        ensure_aborts_fid(program, *op, *w);
        fid_map.insert((*op, *w), fid);
    }

    // Pass 3: walk each function body again, replacing every BinOp
    // and Cast site with the Call. Skip the functions that already
    // failed at pass 1; rewrite would hit the same TypeOf failure.
    for fid in &target_fids {
        if failed.contains(fid) {
            continue;
        }
        if let Err(err) = rewrite_function(program, *fid, &fid_map) {
            failures.push(Stage10FunctionFailure {
                function: *fid,
                phase: Stage10RewritePhase::Rewrite,
                err,
            });
        }
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(Stage10Error::FunctionFailures(failures))
    }
}

// ---------------------------------------------------------------------------
// Pass 1 -- collect needs
// ---------------------------------------------------------------------------

fn collect_needs_function(
    program: &Program,
    fid: FunId,
    needs: &mut BTreeSet<(Op, u32)>,
) -> Result<(), TypeOfError> {
    let f = &program.functions[&fid];
    let scope = build_param_scope(f);
    let mut collector = NeedsCollector { needs, program };
    walk_typed_block(&mut collector, &f.body, scope, program)
}

/// Records the `(Op, src_width)` registration need for every UInt
/// `BinOp` / `Cast` / `BitNot` site.
struct NeedsCollector<'a> {
    needs: &'a mut BTreeSet<(Op, u32)>,
    program: &'a Program,
}

impl TypedScopeVisitor for NeedsCollector<'_> {
    type Error = TypeOfError;

    fn visit_expr(&mut self, e: &Expr, scope: &TypedScope) -> Result<(), TypeOfError> {
        match e {
            Expr::BinOp { op, lhs, rhs } => {
                // Only rewrite when the lhs is UInt(N). Logical And/Or
                // operate on Bool and pass through.
                if let Some(src_w) = uint_width(&type_of(lhs, scope, self.program)?) {
                    if let Some(op_kind) = binop_to_op(*op, &type_of(rhs, scope, self.program)?)? {
                        self.needs.insert((op_kind, src_w));
                    }
                }
            }
            Expr::UnOp { op, operand } => {
                if let UnOp::Cast(dst) = op {
                    if let Some(src_w) = uint_width(&type_of(operand, scope, self.program)?) {
                        self.needs.insert((Op::Cast { dst: *dst }, src_w));
                    }
                }
                if let UnOp::BitNot = op {
                    if let Some(src_w) = uint_width(&type_of(operand, scope, self.program)?) {
                        self.needs.insert((Op::BitNot, src_w));
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Pass 4 -- rewrite
// ---------------------------------------------------------------------------

fn rewrite_function(program: &mut Program, fid: FunId, map: &FidMap) -> Result<(), TypeOfError> {
    let scope = build_param_scope(&program.functions[&fid]);
    let mut body = program.functions[&fid].body.clone();
    {
        let program_ref: &Program = program;
        let mut rewriter = Rewriter {
            map,
            program: program_ref,
        };
        walk_typed_block_mut(&mut rewriter, &mut body, scope, program_ref)?;
    }
    program.functions.get_mut(&fid).unwrap().body = body;
    Ok(())
}

/// Replaces every UInt `BinOp` / `Cast` / `BitNot` site with a `Call`
/// against the registered BoundedU FunId. Runs post-order, so nested
/// arithmetic like `(a + b) * c` sees the inner `Add`-turned-`Call`
/// (which returns UInt(N) per the registered signature) and still
/// fires the outer multiplication.
struct Rewriter<'a> {
    map: &'a FidMap,
    program: &'a Program,
}

impl TypedScopeMutVisitor for Rewriter<'_> {
    type Error = TypeOfError;

    fn visit_expr_mut(&mut self, e: &mut Expr, scope: &TypedScope) -> Result<(), TypeOfError> {
        match e {
            Expr::BinOp { op, lhs, rhs } => {
                let lhs_ty = type_of(lhs, scope, self.program)?;
                let src_w = match uint_width(&lhs_ty) {
                    Some(w) => w,
                    None => return Ok(()), // Bool And/Or, or non-numeric -- pass through.
                };
                let rhs_ty = type_of(rhs, scope, self.program)?;
                let op_kind = match binop_to_op(*op, &rhs_ty)? {
                    Some(o) => o,
                    None => return Ok(()), // Not a UInt-flavoured BinOp.
                };
                let fid = *map_get(self.map, op_kind, src_w);
                let lhs_taken = std::mem::replace(&mut **lhs, Expr::Unit);
                let rhs_taken = std::mem::replace(&mut **rhs, Expr::Unit);
                *e = Expr::Call {
                    fun: fid,
                    type_args: Vec::new(),
                    args: vec![lhs_taken, rhs_taken],
                };
            }
            Expr::UnOp { op, operand } => match op {
                UnOp::Cast(dst) => {
                    let operand_ty = type_of(operand, scope, self.program)?;
                    if let Some(src_w) = uint_width(&operand_ty) {
                        let fid = *map_get(self.map, Op::Cast { dst: *dst }, src_w);
                        let operand_taken = std::mem::replace(&mut **operand, Expr::Unit);
                        *e = Expr::Call {
                            fun: fid,
                            type_args: Vec::new(),
                            args: vec![operand_taken],
                        };
                    }
                }
                UnOp::BitNot => {
                    let operand_ty = type_of(operand, scope, self.program)?;
                    if let Some(src_w) = uint_width(&operand_ty) {
                        let fid = *map_get(self.map, Op::BitNot, src_w);
                        let operand_taken = std::mem::replace(&mut **operand, Expr::Unit);
                        *e = Expr::Call {
                            fun: fid,
                            type_args: Vec::new(),
                            args: vec![operand_taken],
                        };
                    }
                }
                UnOp::Not => {} // Bool only, leave alone.
            },
            _ => {}
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn build_param_scope(f: &crate::ir::Function) -> Scope {
    f.signature
        .params
        .iter()
        .map(|p| (p.var.clone(), p.ty.clone()))
        .collect()
}

fn map_get(map: &FidMap, op: Op, src_w: u32) -> &FunId {
    map.get(&(op, src_w)).expect("registered in pass 2")
}

/// Returns `Some(N)` iff `ty` is `Type::UInt(N)`. Stage 10 only fires
/// on bare UInt operands -- references / mutable references to UInts
/// are left for stage 4 to strip first.
fn uint_width(ty: &Type) -> Option<u32> {
    match ty {
        Type::UInt(n) => Some(*n),
        _ => None,
    }
}

/// Translate a `BinOp` into stage-10's `Op` enum when the op is
/// in scope. Returns `Ok(None)` for `And`/`Or` on Bool. Shift ops
/// carry the rhs width from the inferred rhs type.
fn binop_to_op(op: BinOp, rhs_ty: &Type) -> Result<Option<Op>, TypeOfError> {
    Ok(Some(match op {
        BinOp::Add => Op::Add,
        BinOp::Sub => Op::Sub,
        BinOp::Mul => Op::Mul,
        BinOp::WrappingAdd => Op::WrappingAdd,
        BinOp::WrappingSub => Op::WrappingSub,
        BinOp::WrappingMul => Op::WrappingMul,
        BinOp::SAdd => Op::SAdd,
        BinOp::SSub => Op::SSub,
        BinOp::SMul => Op::SMul,
        BinOp::Div => Op::Div,
        BinOp::Mod => Op::Mod,
        BinOp::SDiv => Op::SDiv,
        BinOp::SMod => Op::SMod,
        BinOp::BitAnd => Op::BitAnd,
        BinOp::BitOr => Op::BitOr,
        BinOp::BitXor => Op::BitXor,
        BinOp::Shl => {
            let w = uint_width(rhs_ty).ok_or_else(|| TypeOfError::MalformedAccess {
                reason: "shift rhs not UInt".to_string(),
            })?;
            Op::Shl { rhs_width: w }
        }
        BinOp::Shr => {
            let w = uint_width(rhs_ty).ok_or_else(|| TypeOfError::MalformedAccess {
                reason: "shift rhs not UInt".to_string(),
            })?;
            Op::Shr { rhs_width: w }
        }
        BinOp::LShr => {
            let w = uint_width(rhs_ty).ok_or_else(|| TypeOfError::MalformedAccess {
                reason: "logical shift-right rhs not UInt".to_string(),
            })?;
            Op::LShr { rhs_width: w }
        }
        BinOp::AShr => {
            let w = uint_width(rhs_ty).ok_or_else(|| TypeOfError::MalformedAccess {
                reason: "arithmetic shift-right rhs not UInt".to_string(),
            })?;
            Op::AShr { rhs_width: w }
        }
        BinOp::Eq => Op::Eq,
        BinOp::Neq => Op::Neq,
        BinOp::Lt => Op::Lt,
        BinOp::Le => Op::Le,
        BinOp::Gt => Op::Gt,
        BinOp::Ge => Op::Ge,
        BinOp::SLt => Op::SLt,
        BinOp::SLe => Op::SLe,
        BinOp::SGt => Op::SGt,
        BinOp::SGe => Op::SGe,
        BinOp::And | BinOp::Or => return Ok(None),
    }))
}
