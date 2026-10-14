//! Single-use continuation inlining (interpreter-depth reduction).
//!
//! `return_lift` lifts inner returns by extracting `f.cont_N` (and nested
//! `cont_N.cont_M`) continuation functions, each tail-called from exactly
//! one site. The Lean *interpreter* (used by `sui-lean --test` via
//! `lake env lean --run`) performs no tail-call optimization, so a long
//! chain of single-use conts costs one interpreter stack frame per cont.
//! A deep test like cetus/ika `test_multiaddr` (18 asserts -> a ~60-deep
//! `.aborts` cont chain, each link evaluating a `validate_*` call with its
//! own lifted conts) then exceeds the interpreter's recursion limit and
//! reports an opaque code-2000 invariant violation.
//!
//! This pass inlines every single-use `Synthetic` continuation back into
//! its unique caller -- binding the cont's parameters to the call's
//! arguments with `let`s and splicing its body in place -- collapsing the
//! chains into flat `let`/`if` bodies. Semantics are identical; the
//! interpreter just sees far fewer frames. Single use means no code
//! duplication. Loop helpers are `FunctionKind::LoopBody`/`LoopAfter`
//! (never `Synthetic`), so loops are never inlined and recursion is not a
//! concern -- return_lift's `Synthetic` conts form a DAG.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::expr::{Block, BlockTail, Expr, Stmt};
use crate::ir::function::{FunctionKind, Param};
use crate::ir::ops::BitOp;
use crate::ir::quant::QuantDomain;
use crate::ir::visit::{walk_block_mut_default, walk_expr_default, MutVisitor, Visitor};
use crate::ir::{FunId, Program};

use super::Stage7Error;

/// Maximum IR-node size of a continuation we will inline. Small conts are
/// the per-iteration loop/control continuations whose chains drive the
/// interpreter's recursion depth -- inlining them is exactly the fix.
/// Large conts are whole-test composition tails (e.g. an `.aborts` body
/// that threads dozens of asserts); inlining those concentrates thousands
/// of nodes into one function and makes Lean's elaborator super-linear.
/// The observed ika_common size distribution has a clean gap between the
/// control conts (<= 57 nodes) and the composition tails (>= 110), so any
/// cap in that range inlines the former and leaves the latter as calls.
const SIZE_CAP: usize = 100;

pub fn run(program: &mut Program) -> Result<(), Stage7Error> {
    const MAX_ITER: usize = 64;
    for _iter in 0..MAX_ITER {
        let counts = count_calls(program);
        // Single-use Synthetic continuations under the size cap are candidates.
        let candidates: BTreeMap<FunId, (Vec<Param>, Block)> = program
            .functions
            .iter()
            .filter(|(id, f)| {
                matches!(f.kind, FunctionKind::Synthetic)
                    && counts.get(*id).copied().unwrap_or(0) == 1
                    && block_size(&f.body) <= SIZE_CAP
                    // A Return is scoped to the synthetic continuation's
                    // function boundary.  Splicing that body into a value
                    // position in its caller would turn it back into an
                    // illegal inner Return, undoing `return_lift`.
                    && !block_contains_return(&f.body)
            })
            .map(|(id, f)| (*id, (f.signature.params.clone(), f.body.clone())))
            .collect();
        if candidates.is_empty() {
            break;
        }
        let mut absorbed: BTreeMap<FunId, BTreeSet<FunId>> = BTreeMap::new();
        for (host, f) in program.functions.iter_mut() {
            let mut inliner = Inliner {
                cands: &candidates,
                host: *host,
                absorbed: &mut absorbed,
            };
            inliner.visit_block_mut(&mut f.body);
        }
        // Drop conts that are now unreferenced.
        let after = count_calls(program);
        let before_len = program.functions.len();
        program.functions.retain(|id, f| {
            !(matches!(f.kind, FunctionKind::Synthetic)
                && candidates.contains_key(id)
                && after.get(id).copied().unwrap_or(0) == 0)
        });
        if program.functions.len() == before_len {
            // Nothing was removed -> no progress; stop to avoid spinning.
            break;
        }
        repoint_inlined_loop_parents(program, &absorbed);
    }
    Ok(())
}

pub(super) fn prune_unreferenced_continuations(program: &mut Program) {
    loop {
        let calls = count_calls(program);
        let mut structural_roots = BTreeSet::new();
        for function in program.functions.values() {
            match function.kind {
                FunctionKind::Spec { target, .. } => {
                    structural_roots.insert(target);
                }
                FunctionKind::LoopBody { parent, .. } | FunctionKind::LoopAfter { parent, .. } => {
                    structural_roots.insert(parent);
                }
                FunctionKind::Theorem { target, source }
                | FunctionKind::Axiom { target, source, .. } => {
                    structural_roots.extend([target, source]);
                }
                _ => {}
            }
        }
        for (source, target) in &program.spec_to_impl {
            structural_roots.extend([*source, *target]);
        }
        for (source, (target, _)) in &program.trusted_spec_to_impl {
            structural_roots.extend([*source, *target]);
        }
        let before = program.functions.len();
        program.functions.retain(|id, function| {
            !matches!(function.kind, FunctionKind::Synthetic)
                || calls.get(id).copied().unwrap_or(0) != 0
                || structural_roots.contains(id)
        });
        if program.functions.len() == before {
            break;
        }
    }
}

// ---- Loop-parent repair ----

/// A `LoopBody`/`LoopAfter` names, in its `parent` field, the function
/// whose body held the `Expr::While` -- and an extracted labeled block's
/// `<f>.aborts.labeled_N` wrapper is exactly such a parent while being a
/// single-use `Synthetic`. Phase 3b.5b (`aborts_live_loop::
/// run_labeled_wrapper_loops`) rewrites the wrapper's host to TAIL-call
/// it, which is what makes it inlinable here; a chain whose consumption
/// stays a non-tail `let acc = wrapper(..)` is never inlined and keeps
/// its wrapper. Inlining moves the wrapper's `while_N` call into the
/// absorbing function, so THAT function becomes the loop's parent -- and
/// leaving the deleted id in place breaks the
/// `function-kind-references-resolve` invariant, which is held from
/// Baseline through Render.
///
/// The slot only pairs a `LoopBody` with its `LoopAfter` under one
/// parent, so a pair moving onto a parent that already owns that slot
/// (a host with a direct loop of its own plus a labeled-block loop) is
/// renumbered onto a free one, together.
///
/// Scoped to the wrappers THIS pass inlined. A parent that never
/// resolved and was not inlined here is a producer bug in
/// `loop_extract` -- the case `function-kind-references-resolve` was
/// written for -- and stays that invariant's to report.
fn repoint_inlined_loop_parents(
    program: &mut Program,
    absorbed: &BTreeMap<FunId, BTreeSet<FunId>>,
) {
    let mut used: BTreeMap<FunId, BTreeSet<u32>> = BTreeMap::new();
    let mut inlined_away: BTreeSet<(FunId, u32)> = BTreeSet::new();
    for f in program.functions.values() {
        let (Some(parent), Some(slot)) = (f.kind.loop_parent(), f.kind.loop_slot()) else {
            continue;
        };
        if program.functions.contains_key(&parent) {
            used.entry(parent).or_default().insert(slot);
        } else if absorbed.contains_key(&parent) {
            inlined_away.insert((parent, slot));
        }
    }
    if inlined_away.is_empty() {
        return;
    }
    let mut moves: BTreeMap<(FunId, u32), (FunId, u32)> = BTreeMap::new();
    for (old_parent, slot) in inlined_away {
        let new_parent = surviving_absorber(old_parent, absorbed, program);
        let taken = used.entry(new_parent).or_default();
        let new_slot = if taken.contains(&slot) {
            taken
                .iter()
                .next_back()
                .expect("slot set holds the collision")
                + 1
        } else {
            slot
        };
        taken.insert(new_slot);
        moves.insert((old_parent, slot), (new_parent, new_slot));
    }
    for f in program.functions.values_mut() {
        let (Some(parent), Some(slot)) = (f.kind.loop_parent(), f.kind.loop_slot()) else {
            continue;
        };
        let Some((new_parent, new_slot)) = moves.get(&(parent, slot)) else {
            continue;
        };
        f.kind = match f.kind {
            FunctionKind::LoopBody { .. } => FunctionKind::LoopBody {
                parent: *new_parent,
                slot: *new_slot,
            },
            FunctionKind::LoopAfter { .. } => FunctionKind::LoopAfter {
                parent: *new_parent,
                slot: *new_slot,
            },
            _ => panic!("loop_parent/loop_slot are only Some on loop helpers"),
        };
    }
}

/// The one surviving function holding the body of `start`. A cont whose
/// body was spliced into another cont in the same pass is itself
/// unreferenced and dropped, so the absorber chain is followed until it
/// reaches a function that survived.
fn surviving_absorber(
    start: FunId,
    absorbed: &BTreeMap<FunId, BTreeSet<FunId>>,
    program: &Program,
) -> FunId {
    let mut frontier = vec![start];
    let mut seen: BTreeSet<FunId> = BTreeSet::new();
    let mut found: BTreeSet<FunId> = BTreeSet::new();
    while let Some(fid) = frontier.pop() {
        if !seen.insert(fid) {
            continue;
        }
        let hosts = absorbed
            .get(&fid)
            .unwrap_or_else(|| panic!("inlined cont #{fid} recorded no absorbing function"));
        for host in hosts {
            if program.functions.contains_key(host) {
                found.insert(*host);
            } else {
                frontier.push(*host);
            }
        }
    }
    assert_eq!(
        found.len(),
        1,
        "inlined cont #{start} must land in exactly one surviving function, got {found:?}"
    );
    *found.iter().next().expect("checked non-empty")
}

// ---- Inlining ----

struct Inliner<'a> {
    cands: &'a BTreeMap<FunId, (Vec<Param>, Block)>,
    host: FunId,
    absorbed: &'a mut BTreeMap<FunId, BTreeSet<FunId>>,
}

impl MutVisitor for Inliner<'_> {
    fn visit_block_mut(&mut self, b: &mut Block) {
        // Collapse a chain of tail-position single-use cont calls in place.
        loop {
            let inline = matches!(
                &b.tail,
                BlockTail::Value(Expr::Call { fun, .. }) if self.cands.contains_key(fun)
            );
            if !inline {
                break;
            }
            let (fun, args) = match std::mem::replace(&mut b.tail, BlockTail::Value(Expr::Unit)) {
                BlockTail::Value(Expr::Call { fun, args, .. }) => (fun, args),
                _ => unreachable!(),
            };
            let (params, body) = self.cands.get(&fun).cloned().expect("candidate present");
            self.absorbed.entry(fun).or_default().insert(self.host);
            // Bind each param to the corresponding arg, then splice the body.
            for (p, a) in params.into_iter().zip(args.into_iter()) {
                // Skip a no-op self-rebind. return_lift names a cont's
                // params after the captured vars it forwards, so an
                // un-renamed capture arrives here as `let v = Var(v)`.
                // Emitting it would just be an identity Let for a later
                // pass to clean up; drop it at the source instead.
                if matches!(&a, Expr::Var(w) if *w == p.var) {
                    continue;
                }
                b.stmts.push(Stmt::Let {
                    pattern: vec![Some(p.var)],
                    value: a,
                });
            }
            b.stmts.extend(body.stmts);
            b.tail = body.tail;
        }
        // Recurse into stmt sub-expressions and the (now-final) tail.
        walk_block_mut_default(self, b);
    }
}

// ---- Call counting ----

fn count_calls(program: &Program) -> BTreeMap<FunId, usize> {
    let mut counter = CallCounter {
        counts: BTreeMap::new(),
    };
    for f in program.functions.values() {
        counter.visit_block(&f.body);
    }
    counter.counts
}

struct CallCounter {
    counts: BTreeMap<FunId, usize>,
}

impl Visitor for CallCounter {
    fn visit_expr(&mut self, e: &Expr) {
        if let Expr::Call { fun, .. } = e {
            *self.counts.entry(*fun).or_insert(0) += 1;
        }
        walk_expr_default(self, e);
    }
}

// ---- Size estimation (IR node count) ----

fn block_size(b: &Block) -> usize {
    let mut n = 1;
    for s in &b.stmts {
        n += match s {
            Stmt::Let { value, .. } => 1 + expr_size(value),
            Stmt::Eval(e) => 1 + expr_size(e),
        };
    }
    n += tail_size(&b.tail);
    n
}

pub(super) fn block_contains_return(b: &Block) -> bool {
    b.stmts.iter().any(|s| match s {
        Stmt::Let { value, .. } | Stmt::Eval(value) => expr_contains_return(value),
    }) || match &b.tail {
        BlockTail::Return(_) => true,
        BlockTail::Value(value) => expr_contains_return(value),
        BlockTail::Abort { code: value }
        | BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::ReturnFromBlock { value, .. } => expr_contains_return(value),
    }
}

fn expr_contains_return(e: &Expr) -> bool {
    match e {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            expr_contains_return(cond)
                || block_contains_return(then_branch)
                || block_contains_return(else_branch)
        }
        Expr::Match {
            selector, cases, ..
        } => {
            expr_contains_return(selector)
                || cases.iter().any(|arm| block_contains_return(&arm.body))
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            ..
        } => {
            iter_locals
                .iter()
                .any(|(_, init)| expr_contains_return(init))
                || block_contains_return(header)
                || expr_contains_return(cond)
                || block_contains_return(body)
        }
        Expr::Quantifier { domain, body, .. } => {
            let domain_has_return = match domain {
                QuantDomain::Unbounded => false,
                QuantDomain::Range { start, end } => {
                    expr_contains_return(start) || expr_contains_return(end)
                }
                QuantDomain::VecRange { vec, start, end } => {
                    expr_contains_return(vec)
                        || expr_contains_return(start)
                        || expr_contains_return(end)
                }
                QuantDomain::Collection(collection) => expr_contains_return(collection),
            };
            domain_has_return || block_contains_return(body)
        }
        Expr::LabeledBlock { body, .. } => block_contains_return(body),
        Expr::BinOp { lhs, rhs, .. } => expr_contains_return(lhs) || expr_contains_return(rhs),
        Expr::UnOp { operand, .. } => expr_contains_return(operand),
        Expr::BitOp(op) => match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => expr_contains_return(operand),
            BitOp::Concat { high, low } => expr_contains_return(high) || expr_contains_return(low),
        },
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            args.iter().any(expr_contains_return)
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => expr_contains_return(value),
        Expr::WriteRef { reference, value } => {
            expr_contains_return(reference) || expr_contains_return(value)
        }
        Expr::Borrow { step, base } => {
            step.exprs().any(expr_contains_return) || expr_contains_return(base)
        }
        Expr::Update { step, base, value } => {
            step.exprs().any(expr_contains_return)
                || expr_contains_return(base)
                || expr_contains_return(value)
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => false,
    }
}

fn tail_size(t: &BlockTail) -> usize {
    match t {
        BlockTail::Value(e) => expr_size(e),
        BlockTail::Abort { code } => 1 + expr_size(code),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => 1 + expr_size(value),
    }
}

fn expr_size(e: &Expr) -> usize {
    1 + match e {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => expr_size(cond) + block_size(then_branch) + block_size(else_branch),
        Expr::Match {
            selector, cases, ..
        } => expr_size(selector) + cases.iter().map(|a| block_size(&a.body)).sum::<usize>(),
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            ..
        } => {
            iter_locals.iter().map(|(_, i)| expr_size(i)).sum::<usize>()
                + block_size(header)
                + expr_size(cond)
                + block_size(body)
        }
        Expr::Quantifier { domain, body, .. } => {
            let d = match domain {
                QuantDomain::Unbounded => 0,
                QuantDomain::Range { start, end } => expr_size(start) + expr_size(end),
                QuantDomain::VecRange { vec, start, end } => {
                    expr_size(vec) + expr_size(start) + expr_size(end)
                }
                QuantDomain::Collection(c) => expr_size(c),
            };
            d + block_size(body)
        }
        Expr::LabeledBlock { body, .. } => block_size(body),
        Expr::BinOp { lhs, rhs, .. } => expr_size(lhs) + expr_size(rhs),
        Expr::UnOp { operand, .. } => expr_size(operand),
        Expr::BitOp(op) => bitop_size(op),
        Expr::Call { args, .. } | Expr::Tuple(args) | Expr::Pack { fields: args, .. } => {
            args.iter().map(expr_size).sum()
        }
        Expr::Unpack { value, .. }
        | Expr::Field { base: value, .. }
        | Expr::ReadRef(value)
        | Expr::ToProp(value)
        | Expr::ToBool(value) => expr_size(value),
        Expr::WriteRef { reference, value } => expr_size(reference) + expr_size(value),
        Expr::Borrow { step, base } => step.exprs().map(expr_size).sum::<usize>() + expr_size(base),
        Expr::Update { step, base, value } => {
            step.exprs().map(expr_size).sum::<usize>() + expr_size(base) + expr_size(value)
        }
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => 0,
    }
}

fn bitop_size(op: &BitOp) -> usize {
    match op {
        BitOp::Extract { operand, .. }
        | BitOp::ZeroExtend { operand, .. }
        | BitOp::SignExtend { operand, .. } => expr_size(operand),
        BitOp::Concat { high, low } => expr_size(high) + expr_size(low),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::builder::{binop, call, eval, just, lit_bool, lit_u64, var};
    use crate::ir::function::{Function, Signature};
    use crate::ir::ops::BinOp;
    use crate::ir::{Module, Type};

    fn module() -> Module {
        Module {
            name: String::new(),
            package_name: String::new(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        }
    }

    fn func(name: &str, kind: FunctionKind, params: Vec<Param>, body: Block) -> Function {
        Function {
            module: 0,
            name: name.to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params,
                return_type: Type::UInt(64),
            },
            body,
            kind,
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
        }
    }

    fn u64_param(name: &str) -> Param {
        Param {
            name: name.to_string(),
            var: name.into(),
            ty: Type::UInt(64),
        }
    }

    fn calls_to(program: &Program, fid: FunId) -> usize {
        count_calls(program).get(&fid).copied().unwrap_or(0)
    }

    #[test]
    fn orphan_continuation_chains_are_removed_but_loop_parents_are_retained() {
        let mut p = Program::default();
        p.modules.insert(0, module());
        p.functions.insert(
            1,
            func("main", FunctionKind::Source, vec![], just(lit_u64(0))),
        );
        p.functions.insert(
            2,
            func(
                "orphan",
                FunctionKind::Synthetic,
                vec![],
                just(call(3, vec![])),
            ),
        );
        p.functions.insert(
            3,
            func(
                "orphan.cont",
                FunctionKind::Synthetic,
                vec![],
                just(lit_u64(0)),
            ),
        );
        p.functions.insert(
            4,
            func(
                "loop.parent",
                FunctionKind::Synthetic,
                vec![],
                just(lit_u64(0)),
            ),
        );
        p.functions.insert(
            5,
            func(
                "loop.body",
                FunctionKind::LoopBody { parent: 4, slot: 0 },
                vec![],
                just(lit_u64(0)),
            ),
        );

        prune_unreferenced_continuations(&mut p);

        assert_eq!(
            p.functions.keys().copied().collect::<Vec<_>>(),
            vec![1, 4, 5]
        );
    }

    /// A single-use `Synthetic` cont is inlined into its unique caller
    /// (params bound by `let`, body spliced into the tail) and then
    /// dropped.
    #[test]
    fn single_use_synthetic_cont_is_inlined_and_dropped() {
        let mut p = Program::default();
        p.modules.insert(0, module());
        // main(): cont(a)   |   main.cont_0(p) := p + 1   [Synthetic, 1 use]
        p.functions.insert(
            1,
            func(
                "main",
                FunctionKind::Source,
                vec![],
                just(call(2, vec![var("a")])),
            ),
        );
        p.functions.insert(
            2,
            func(
                "main.cont_0",
                FunctionKind::Synthetic,
                vec![u64_param("p")],
                just(binop(BinOp::Add, var("p"), lit_u64(1))),
            ),
        );

        run(&mut p).unwrap();

        assert!(
            !p.functions.contains_key(&2),
            "single-use cont must be dropped"
        );
        assert_eq!(calls_to(&p, 2), 0, "no call to the inlined cont remains");
        let main = &p.functions[&1];
        assert!(
            matches!(main.body.tail, BlockTail::Value(Expr::BinOp { .. })),
            "cont body spliced into main's tail: {:?}",
            main.body.tail
        );
        assert!(
            main.body
                .stmts
                .iter()
                .any(|s| matches!(s, Stmt::Let { .. })),
            "cont param bound by a let"
        );
    }

    /// A multi-use `Synthetic` cont (inlining it would duplicate code) and
    /// a single-use loop helper (`LoopBody`, not `Synthetic`) are both left
    /// alone.
    #[test]
    fn multi_use_and_loop_helpers_are_not_inlined() {
        let mut p = Program::default();
        p.modules.insert(0, module());
        // caller(): { cont2(a); cont2(b) }  -- 2 uses of Synthetic cont2(4)
        p.functions.insert(
            3,
            func(
                "caller",
                FunctionKind::Source,
                vec![],
                Block {
                    stmts: vec![eval(call(4, vec![var("a")]))],
                    tail: BlockTail::Value(call(4, vec![var("b")])),
                },
            ),
        );
        p.functions.insert(
            4,
            func(
                "cont2",
                FunctionKind::Synthetic,
                vec![u64_param("p")],
                just(var("p")),
            ),
        );
        // loop_caller(): f.while_0(a)  -- 1 use, but LoopBody (not Synthetic)
        p.functions.insert(
            6,
            func(
                "loop_caller",
                FunctionKind::Source,
                vec![],
                just(call(5, vec![var("a")])),
            ),
        );
        p.functions.insert(
            5,
            func(
                "f.while_0",
                FunctionKind::LoopBody { parent: 6, slot: 0 },
                vec![u64_param("p")],
                just(var("p")),
            ),
        );

        run(&mut p).unwrap();

        assert!(
            p.functions.contains_key(&4),
            "multi-use Synthetic cont stays"
        );
        assert_eq!(
            calls_to(&p, 4),
            2,
            "both calls to the multi-use cont remain"
        );
        assert!(
            p.functions.contains_key(&5),
            "loop helper (LoopBody) is never inlined"
        );
        assert_eq!(calls_to(&p, 5), 1, "call to the loop helper remains");
    }

    /// Inlining a continuation that still owns a nested function Return
    /// would move that Return into the caller's value expression.  That
    /// recreates the exact shape `return_lift` removed and violates the
    /// stage-7 postcondition, so the continuation remains a call boundary.
    #[test]
    fn return_bearing_synthetic_cont_is_not_inlined() {
        let mut p = Program::default();
        p.modules.insert(0, module());
        p.functions.insert(
            1,
            func(
                "caller",
                FunctionKind::Source,
                vec![],
                just(call(2, vec![var("a")])),
            ),
        );
        p.functions.insert(
            2,
            func(
                "caller.cont_0",
                FunctionKind::Synthetic,
                vec![u64_param("p")],
                just(Expr::If {
                    cond: Box::new(lit_bool(true)),
                    then_branch: Box::new(Block {
                        stmts: vec![],
                        tail: BlockTail::Return(Box::new(var("p"))),
                    }),
                    else_branch: Box::new(just(var("p"))),
                }),
            ),
        );

        run(&mut p).unwrap();

        assert!(p.functions.contains_key(&2));
        assert_eq!(calls_to(&p, 2), 1);
    }

    /// `<f>.aborts.labeled_N` wrapper (Synthetic, single-use, tail-called)
    /// plus the `LoopBody`/`LoopAfter` pair that names it as `parent`.
    fn labeled_wrapper_chain(
        p: &mut Program,
        wrapper: FunId,
        body: FunId,
        after: FunId,
        slot: u32,
    ) {
        p.functions.insert(
            wrapper,
            func(
                "f.aborts.labeled_0",
                FunctionKind::Synthetic,
                vec![u64_param("i")],
                just(call(body, vec![var("i")])),
            ),
        );
        p.functions.insert(
            body,
            func(
                "f.aborts.labeled_0.while_0",
                FunctionKind::LoopBody {
                    parent: wrapper,
                    slot,
                },
                vec![u64_param("i")],
                just(call(after, vec![var("i")])),
            ),
        );
        p.functions.insert(
            after,
            func(
                "f.aborts.labeled_0.while_0.after",
                FunctionKind::LoopAfter {
                    parent: wrapper,
                    slot,
                },
                vec![u64_param("i")],
                just(var("i")),
            ),
        );
    }

    /// Phase 3b.5b makes the host tail-call the labeled-block wrapper, so
    /// the wrapper -- a single-use Synthetic that the loop chain names as
    /// its `parent` -- is inlined and dropped here. The pair must follow
    /// the body into the absorbing host, or `LoopBody.parent` dangles and
    /// `function-kind-references-resolve` fails at every later stage.
    #[test]
    fn inlined_wrapper_hands_its_loop_parentage_to_the_host() {
        let mut p = Program::default();
        p.modules.insert(0, module());
        p.functions.insert(
            1,
            func(
                "f.aborts",
                FunctionKind::Source,
                vec![],
                just(call(2, vec![var("a")])),
            ),
        );
        labeled_wrapper_chain(&mut p, 2, 3, 4, 0);

        run(&mut p).unwrap();

        assert!(!p.functions.contains_key(&2), "the wrapper is inlined");
        for fid in [3, 4] {
            assert_eq!(
                p.functions[&fid].kind.loop_parent(),
                Some(1),
                "helper #{fid} follows the wrapper's body into the host"
            );
            assert_eq!(p.functions[&fid].kind.loop_slot(), Some(0));
        }
    }

    /// A host that already owns slot 0 through a loop of its own: the
    /// re-parented pair moves onto a free slot, and both halves move
    /// together so the pairing survives.
    #[test]
    fn repointed_pair_takes_a_free_slot_when_the_host_owns_that_one() {
        let mut p = Program::default();
        p.modules.insert(0, module());
        p.functions.insert(
            1,
            func(
                "f.aborts",
                FunctionKind::Source,
                vec![],
                Block {
                    stmts: vec![eval(call(5, vec![var("a")]))],
                    tail: BlockTail::Value(call(2, vec![var("a")])),
                },
            ),
        );
        labeled_wrapper_chain(&mut p, 2, 3, 4, 0);
        p.functions.insert(
            5,
            func(
                "f.aborts.while_0",
                FunctionKind::LoopBody { parent: 1, slot: 0 },
                vec![u64_param("i")],
                just(call(6, vec![var("i")])),
            ),
        );
        p.functions.insert(
            6,
            func(
                "f.aborts.while_0.after",
                FunctionKind::LoopAfter { parent: 1, slot: 0 },
                vec![u64_param("i")],
                just(var("i")),
            ),
        );

        run(&mut p).unwrap();

        let moved = p.functions[&3].kind.loop_slot().expect("LoopBody slot");
        assert_ne!(moved, 0, "slot 0 under the host is taken by its own loop");
        assert_eq!(
            p.functions[&4].kind.loop_slot(),
            Some(moved),
            "the LoopAfter moves onto the same slot as its LoopBody"
        );
        for fid in [3, 4] {
            assert_eq!(p.functions[&fid].kind.loop_parent(), Some(1));
        }
        for fid in [5, 6] {
            assert_eq!(p.functions[&fid].kind.loop_parent(), Some(1));
            assert_eq!(p.functions[&fid].kind.loop_slot(), Some(0));
        }
    }

    /// The absorber may itself be a cont that is inlined away in the same
    /// pass; the chain is followed to the function that survives.
    #[test]
    fn repointing_follows_a_chain_of_inlined_conts() {
        let mut p = Program::default();
        p.modules.insert(0, module());
        p.functions.insert(
            1,
            func(
                "f.aborts",
                FunctionKind::Source,
                vec![],
                just(call(7, vec![var("a")])),
            ),
        );
        p.functions.insert(
            7,
            func(
                "f.aborts.cont_0",
                FunctionKind::Synthetic,
                vec![u64_param("i")],
                just(call(2, vec![var("i")])),
            ),
        );
        labeled_wrapper_chain(&mut p, 2, 3, 4, 0);

        run(&mut p).unwrap();

        assert!(!p.functions.contains_key(&2));
        assert!(!p.functions.contains_key(&7));
        for fid in [3, 4] {
            assert_eq!(p.functions[&fid].kind.loop_parent(), Some(1));
        }
    }
}
