// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Nested-loop termination threading.
//!
//! The legacy backend lowers a Move `while` whose body contains a second
//! `while` into a three-member mutual block:
//!
//!   `<base>.while_0`        outer forward counter `i`, guard `i < n`, calls `while_1`
//!   `<base>.while_1`        inner counter, self-recurses, else-calls `while_1.after`
//!   `<base>.while_1.after`  steps `i := i + 1`, re-enters `while_0`
//!
//! A purely-local single-counter measure cannot discharge the
//! `while_1.after -> while_0(i+1)` back-edge: `while_1.after` has no loop guard
//! in scope, so `i + 1` could wrap mod 2^64 and the outer measure `n - i` need
//! not decrease. The fix threads the outer guard `i < n` as a loop-invariant
//! hypothesis (`hinv`) onto `while_1` and `while_1.after`, putting `i < n` in
//! scope at the back-edge so omega closes it.
//!
//! This pass detects the exact three-member shape, registers an `hinv` proof
//! parameter on `while_1` and `while_1.after` (via [`Program::loop_inv_hyps`],
//! making them loop-inv helpers the renderer already knows how to handle), marks
//! the base in [`Program::loop_invariants`] (so the renderer emits the
//! user-measure + decreasing-macro form for every member), and rewrites the
//! inter-member calls so the hypothesis is supplied at the `while_0 -> while_1`
//! entry (from the guard) and forwarded across the inner recursion. The
//! lexicographic measure + decreasing proof live in a hand-written
//! `Termination/<Module>.lean`.
//!
//! Conservative by construction: anything that does not match the exact shape is
//! left untouched (`termination_by (0 : Nat)` / `decreasing_by all_goals sorry`).

use crate::data::ir::IRNode;
use crate::{BinOp, FunctionID, LoopInvHyp, Program};

struct NestedShape {
    base: String,
    w0_id: FunctionID,
    w1_id: FunctionID,
    after_id: FunctionID,
}

pub fn thread_nested_loop_termination(program: &mut Program) {
    let shapes = detect_shapes(program);
    for shape in shapes {
        // Only thread the nested-loop hypotheses when the client hand-wrote the
        // matching `def <base>.while_1.loop_hyp` in `sources/lean/`. Otherwise the
        // injected `hinv` / `termination_by <member>.termination` references point
        // at undefined identifiers (the `Unknown identifier <f>.while_1.loop_hyp`
        // + `unknown tactic` cluster); the loop instead falls back to the
        // transparent `termination_by (0 : Nat)` / `decreasing_by all_goals sorry`
        // form. Mirrors the single-loop gate in `program_builder`.
        let w1_stem = format!("{}.while_1", shape.base);
        if !program.lean_termination_decls.loop_hyp.contains(&w1_stem) {
            continue;
        }

        // `hinv` on while_1 and while_1.after only. while_0's own outgoing edge
        // (`while_0 -> while_1`) just drops the phase and needs no guard, so
        // while_0 carries no hypothesis.
        for (id, member) in [(shape.w1_id, "while_1"), (shape.after_id, "while_1.after")] {
            program.loop_inv_hyps.insert(
                id,
                LoopInvHyp {
                    hyp_param: "hinv".to_string(),
                    hook_name: format!("{}.{}.loop_hyp", shape.base, member),
                },
            );
        }

        // Register the base so the renderer emits `termination_by
        // <member>.termination` + the decreasing macro for every member instead
        // of the sorry fallback. The recorded id is a placeholder (no Move-level
        // invariant predicate backs this synthetic registration).
        program
            .loop_invariants
            .entry(shape.base.clone())
            .or_insert(shape.w0_id);

        rewrite_calls(program, &shape);
    }
}

fn rewrite_calls(program: &mut Program, shape: &NestedShape) {
    let (w0_id, w1_id, after_id) = (shape.w0_id, shape.w1_id, shape.after_id);

    // while_0 -> while_1: supply the hypothesis from the in-scope guard. The
    // renderer turns a trailing `Abort` arg to a loop-inv helper into the
    // dependent-`if h : i < n` + entry `by`-macro.
    let w0_body = std::mem::replace(&mut program.functions.get_mut(w0_id).body, IRNode::unit());
    program.functions.get_mut(w0_id).body =
        append_proof_arg(w0_body, &|f| f == w1_id, ProofArg::Entry);

    // while_1 -> while_1 (self) and while_1 -> while_1.after: forward `hinv`.
    let w1_body = std::mem::replace(&mut program.functions.get_mut(w1_id).body, IRNode::unit());
    program.functions.get_mut(w1_id).body =
        append_proof_arg(w1_body, &|f| f == w1_id || f == after_id, ProofArg::Forward);

    // while_1.after -> while_0 carries no hypothesis (while_0 has no `hinv`).
}

enum ProofArg {
    Entry,
    Forward,
}

fn append_proof_arg(body: IRNode, pred: &dyn Fn(FunctionID) -> bool, kind: ProofArg) -> IRNode {
    body.map(&mut |node| match node {
        IRNode::Call {
            function,
            type_args,
            mut args,
        } if pred(function) => {
            let already = match kind {
                ProofArg::Entry => matches!(args.last(), Some(IRNode::Abort { .. })),
                ProofArg::Forward => {
                    matches!(args.last(), Some(IRNode::Var(v)) if v.as_ref() == "hinv")
                }
            };
            if !already {
                match kind {
                    ProofArg::Entry => args.push(IRNode::Abort { code: None }),
                    ProofArg::Forward => args.push(IRNode::Var("hinv".into())),
                }
            }
            IRNode::Call {
                function,
                type_args,
                args,
            }
        }
        other => other,
    })
}

fn detect_shapes(program: &Program) -> Vec<NestedShape> {
    use std::collections::BTreeMap;
    let mut groups: BTreeMap<usize, Vec<(FunctionID, String)>> = BTreeMap::new();
    for (id, f) in program.functions.iter() {
        if let Some(gid) = f.mutual_group_id {
            if !f.name.ends_with(".aborts") {
                groups.entry(gid).or_default().push((id, f.name.clone()));
            }
        }
    }

    let mut shapes = Vec::new();
    for (_gid, members) in groups {
        if members.len() != 3 {
            continue;
        }
        let after = match members.iter().find(|(_, n)| n.ends_with(".while_1.after")) {
            Some(m) => m.clone(),
            None => continue,
        };
        let w1 = match members
            .iter()
            .find(|(_, n)| n.ends_with(".while_1") && !n.ends_with(".after"))
        {
            Some(m) => m.clone(),
            None => continue,
        };
        let w0 = match members
            .iter()
            .find(|(_, n)| n.ends_with(".while_0") && !n.ends_with(".after"))
        {
            Some(m) => m.clone(),
            None => continue,
        };

        let base = match w0.1.strip_suffix(".while_0") {
            Some(b) => b.to_string(),
            None => continue,
        };
        if w1.1 != format!("{}.while_1", base) || after.1 != format!("{}.while_1.after", base) {
            continue;
        }

        let w0_calls: Vec<FunctionID> = program.functions.get(&w0.0).body.calls().collect();
        let w1_calls: Vec<FunctionID> = program.functions.get(&w1.0).body.calls().collect();
        let after_calls: Vec<FunctionID> = program.functions.get(&after.0).body.calls().collect();

        let w0_ok = w0_calls.contains(&w1.0) && !w0_calls.contains(&after.0);
        let w1_ok = w1_calls.contains(&w1.0) && w1_calls.contains(&after.0);
        let after_ok = after_calls.contains(&w0.0);
        if !(w0_ok && w1_ok && after_ok) {
            continue;
        }

        // Require while_0's guard to be a `Lt(Var, Var)` forward OUTER counter
        // check. The INNER guard (in `while_1`) may be forward (`j < n`,
        // `j + 1`) or backward (`j > 0`, `j - 1`); both are handled by the
        // lexicographic measure the client provides in `Termination/`. (The
        // backward-inner variant additionally relies on a `Prod.Lex` tuple
        // measure rather than a flat-Nat one, so the Lean *kernel* never
        // reduces the huge `2^64` literals a flat measure would carry when a
        // heavy importer like `validator_set::advance_epoch` transitively
        // reduces through it.)
        if extract_lt_guard(&program.functions.get(&w0.0).body).is_none() {
            continue;
        }

        shapes.push(NestedShape {
            base,
            w0_id: w0.0,
            w1_id: w1.0,
            after_id: after.0,
        });
    }
    shapes
}

/// Peel `Let`s to the first `If`, follow a let-bound guard temp, and return the
/// resolved (bool-unwrapped) guard expression.
fn first_guard(body: &IRNode) -> Option<&IRNode> {
    use std::collections::HashMap;
    let mut bindings: HashMap<String, &IRNode> = HashMap::new();
    let mut node = body;
    let cond = loop {
        match node {
            IRNode::Let {
                pattern,
                value,
                body,
            } => {
                if pattern.len() == 1 {
                    bindings.insert(pattern[0].to_string(), value.as_ref());
                }
                node = body;
            }
            IRNode::If { cond, .. } => break cond.as_ref(),
            _ => return None,
        }
    };
    let mut g = peel_bool(cond);
    if let IRNode::Var(v) = g {
        if let Some(b) = bindings.get(v.as_ref()) {
            g = peel_bool(b);
        }
    }
    Some(g)
}

fn extract_lt_guard(body: &IRNode) -> Option<(String, String)> {
    if let Some(IRNode::BinOp {
        op: BinOp::Lt,
        lhs,
        rhs,
    }) = first_guard(body)
    {
        if let (IRNode::Var(i), IRNode::Var(n)) = (lhs.as_ref(), rhs.as_ref()) {
            return Some((i.to_string(), n.to_string()));
        }
    }
    None
}

fn peel_bool(node: &IRNode) -> &IRNode {
    let mut n = node;
    while let IRNode::ToBool(inner) = n {
        n = inner;
    }
    n
}
