//! Loop fixtures.

use super::super::Termination;
use super::root_of;
use super::BytecodeBuilder;
use super::Region;

/// Simple `while (cond) { nop }; ret`. Header carries `label + load`,
/// cond_at points at the deciding Branch, body is a Basic for the body
/// content. The implicit innermost-continue (back-edge into the header)
/// is recorded as the natural tail -- no `Term(Continue)` emitted.
#[test]
fn simple_while() {
    // PC 0: label "head"
    // PC 1: load_bool 0, true
    // PC 2: branch 0 -> "body" / "exit"
    // PC 3: label "body"
    // PC 4: nop
    // PC 5: jump "head"
    // PC 6: label "exit"
    // PC 7: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "body", "exit")
            .label("body")
            .nop()
            .jump("head")
            .label("exit")
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    assert_eq!(parts.len(), 3);
    let (header, cond_at, body) = match &parts[0] {
        Region::While {
            header,
            cond_at,
            body,
            ..
        } => (header.as_ref(), *cond_at, body.as_ref()),
        other => panic!("expected While, got {other:?}"),
    };
    assert_eq!(cond_at, 2);
    assert!(matches!(*header, Region::Basic { lower: 0, upper: 1 }));
    assert!(matches!(*body, Region::Basic { lower: 3, upper: 4 }));
    // Tail: Basic for the exit label + the Ret.
    assert!(matches!(parts[1], Region::Basic { lower: 6, upper: 6 }));
    assert!(matches!(
        parts[2],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
}

/// `while (cond) {}; ret` -- header-only loop. Body collapses to
/// `Seq(vec![])`, the canonical empty region.
#[test]
fn header_only_while() {
    // PC 0: label "head"
    // PC 1: load_bool 0, true
    // PC 2: branch 0 -> "head" / "exit"
    // PC 3: label "exit"
    // PC 4: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "head", "exit")
            .label("exit")
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    assert_eq!(parts.len(), 3);
    let body = match &parts[0] {
        Region::While { body, .. } => body.as_ref(),
        other => panic!("expected While, got {other:?}"),
    };
    assert!(matches!(body, Region::Seq(v) if v.is_empty()));
}

/// `while (true) { nop }` -- the deciding Branch always takes the body
/// arm, but our structurer doesn't constant-fold; as long as one arm
/// stays in `loop_body` and the other leaves, it's a well-formed loop.
/// This fixture confirms the structurer doesn't trip when the exit-arm
/// label goes straight to the function exit (DUMMY).
#[test]
fn while_with_immediate_return_after_loop() {
    // PC 0: label "head"
    // PC 1: load_bool 0, true
    // PC 2: branch 0 -> "body" / "exit"
    // PC 3: label "body"
    // PC 4: nop
    // PC 5: jump "head"
    // PC 6: label "exit"
    // PC 7: ret []
    //
    // (Identical structurally to `simple_while`; this fixture is a
    // sanity check that the exit Basic + Term(Return) appear.)
    let r = root_of(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "body", "exit")
            .label("body")
            .nop()
            .jump("head")
            .label("exit")
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    assert!(matches!(parts[0], Region::While { .. }));
}

/// **Complex while-header** -- the deciding `Branch` (`cond_at`) is
/// deeper than the loop_header block. Move-source equivalent:
/// `while ({ if a then c1 else c2 }) body`. The header field of the
/// emitted `Region::While` becomes a Seq containing the cond-evaluation
/// scaffold (initial Basic + inner If + the merge label's Basic);
/// `cond_at` points at the deciding Branch's PC, not at the loop_header
/// block. Exercises `find_cond_at`'s post-dom walk and the
/// "starting at the new loop's header" first-iteration skip in
/// `structure`.
#[test]
fn while_with_complex_header() {
    // PC  0: label "head"
    // PC  1: load_bool 0, true              (a)
    // PC  2: branch 0 -> "left" / "right"
    // PC  3: label "left"
    // PC  4: load_bool 1, true              (left's c)
    // PC  5: jump "merge"
    // PC  6: label "right"
    // PC  7: load_bool 1, false             (right's c)
    // PC  8: jump "merge"
    // PC  9: label "merge"
    // PC 10: branch 1 -> "body" / "exit"    (deciding Branch = cond_at)
    // PC 11: label "body"
    // PC 12: nop
    // PC 13: jump "head"
    // PC 14: label "exit"
    // PC 15: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "left", "right")
            .label("left")
            .load_bool(1, true)
            .jump("merge")
            .label("right")
            .load_bool(1, false)
            .jump("merge")
            .label("merge")
            .branch(1, "body", "exit")
            .label("body")
            .nop()
            .jump("head")
            .label("exit")
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    assert_eq!(parts.len(), 3, "parts: {parts:?}");
    let (header, cond_at, body) = match &parts[0] {
        Region::While {
            header,
            cond_at,
            body,
            ..
        } => (header.as_ref(), *cond_at, body.as_ref()),
        other => panic!("expected While, got {other:?}"),
    };
    // cond_at points at the deciding Branch, NOT the loop_header.
    assert_eq!(cond_at, 10);
    // Header shape: Seq([Basic{head+load}, If{cond_eval}, Basic{merge label}]).
    let header_parts = match header {
        Region::Seq(v) => v,
        other => panic!("expected complex header = Seq, got {other:?}"),
    };
    assert_eq!(header_parts.len(), 3, "header parts: {header_parts:?}");
    assert!(matches!(
        header_parts[0],
        Region::Basic { lower: 0, upper: 1 }
    ));
    let (inner_cond_at, then_b, else_b) = match &header_parts[1] {
        Region::If {
            cond_at,
            then_branch,
            else_branch,
        } => (*cond_at, then_branch.as_ref(), else_branch.as_ref()),
        other => panic!("expected inner If in header, got {other:?}"),
    };
    assert_eq!(inner_cond_at, 2);
    assert!(matches!(*then_b, Region::Basic { lower: 3, upper: 4 }));
    assert!(matches!(*else_b, Region::Basic { lower: 6, upper: 7 }));
    assert!(matches!(
        header_parts[2],
        Region::Basic { lower: 9, upper: 9 }
    ));
    // Body: just the body label + nop (jump dropped).
    assert!(matches!(
        *body,
        Region::Basic {
            lower: 11,
            upper: 12
        }
    ));
    // Trailing tail: exit label + Term(Return).
    assert!(matches!(
        parts[1],
        Region::Basic {
            lower: 14,
            upper: 14
        }
    ));
    assert!(matches!(
        parts[2],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
}

/// Regression: `while` loop containing an aborting Call (e.g. `Mul` / `Mod`
/// / narrowing `Cast` -- represented in upstream stackless bytecode with
/// `Some(AbortAction::Check)`) must still be recognized as a loop. The
/// loop-detection CFG (`ignore_return_abort=false`) and the forward CFG
/// (`ignore_return_abort=true`) partition basic blocks differently
/// around aborting Calls -- the same code lands under different
/// `BlockId`s in the two graphs. Before the `loops::translate_loops` PC
/// translation was added, `LoopIndex` was keyed on loop-detection-CFG
/// BlockIds while the structurer queried with forward-CFG BlockIds:
/// `header_at(forward_id)` always missed, the loop went unrecognized,
/// and the structurer recursed through the back-edge as if it were a
/// plain Branch -- 10K+ frame stack overflow on real Move code
/// (`decimal::pow` in scallop-lending was the first repro).
#[test]
fn while_with_aborting_call_in_body_is_recognized_as_loop() {
    use move_stackless_bytecode::stackless_bytecode::Operation;
    // PC 0: label "head"
    // PC 1: load_bool 0, true
    // PC 2: branch 0 -> "body" / "exit"
    // PC 3: label "body"
    // PC 4: Call(Mul, [1], [1, 1], Some(AbortAction::Check))   -- aborting
    // PC 5: jump "head"
    // PC 6: label "exit"
    // PC 7: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "body", "exit")
            .label("body")
            .call_aborting(&[1], Operation::Mul, &[1, 1])
            .jump("head")
            .label("exit")
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    let (cond_at, body) = match &parts[0] {
        Region::While { cond_at, body, .. } => (*cond_at, body.as_ref()),
        other => panic!("expected While, got {other:?}"),
    };
    // The aborting Call at PC 4 sits inside the body. With the
    // `translate_loops` fix the structurer recognizes the loop and
    // emits a `While`; without the fix it would either stack-overflow
    // or shape the back-edge as a plain Branch.
    assert_eq!(cond_at, 2);
    assert!(matches!(body, Region::Basic { lower: 3, upper: 4 }));
    assert!(matches!(
        parts[2],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
}

/// **Regression**: a `while (cond) { if (x) { A; continue } else { B; B'; B''; continue } }`
/// loop has TWO back-edges to the same header — one from each arm's
/// `continue`. `find_natural_loops` returns two `NaturalLoop` entries
/// with the same `loop_header`, each carrying only the body blocks
/// along its own back-edge path. `LoopIndex::build` must UNION their
/// `loop_body` sets; otherwise `is_break` misclassifies any merge
/// label on the path-not-registered as a loop exit and the structurer
/// emits a spurious `Term(Break)`.
///
/// Without the union fix, the structurer collapses the ELSE arm into
/// a `Break` (because the merge points in the descent aren't in the
/// first-registered loop's body), and the descent disappears. Real
/// failure mode: `move_stl::skip_list::remove`'s inner `while
/// (is_some_and_lte) { if (next_score == score) { write } else {
/// borrow_mut_node + descend } }` loses the descent and `test_remove`
/// fuel-exhausts.
///
/// The ELSE arm carries an additional inner `if/then` (one with no
/// `else`) before its `continue`. That inner if produces a merge
/// label inside the loop body — the label whose membership the bug
/// got wrong. Without the inner if, both back-edges'  bodies happen
/// to coincide structurally and the bug doesn't surface.
#[test]
fn while_with_inner_if_continue_in_both_arms_preserves_else_body() {
    // PC  0: label "head"
    // PC  1: load_bool 0, true
    // PC  2: branch 0 -> "body" / "exit"
    // PC  3: label "body"
    // PC  4: branch 1 -> "then_arm" / "else_arm"
    // PC  5: label "then_arm"
    // PC  6: nop                     -- THEN side-effect (back-edge #1)
    // PC  7: jump "head"
    // PC  8: label "else_arm"
    // PC  9: branch 2 -> "guard_t" / "guard_join"
    // PC 10: label "guard_t"
    // PC 11: nop                     -- guarded side-effect
    // PC 12: label "guard_join"      -- merge point INSIDE the loop body
    // PC 13: nop                     -- ELSE side-effect
    // PC 14: jump "head"             -- continue (back-edge #2)
    // PC 15: label "exit"
    // PC 16: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "body", "exit")
            .label("body")
            .branch(1, "then_arm", "else_arm")
            .label("then_arm")
            .nop()
            .jump("head")
            .label("else_arm")
            .branch(2, "guard_t", "guard_join")
            .label("guard_t")
            .nop()
            .label("guard_join")
            .nop()
            .jump("head")
            .label("exit")
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    let (cond_at, body) = match &parts[0] {
        Region::While { cond_at, body, .. } => (*cond_at, body.as_ref()),
        other => panic!("expected While, got {other:?}"),
    };
    assert_eq!(cond_at, 2);
    // The body wraps the inner If in a Seq (the body label + the If).
    // Find the If inside the body and check both arms.
    let inner_if = match body {
        Region::If { .. } => body,
        Region::Seq(parts) => parts
            .iter()
            .find(|p| matches!(p, Region::If { .. }))
            .unwrap_or_else(|| panic!("no If found in body Seq: {body:?}")),
        other => panic!("expected If or Seq, got {other:?}"),
    };
    let (then_arm, else_arm) = match inner_if {
        Region::If {
            then_branch,
            else_branch,
            ..
        } => (then_branch.as_ref(), else_branch.as_ref()),
        _ => unreachable!(),
    };
    // Neither arm may contain a `Term(Break)`. Before the LoopIndex
    // union fix, the ELSE arm collapsed to `Basic + Term(Break level=0)`
    // because the second-registered loop's larger body (containing the
    // ELSE-path's continue) was discarded.
    fn contains_break(r: &Region) -> bool {
        match r {
            Region::Term(Termination::Break { .. }) => true,
            Region::Seq(parts) => parts.iter().any(contains_break),
            Region::If {
                then_branch,
                else_branch,
                ..
            } => contains_break(then_branch) || contains_break(else_branch),
            Region::While { header, body, .. } => contains_break(header) || contains_break(body),
            Region::Switch { branches, .. } => branches.iter().any(contains_break),
            _ => false,
        }
    }
    assert!(
        !contains_break(then_arm),
        "THEN arm contains a spurious Break: {then_arm:?}"
    );
    assert!(
        !contains_break(else_arm),
        "ELSE arm contains a spurious Break: {else_arm:?}"
    );
}

#[test]
fn loop_with_return_only_exits_structures_as_while() {
    // `loop { if c1 { return a }; if c2 { return b }; nop }` with the
    // unreachable tail dropped by the Move compiler -- the back-edge
    // Jump is the LAST pc (cetus_dlmm::bin::prev_score_in_group shape).
    // Stage 1 normalizes the structuring view (final Jump -> Ret +
    // explicit header boundary) and must produce a While whose exits
    // are the two returns, with NO spurious Break.
    let r = root_of(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "ret_a", "next")
            .label("ret_a")
            .ret(&[1])
            .label("next")
            .load_bool(2, false)
            .branch(2, "ret_b", "cont")
            .label("ret_b")
            .ret(&[3])
            .label("cont")
            .nop()
            .jump("head"),
    );
    let Region::Seq(top) = &r else {
        panic!("expected top-level Seq, got {r:?}")
    };
    let Region::While {
        cond_at,
        negate_cond,
        body,
        ..
    } = &top[0]
    else {
        panic!("expected While first, got {:?}", top[0])
    };
    assert_eq!(*cond_at, 2);
    assert!(*negate_cond, "loop continues on cond == false");
    // Body: the second return stays inside; no Break/Continue terms.
    let Region::Seq(body_items) = body.as_ref() else {
        panic!("expected Seq body, got {body:?}")
    };
    assert!(
        body_items.iter().any(|x| matches!(
            x,
            Region::If { then_branch, .. }
                if matches!(then_branch.as_ref(), Region::Seq(arm)
                    if arm.iter().any(|y| matches!(y, Region::Term(Termination::Return { .. }))))
        )),
        "in-loop return missing: {body_items:?}"
    );
    assert!(
        !body_items
            .iter()
            .any(|x| matches!(x, Region::Term(Termination::Break { .. }))),
        "latch must be implicit continue, not Break: {body_items:?}"
    );
    // After the loop: the cond_at exit arm = `return a`.
    assert!(
        top.iter()
            .any(|x| matches!(x, Region::Term(Termination::Return { temps }) if temps == &vec![1])),
        "after-loop return missing: {top:?}"
    );
}

#[test]
fn if_nested_loop_with_two_returns_structures() {
    // `if (c) { loop { if c1 { return a }; if c2 { return b }; nop } };
    // rest` -- the back-edge is MID-code (rest reachable via !c), so the
    // loop component would be exit-free in the structuring CFG; the
    // generalized back-edge exit anchor makes post-doms well-defined.
    let r = super::cfg_from(
        BytecodeBuilder::new()
            .load_bool(4, true)
            .branch(4, "head", "rest")
            .label("head")
            .load_bool(0, true)
            .branch(0, "ret_a", "cont")
            .label("ret_a")
            .ret(&[1])
            .label("cont")
            .load_bool(5, false)
            .branch(5, "ret_b", "cont2")
            .label("ret_b")
            .ret(&[3])
            .label("cont2")
            .nop()
            .jump("head")
            .label("rest")
            .nop()
            .ret(&[2]),
    )
    .expect("nested return-only loop must structure");
    fn count_terms(r: &Region, f: &mut dyn FnMut(&Termination)) {
        match r {
            Region::Seq(xs) => xs.iter().for_each(|x| count_terms(x, f)),
            Region::If {
                then_branch,
                else_branch,
                ..
            } => {
                count_terms(then_branch, f);
                count_terms(else_branch, f);
            }
            Region::Switch { branches, .. } => branches.iter().for_each(|x| count_terms(x, f)),
            Region::While { header, body, .. } => {
                count_terms(header, f);
                count_terms(body, f);
            }
            Region::LabeledBlock { body } => count_terms(body, f),
            Region::Term(t) => f(t),
            Region::Basic { .. } => {}
        }
    }
    let mut whiles = 0;
    fn count_whiles(r: &Region, n: &mut u32) {
        match r {
            Region::Seq(xs) => xs.iter().for_each(|x| count_whiles(x, n)),
            Region::If {
                then_branch,
                else_branch,
                ..
            } => {
                count_whiles(then_branch, n);
                count_whiles(else_branch, n);
            }
            Region::Switch { branches, .. } => branches.iter().for_each(|x| count_whiles(x, n)),
            Region::While { header, body, .. } => {
                *n += 1;
                count_whiles(header, n);
                count_whiles(body, n);
            }
            Region::LabeledBlock { body } => count_whiles(body, n),
            _ => {}
        }
    }
    count_whiles(&r.root, &mut whiles);
    assert_eq!(whiles, 1, "exactly one While: {:?}", r.root);
    let (mut returns, mut breaks) = (0u32, 0u32);
    count_terms(&r.root, &mut |t| match t {
        Termination::Return { .. } => returns += 1,
        Termination::Break { .. } => breaks += 1,
        _ => {}
    });
    assert_eq!(returns, 3, "three returns (a, b, rest): {:?}", r.root);
    assert_eq!(breaks, 0, "no spurious breaks: {:?}", r.root);
    // The return-only loop falls through like an early return, so `rest`
    // is the outer if's JOIN: its return sits at top level and the else
    // arm stays empty (not `rest` nested into the else).
    let Region::Seq(top) = &r.root else {
        panic!("expected top-level Seq, got {:?}", r.root)
    };
    assert!(
        matches!(top.last(), Some(Region::Term(Termination::Return { temps })) if temps == &vec![2]),
        "rest's return must close the top-level Seq: {top:?}"
    );
    let else_arm = top
        .iter()
        .find_map(|x| match x {
            Region::If { else_branch, .. } => Some(else_branch),
            _ => None,
        })
        .expect("outer if present");
    assert!(
        matches!(else_arm.as_ref(), Region::Seq(v) if v.is_empty()),
        "else arm must be empty -- rest is the join: {else_arm:?}"
    );
}

#[test]
fn nested_return_only_loop_with_continue() {
    // `if (c) { loop { if a { return x }; if b { continue }; nop } };
    // rest` -- a return-only loop with TWO latches. Only the exiting
    // latch (textual successor outside the loop) falls through; the
    // mid-body continue latch gets nothing.
    let r = super::cfg_from(
        BytecodeBuilder::new()
            .load_bool(6, true)
            .branch(6, "head", "rest")
            .label("head")
            .load_bool(0, true)
            .branch(0, "ret_x", "n1")
            .label("ret_x")
            .ret(&[1])
            .label("n1")
            .load_bool(2, false)
            .branch(2, "do_cont", "after")
            .label("do_cont")
            .jump("head")
            .label("after")
            .nop()
            .jump("head")
            .label("rest")
            .nop()
            .ret(&[2]),
    )
    .expect("multi-latch return-only loop must structure");
    let Region::Seq(top) = &r.root else {
        panic!("expected top-level Seq, got {:?}", r.root)
    };
    assert!(
        matches!(top.last(), Some(Region::Term(Termination::Return { temps })) if temps == &vec![2]),
        "rest's return must close the top-level Seq: {top:?}"
    );
    let (mut returns, mut continues, mut breaks) = (0u32, 0u32, 0u32);
    fn walk(r: &Region, f: &mut dyn FnMut(&Termination)) {
        match r {
            Region::Seq(xs) => xs.iter().for_each(|x| walk(x, f)),
            Region::If {
                then_branch,
                else_branch,
                ..
            } => {
                walk(then_branch, f);
                walk(else_branch, f);
            }
            Region::Switch { branches, .. } => branches.iter().for_each(|x| walk(x, f)),
            Region::While { header, body, .. } => {
                walk(header, f);
                walk(body, f);
            }
            Region::LabeledBlock { body } => walk(body, f),
            Region::Term(t) => f(t),
            Region::Basic { .. } => {}
        }
    }
    walk(&r.root, &mut |t| match t {
        Termination::Return { .. } => returns += 1,
        Termination::Continue { .. } => continues += 1,
        Termination::Break { .. } => breaks += 1,
        _ => {}
    });
    assert_eq!(returns, 2, "ret_x + rest: {top:?}");
    assert_eq!(continues, 1, "the explicit mid-body continue: {top:?}");
    assert_eq!(breaks, 0, "no spurious breaks: {top:?}");
}

#[test]
fn one_return_loop_with_non_header_decision_structures() {
    // `loop { if a { nop }; if r { return x }; nop }` -- function-final,
    // ONE return, but the r-decision sits one post-dom step below the
    // header block, so find_loop_decision's walk itself needs an
    // immediate post-dominator on an exit-free loop. Covered by the
    // back-edge exit anchor; without it this errored UnsupportedLoop.
    let r = super::cfg_from(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "a_then", "merge")
            .label("a_then")
            .nop()
            .jump("merge")
            .label("merge")
            .load_bool(2, true)
            .branch(2, "ret_x", "cont")
            .label("ret_x")
            .ret(&[1])
            .label("cont")
            .nop()
            .jump("head"),
    )
    .expect("walk-variant return-only loop must structure");
    let mut whiles = 0u32;
    fn count_whiles(r: &Region, n: &mut u32) {
        match r {
            Region::Seq(xs) => xs.iter().for_each(|x| count_whiles(x, n)),
            Region::If {
                then_branch,
                else_branch,
                ..
            } => {
                count_whiles(then_branch, n);
                count_whiles(else_branch, n);
            }
            Region::Switch { branches, .. } => branches.iter().for_each(|x| count_whiles(x, n)),
            Region::While { header, body, .. } => {
                *n += 1;
                count_whiles(header, n);
                count_whiles(body, n);
            }
            Region::LabeledBlock { body } => count_whiles(body, n),
            _ => {}
        }
    }
    count_whiles(&r.root, &mut whiles);
    assert_eq!(whiles, 1, "expected one While: {:?}", r.root);
}

#[test]
fn loop_without_every_iteration_decision_errors_cleanly() {
    // `loop { if a { if b { return x } }; nop }` -- the return decision
    // runs only when `a`, so NO block on the header's post-dom chain
    // carries an in/out branch: this is `while true` with a conditional
    // early return, which the cond_at-based While model cannot express.
    // Pre-existing limitation, orthogonal to the exit-anchor work; the
    // expected behavior is the clean per-function UnsupportedLoop stub
    // (zero corpus instances today). If while-true support lands, update
    // this test deliberately.
    let r = super::cfg_from(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "outer_then", "cont")
            .label("outer_then")
            .load_bool(2, true)
            .branch(2, "ret_x", "cont")
            .label("ret_x")
            .ret(&[1])
            .label("cont")
            .nop()
            .jump("head"),
    );
    assert!(
        matches!(
            r,
            Err(super::Stage1Error::UnsupportedLoop { loop_header_pc: 0 })
        ),
        "expected UnsupportedLoop, got {r:?}"
    );
}
