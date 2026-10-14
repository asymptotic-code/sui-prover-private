//! Variant introduction tests for non-loop control flow:
//! `Bytecode::Ret`, `Bytecode::Abort`, `Bytecode::Branch`,
//! `Bytecode::VariantSwitch`, plain fall-through.

use super::super::Termination;
use super::root_of;
use super::BytecodeBuilder;
use super::Region;
use move_stackless_bytecode::stackless_bytecode::Operation;

/// `nop; ret` -> `Seq([Basic{0..=0}, Term(Return)])`. The Ret block has
/// nothing before its terminator, so its Basic is omitted.
#[test]
fn nop_then_ret_emits_basic_and_term_return() {
    let r = root_of(BytecodeBuilder::new().nop().ret(&[]));
    match r {
        Region::Seq(parts) => {
            assert_eq!(
                parts.len(),
                2,
                "expected Basic + Term(Return), got {parts:?}"
            );
            assert!(matches!(parts[0], Region::Basic { lower: 0, upper: 0 }));
            match &parts[1] {
                Region::Term(Termination::Return { temps }) => assert!(temps.is_empty()),
                other => panic!("expected Term(Return), got {other:?}"),
            }
        }
        other => panic!("expected Seq, got {other:?}"),
    }
}

/// Bare `ret` with no body has no Basic, just the Termination.
#[test]
fn bare_ret_emits_only_term_return() {
    let r = root_of(BytecodeBuilder::new().ret(&[]));
    assert!(matches!(
        r,
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
}

/// `ret(&[3, 4])` carries the source temps through unchanged.
#[test]
fn ret_carries_source_temps() {
    let r = root_of(BytecodeBuilder::new().ret(&[3, 4]));
    match r {
        Region::Term(Termination::Return { temps }) => assert_eq!(temps, vec![3, 4]),
        other => panic!("expected Term(Return), got {other:?}"),
    }
}

/// `abort 7` -> `Term(Abort{Some(7)})`. Stage 1 always emits `Some(...)`;
/// `None` is reserved for synthetic aborts inserted by later stages.
#[test]
fn abort_emits_term_with_code_temp() {
    let r = root_of(BytecodeBuilder::new().abort(7));
    assert!(matches!(
        r,
        Region::Term(Termination::Abort { code_temp: Some(7) })
    ));
}

/// `if (cond) { ret } else { ret }`. Both arms terminate.
///
/// **Asymmetric shape.** Stage 1 builds its CFGs with
/// `ignore_return_abort=true`, which gives mid-code `Ret`/`Abort`
/// blocks a synthetic fall-through edge to `pc+1` instead of edging to
/// `DUMMY_EXIT`. That setting is what makes the *common* early-return
/// pattern lift cleanly (`if (cond) return; rest_of_function;` ->
/// `Seq([..., If{then: Term(Return), else: Seq([])}, rest, Term(Return)])`),
/// at the cost of producing an asymmetric IR for the rare "every arm
/// returns" case: the post-dom of the if is the *second* `Ret`'s block,
/// the else-recursion finds `start == stop` immediately and returns
/// `Seq([])`, and the second `Ret` is then processed by the *outer*
/// iteration as the function tail.
///
/// Expected shape:
///   `Seq([ Basic{0..=0}, If{ then: arm{Basic{2..=2}, Term(Return)}, else: Seq([]) }, Basic{4..=4}, Term(Return) ])`.
#[test]
fn if_with_terminating_arms_asymmetric() {
    // PC 0: load_bool 0, true   (cond = temp 0)
    // PC 1: branch 0 -> "t" / "e"
    // PC 2: label "t"
    // PC 3: ret []
    // PC 4: label "e"
    // PC 5: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .load_bool(0, true)
            .branch(0, "t", "e")
            .label("t")
            .ret(&[])
            .label("e")
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    assert_eq!(parts.len(), 4, "parts: {parts:?}");
    assert!(matches!(parts[0], Region::Basic { lower: 0, upper: 0 }));
    let (cond_at, then_branch, else_branch) = match &parts[1] {
        Region::If {
            cond_at,
            then_branch,
            else_branch,
        } => (*cond_at, then_branch, else_branch),
        other => panic!("expected If, got {other:?}"),
    };
    assert_eq!(cond_at, 1);
    assert_arm_label_then_ret(then_branch, 2);
    // Else-arm collapses to Seq([]) -- it WAS the post-dom in disguise.
    assert!(matches!(else_branch.as_ref(), Region::Seq(v) if v.is_empty()));
    // Trailing function tail: the else-arm's bytecode (label + ret) gets
    // hoisted out of the If and consumed by the outer iteration.
    assert!(matches!(parts[2], Region::Basic { lower: 4, upper: 4 }));
    assert!(matches!(
        parts[3],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
}

/// Add a fixture for the early-return pattern that motivates
/// `ignore_return_abort=true`: `if (cond) return; rest;`. The expected
/// shape has the `If` with an empty else-arm, followed by the rest of
/// the function as the outer tail.
#[test]
fn if_then_return_followed_by_rest_lifts_cleanly() {
    // PC 0: load_bool 0, true     (cond)
    // PC 1: branch 0 -> "early" / "rest"
    // PC 2: label "early"
    // PC 3: ret []
    // PC 4: label "rest"
    // PC 5: nop
    // PC 6: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .load_bool(0, true)
            .branch(0, "early", "rest")
            .label("early")
            .ret(&[])
            .label("rest")
            .nop()
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    assert_eq!(parts.len(), 4, "parts: {parts:?}");
    assert!(matches!(parts[0], Region::Basic { lower: 0, upper: 0 }));
    let (then_branch, else_branch) = match &parts[1] {
        Region::If {
            then_branch,
            else_branch,
            ..
        } => (then_branch.as_ref(), else_branch.as_ref()),
        other => panic!("expected If, got {other:?}"),
    };
    assert_arm_label_then_ret(
        &Region::Seq(match then_branch {
            Region::Seq(v) => v.clone(),
            other => panic!("expected then-arm Seq, got {other:?}"),
        }),
        2,
    );
    // Else collapses (post-dom == "rest" block).
    assert!(matches!(else_branch, Region::Seq(v) if v.is_empty()));
    // The "rest" block becomes the outer tail.
    assert!(matches!(parts[2], Region::Basic { lower: 4, upper: 5 }));
    assert!(matches!(
        parts[3],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
}

fn assert_arm_label_then_ret(arm: &Region, label_pc: u16) {
    let parts = match arm {
        Region::Seq(parts) => parts,
        other => panic!("expected arm = Seq, got {other:?}"),
    };
    assert_eq!(parts.len(), 2, "arm parts: {parts:?}");
    assert!(
        matches!(parts[0], Region::Basic { lower, upper } if lower == label_pc && upper == label_pc)
    );
    assert!(matches!(
        parts[1],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
}

/// `if (cond) { nop; jump end } else { nop; jump end }; end: ret`. Both
/// arms fall through to the same join point. The Jump terminators are
/// dropped from each arm's Basic; the End block contributes a Basic for
/// its leading label plus a Term(Return).
#[test]
fn if_with_falling_through_arms_meets_at_ret() {
    let r = root_of(
        BytecodeBuilder::new()
            .load_bool(0, true)
            .branch(0, "t", "e")
            .label("t")
            .nop()
            .jump("end")
            .label("e")
            .nop()
            .jump("end")
            .label("end")
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    // [Basic{0..=0}, If{...}, Basic{8..=8}, Term(Return)]
    assert_eq!(parts.len(), 4);
    assert!(matches!(parts[0], Region::Basic { lower: 0, upper: 0 }));
    let (then_branch, else_branch) = match &parts[1] {
        Region::If {
            then_branch,
            else_branch,
            ..
        } => (then_branch.as_ref(), else_branch.as_ref()),
        other => panic!("expected If, got {other:?}"),
    };
    // Each arm: a single Basic spanning {label_pc, nop_pc} (Jump dropped).
    assert!(matches!(*then_branch, Region::Basic { lower: 2, upper: 3 }));
    assert!(matches!(*else_branch, Region::Basic { lower: 5, upper: 6 }));
    assert!(matches!(parts[2], Region::Basic { lower: 8, upper: 8 }));
    assert!(matches!(
        parts[3],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
}

#[test]
fn jump_before_unreachable_traces_is_consumed() {
    let r = root_of(
        BytecodeBuilder::new()
            .label("merge")
            .call(&[], Operation::TraceReturn(0), &[2])
            .call(&[], Operation::TraceLocal(0), &[0])
            .label("destroy")
            .call(&[], Operation::Destroy, &[0])
            .jump("return")
            .label("unreachable_trace")
            .call(&[], Operation::TraceLocal(0), &[0])
            .call(&[], Operation::TraceMessage("unreachable".to_string()), &[])
            .label("return")
            .ret(&[2]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    assert_eq!(parts.len(), 3, "parts: {parts:?}");
    assert!(matches!(parts[0], Region::Basic { lower: 0, upper: 4 }));
    assert!(matches!(parts[1], Region::Basic { lower: 9, upper: 9 }));
    assert!(matches!(
        parts[2],
        Region::Term(Termination::Return { ref temps }) if temps.as_slice() == [2]
    ));
}

/// Regression: `navi lending_core::storage::get_emode_asset_mut`.
///
/// A `&mut`-returning selector whose last arm aborts makes the borrow
/// instrumenter emit a write-back epilogue behind an orphaned label, AFTER the
/// jump that skips it. Upstream splits blocks only at `branch_dests` targets,
/// so the orphaned label starts no block and the `Jump` stays interior; the
/// dead suffix is `Label + WriteBack + trace`, not traces alone.
///
/// Before the structural fix, only a trace-only suffix was recognised, so the
/// `Jump` was emitted inside the `Region::Basic` and stage 2 rejected the whole
/// function with `Bytecode::Jump reached translate_op`. The function then
/// landed as an `Inhabited` placeholder -- `(default, default, world)` with an
/// unconditionally `Aborted` abort side -- which is invisible to the sorry
/// census because it is not a `sorry`.
#[test]
fn jump_before_unreachable_writeback_epilogue_is_consumed() {
    use move_stackless_bytecode::stackless_bytecode::{BorrowEdge, BorrowNode};
    let r = root_of(
        BytecodeBuilder::new()
            .label("merge")
            .call(&[], Operation::Destroy, &[0])
            .jump("return")
            .label("orphan_epilogue")
            .call(
                &[],
                Operation::WriteBack(BorrowNode::Reference(8), BorrowEdge::Direct),
                &[9],
            )
            .call(&[], Operation::TraceLocal(0), &[0])
            .label("return")
            .ret(&[2]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    assert_eq!(parts.len(), 3, "parts: {parts:?}");
    // Basic stops before the jump at pc2; the dead pc3..pc5 epilogue is dropped.
    assert!(matches!(parts[0], Region::Basic { lower: 0, upper: 1 }));
    assert!(matches!(parts[1], Region::Basic { lower: 6, upper: 6 }));
    assert!(matches!(
        parts[2],
        Region::Term(Termination::Return { ref temps }) if temps.as_slice() == [2]
    ));
}

/// `variant_switch t -> [a, b, c]` with three terminating arms.
///
/// **Asymmetric shape**, same reasoning as `if_with_terminating_arms_asymmetric`:
/// with `ignore_return_abort=true`, the post-dom of the switch is the
/// last arm's block. The first two arms recurse with `stop = last_arm`
/// and return `Seq([Basic, Term(Return)])`. The last arm has
/// `start == stop` and returns `Seq([])`. The outer iteration then
/// processes the last arm's bytecode as the function tail.
#[test]
fn variant_switch_three_terminating_arms_asymmetric() {
    let r = root_of(
        BytecodeBuilder::new()
            .variant_switch(0, &["a", "b", "c"])
            .label("a")
            .ret(&[])
            .label("b")
            .ret(&[])
            .label("c")
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    assert_eq!(parts.len(), 3, "parts: {parts:?}");
    let (switch_at, branches) = match &parts[0] {
        Region::Switch {
            switch_at,
            branches,
        } => (*switch_at, branches),
        other => panic!("expected Switch, got {other:?}"),
    };
    assert_eq!(switch_at, 0);
    assert_eq!(branches.len(), 3);
    // First two arms terminate explicitly.
    assert_arm_label_then_ret(&branches[0], 1);
    assert_arm_label_then_ret(&branches[1], 3);
    // Third arm collapses to Seq([]) -- it WAS the post-dom in disguise.
    assert!(matches!(&branches[2], Region::Seq(v) if v.is_empty()));
    // Trailing function tail: the third arm's bytecode hoisted out.
    assert!(matches!(parts[1], Region::Basic { lower: 5, upper: 5 }));
    assert!(matches!(
        parts[2],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
}

/// Switch where every arm falls through to a common merge block. No
/// arm terminates; each arm's tail is the natural fall-through to the
/// post-dom (the merge), which stage 2 lifts as `BlockTail::Value(Unit)`.
/// The merge block + its `ret` becomes the trailing function tail.
#[test]
fn variant_switch_all_arms_fall_through_to_merge() {
    // PC 0: variant_switch t -> [a, b, c]
    // PC 1: label "a"
    // PC 2: jump "end"
    // PC 3: label "b"
    // PC 4: jump "end"
    // PC 5: label "c"
    // PC 6: jump "end"
    // PC 7: label "end"
    // PC 8: nop
    // PC 9: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .variant_switch(0, &["a", "b", "c"])
            .label("a")
            .jump("end")
            .label("b")
            .jump("end")
            .label("c")
            .jump("end")
            .label("end")
            .nop()
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    assert_eq!(parts.len(), 3, "parts: {parts:?}");
    let (switch_at, branches) = match &parts[0] {
        Region::Switch {
            switch_at,
            branches,
        } => (*switch_at, branches),
        other => panic!("expected Switch, got {other:?}"),
    };
    assert_eq!(switch_at, 0);
    assert_eq!(branches.len(), 3);
    // Each arm: a single Basic for the label (Jump dropped). No Term --
    // the natural tail is "merge at post-dom of the Switch".
    assert!(matches!(branches[0], Region::Basic { lower: 1, upper: 1 }));
    assert!(matches!(branches[1], Region::Basic { lower: 3, upper: 3 }));
    assert!(matches!(branches[2], Region::Basic { lower: 5, upper: 5 }));
    // Trailing: the merge block (label end + nop, ret excluded) + its Term.
    assert!(matches!(parts[1], Region::Basic { lower: 7, upper: 8 }));
    assert!(matches!(
        parts[2],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
}

/// Switch with mixed arm behaviors: arms A and C terminate via `ret`;
/// arm B falls through to the merge. Terminating arms get explicit
/// `Term(Return)`; the falling-through arm has the natural `Value(Unit)`
/// tail at lift time. The trailing merge runs once per execution that
/// took the falling-through arm.
#[test]
fn variant_switch_mixed_terminating_and_fall_through_arms() {
    // PC 0: variant_switch t -> [a, b, c]
    // PC 1: label "a"
    // PC 2: ret []                  (arm A terminates)
    // PC 3: label "b"
    // PC 4: jump "end"               (arm B falls through)
    // PC 5: label "c"
    // PC 6: ret []                  (arm C terminates)
    // PC 7: label "end"
    // PC 8: nop
    // PC 9: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .variant_switch(0, &["a", "b", "c"])
            .label("a")
            .ret(&[])
            .label("b")
            .jump("end")
            .label("c")
            .ret(&[])
            .label("end")
            .nop()
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    assert_eq!(parts.len(), 3, "parts: {parts:?}");
    let (switch_at, branches) = match &parts[0] {
        Region::Switch {
            switch_at,
            branches,
        } => (*switch_at, branches),
        other => panic!("expected Switch, got {other:?}"),
    };
    assert_eq!(switch_at, 0);
    assert_eq!(branches.len(), 3);
    // Arm A: explicit Term(Return).
    assert_arm_label_then_ret(&branches[0], 1);
    // Arm B: just a Basic (label only, jump dropped) -- falls through.
    assert!(matches!(branches[1], Region::Basic { lower: 3, upper: 3 }));
    // Arm C: explicit Term(Return).
    assert_arm_label_then_ret(&branches[2], 5);
    // Trailing merge: Basic{7..=8} (label + nop) + Term(Return).
    assert!(matches!(parts[1], Region::Basic { lower: 7, upper: 8 }));
    assert!(matches!(
        parts[2],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
}

/// `if (a) { if (b) ret_x else ret_y } else { ret_z }` -- nested If
/// inside the outer's then-arm. Confirms the structurer's recursion
/// is uniform: the inner If is structured exactly as a top-level If
/// would be, with its own asymmetric collapse for "every-arm-terminates".
#[test]
fn nested_if_inside_then_arm() {
    // PC 0: load_bool 0, true       (a)
    // PC 1: branch 0 -> "outer_then" / "outer_else"
    // PC 2: label "outer_then"
    // PC 3: load_bool 1, true       (b)
    // PC 4: branch 1 -> "inner_then" / "inner_else"
    // PC 5: label "inner_then"
    // PC 6: ret []
    // PC 7: label "inner_else"
    // PC 8: ret []
    // PC 9: label "outer_else"
    // PC 10: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .load_bool(0, true)
            .branch(0, "outer_then", "outer_else")
            .label("outer_then")
            .load_bool(1, true)
            .branch(1, "inner_then", "inner_else")
            .label("inner_then")
            .ret(&[])
            .label("inner_else")
            .ret(&[])
            .label("outer_else")
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected outer Seq, got {other:?}"),
    };
    // Outer is asymmetric: [Basic{a}, If, Basic{outer_else_label}, Term(Return)].
    assert_eq!(parts.len(), 4, "outer parts: {parts:?}");
    assert!(matches!(parts[0], Region::Basic { lower: 0, upper: 0 }));
    let (outer_cond, outer_then, outer_else) = match &parts[1] {
        Region::If {
            cond_at,
            then_branch,
            else_branch,
        } => (*cond_at, then_branch.as_ref(), else_branch.as_ref()),
        other => panic!("expected outer If, got {other:?}"),
    };
    assert_eq!(outer_cond, 1);
    // Outer else collapses (asymmetric every-arm-terminates).
    assert!(matches!(outer_else, Region::Seq(v) if v.is_empty()));
    // Outer else-arm body hoisted to the outer tail.
    assert!(matches!(parts[2], Region::Basic { lower: 9, upper: 9 }));
    assert!(matches!(
        parts[3],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
    // Outer then-arm: contains its own asymmetric If for the inner condition.
    let outer_then_parts = match outer_then {
        Region::Seq(v) => v,
        other => panic!("expected outer-then = Seq, got {other:?}"),
    };
    // [Basic{outer_then_label + load_bool b}, If{inner}, Basic{inner_else_label}, Term(Return)]
    assert_eq!(outer_then_parts.len(), 4);
    assert!(matches!(
        outer_then_parts[0],
        Region::Basic { lower: 2, upper: 3 }
    ));
    let (inner_cond, inner_then, inner_else) = match &outer_then_parts[1] {
        Region::If {
            cond_at,
            then_branch,
            else_branch,
        } => (*cond_at, then_branch.as_ref(), else_branch.as_ref()),
        other => panic!("expected inner If, got {other:?}"),
    };
    assert_eq!(inner_cond, 4);
    assert_arm_label_then_ret(inner_then, 5);
    assert!(matches!(inner_else, Region::Seq(v) if v.is_empty()));
    assert!(matches!(
        outer_then_parts[2],
        Region::Basic { lower: 7, upper: 7 }
    ));
    assert!(matches!(
        outer_then_parts[3],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
}

/// Degenerate `if (cond) {}` -- both arms of the `Bytecode::Branch`
/// point at the same label. The structurer detects `then_b == else_b`,
/// pushes only the cond block's pre-Branch Basic, and skips emitting an
/// `If` region entirely; control falls through to the join.
#[test]
fn degenerate_if_with_identical_arms_skips_if_region() {
    // PC 0: load_bool 0, true
    // PC 1: branch 0 -> "join" / "join"   (both arms identical)
    // PC 2: label "join"
    // PC 3: nop
    // PC 4: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .load_bool(0, true)
            .branch(0, "join", "join")
            .label("join")
            .nop()
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    // [Basic{cond, branch dropped}, Basic{join_label + nop, ret excluded}, Term(Return)].
    // No If region.
    assert_eq!(parts.len(), 3, "parts: {parts:?}");
    assert!(matches!(parts[0], Region::Basic { lower: 0, upper: 0 }));
    assert!(matches!(parts[1], Region::Basic { lower: 2, upper: 3 }));
    assert!(matches!(
        parts[2],
        Region::Term(Termination::Return { ref temps }) if temps.is_empty()
    ));
    // Confirm no If anywhere in the tree.
    fn has_if(r: &Region) -> bool {
        match r {
            Region::If { .. } => true,
            Region::Seq(parts) => parts.iter().any(has_if),
            Region::Switch { branches, .. } => branches.iter().any(has_if),
            Region::While { header, body, .. } => has_if(header) || has_if(body),
            Region::LabeledBlock { body } => has_if(body),
            Region::Basic { .. } | Region::Term(_) => false,
        }
    }
    let root = Region::Seq(parts);
    assert!(!has_if(&root), "no If should be emitted: {root:?}");
}
