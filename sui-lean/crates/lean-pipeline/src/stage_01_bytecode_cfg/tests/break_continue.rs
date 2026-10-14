//! Break/continue fixtures.

use super::super::Termination;
use super::root_of;
use super::BytecodeBuilder;
use super::Region;

/// `while (cond) { if (other) break; nop }`. Tests:
///   * innermost `break` in a non-tail position emits `Term(Break{0})`,
///   * innermost `continue` in a non-tail position emits explicit
///     `Term(Continue{0})` (the else-arm reaches the loop header via
///     `jump head`, but it's not the body's natural tail),
///   * the body Seq has *no* trailing Term -- both arms of the If
///     already terminate, so the If is the body's tail.
#[test]
fn inner_break_with_implicit_else_continue() {
    let r = root_of(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "body", "exit")
            .label("body")
            .load_bool(1, true)
            .branch(1, "do_break", "after_inner")
            .label("do_break")
            .jump("exit")
            .label("after_inner")
            .nop()
            .jump("head")
            .label("exit")
            .ret(&[]),
    );
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    let body = match &parts[0] {
        Region::While { body, .. } => body.as_ref(),
        other => panic!("expected While, got {other:?}"),
    };
    let body_parts = match body {
        Region::Seq(v) => v,
        other => panic!("expected body=Seq, got {other:?}"),
    };
    assert_eq!(body_parts.len(), 2, "body: {body_parts:?}");
    assert!(matches!(
        body_parts[0],
        Region::Basic { lower: 3, upper: 4 }
    ));
    let (then_branch, else_branch) = match &body_parts[1] {
        Region::If {
            then_branch,
            else_branch,
            ..
        } => (then_branch.as_ref(), else_branch.as_ref()),
        other => panic!("expected If, got {other:?}"),
    };
    // The then-arm preserves the do_break block's label-only `Basic`
    // before emitting `Term(Break)`. The stage 1 structurer no longer
    // collapses a pure pass-through break-pad into a bare `Term(Break)`
    // -- preserving the Basic costs nothing (label-only blocks are
    // no-ops at lift time) and is required for non-trivial break pads
    // whose Basic carries actual side effects (e.g. `level = ...; break`
    // inside `rand_level`).
    let then_parts = match then_branch {
        Region::Seq(v) => v,
        other => panic!("expected then=Seq, got {other:?}"),
    };
    assert_eq!(then_parts.len(), 2, "then parts: {then_parts:?}");
    assert!(matches!(
        then_parts[0],
        Region::Basic { lower: 6, upper: 6 }
    ));
    assert!(matches!(
        then_parts[1],
        Region::Term(Termination::Break { level: 0 })
    ));
    let else_parts = match else_branch {
        Region::Seq(v) => v,
        other => panic!("expected else=Seq, got {other:?}"),
    };
    assert_eq!(else_parts.len(), 2);
    assert!(matches!(
        else_parts[0],
        Region::Basic { lower: 8, upper: 9 }
    ));
    assert!(matches!(
        else_parts[1],
        Region::Term(Termination::Continue { level: 0 })
    ));
}

/// `while (outer) { while (inner) { if (x) break_outer } }`. The inner
/// loop's body has an If whose then-arm jumps past BOTH loops --
/// `Term(Break { level: 1 })`.
#[test]
fn cross_level_break_two_deep() {
    // PC  0: label "outer_head"
    // PC  1: load_bool 0, true
    // PC  2: branch 0 -> "outer_body" / "outer_exit"
    // PC  3: label "outer_body"
    // PC  4: label "inner_head"     (a label following another label is still a block boundary for `bb_offsets`)
    // PC  5: load_bool 1, true
    // PC  6: branch 1 -> "inner_body" / "inner_exit"
    // PC  7: label "inner_body"
    // PC  8: load_bool 2, true
    // PC  9: branch 2 -> "do_break_outer" / "after_inner"
    // PC 10: label "do_break_outer"
    // PC 11: jump "outer_exit"
    // PC 12: label "after_inner"
    // PC 13: nop
    // PC 14: jump "inner_head"
    // PC 15: label "inner_exit"
    // PC 16: jump "outer_head"
    // PC 17: label "outer_exit"
    // PC 18: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .label("outer_head")
            .load_bool(0, true)
            .branch(0, "outer_body", "outer_exit")
            .label("outer_body")
            .label("inner_head")
            .load_bool(1, true)
            .branch(1, "inner_body", "inner_exit")
            .label("inner_body")
            .load_bool(2, true)
            .branch(2, "do_break_outer", "after_inner")
            .label("do_break_outer")
            .jump("outer_exit")
            .label("after_inner")
            .nop()
            .jump("inner_head")
            .label("inner_exit")
            .jump("outer_head")
            .label("outer_exit")
            .ret(&[]),
    );
    // Drill in: outer While -> inner While -> If with then=Break{1}.
    let outer_body = match &r {
        Region::Seq(parts) => match &parts[0] {
            Region::While { body, .. } => body.as_ref(),
            other => panic!("expected outer While, got {other:?}"),
        },
        other => panic!("expected Seq, got {other:?}"),
    };
    // outer_body should contain the inner While somewhere; find it.
    fn find_inner_while(r: &Region) -> Option<&Region> {
        match r {
            Region::While { .. } => Some(r),
            Region::Seq(parts) => parts.iter().find_map(find_inner_while),
            Region::If {
                then_branch,
                else_branch,
                ..
            } => find_inner_while(then_branch).or_else(|| find_inner_while(else_branch)),
            Region::Switch { branches, .. } => branches.iter().find_map(find_inner_while),
            Region::LabeledBlock { body } => find_inner_while(body),
            Region::Basic { .. } | Region::Term(_) => None,
        }
    }
    let inner = find_inner_while(outer_body).expect("inner While not found");
    let inner_body = match inner {
        Region::While { body, .. } => body.as_ref(),
        _ => unreachable!(),
    };
    fn has_break_level_one(r: &Region) -> bool {
        match r {
            Region::Term(Termination::Break { level: 1 }) => true,
            Region::Seq(parts) => parts.iter().any(has_break_level_one),
            Region::If {
                then_branch,
                else_branch,
                ..
            } => has_break_level_one(then_branch) || has_break_level_one(else_branch),
            Region::Switch { branches, .. } => branches.iter().any(has_break_level_one),
            Region::While { header, body, .. } => {
                has_break_level_one(header) || has_break_level_one(body)
            }
            _ => false,
        }
    }
    assert!(
        has_break_level_one(inner_body),
        "inner body missing Term(Break{{level:1}}): {inner_body:#?}"
    );
}

/// `while (outer) { while (inner) { if (x) continue_outer } }`. Like the
/// cross-level break case but the inner if's then-arm jumps to
/// `outer_head` instead of `outer_exit`. `is_continue` from inside the
/// inner body finds `outer_head` at level 1 -> `Term(Continue{1})`.
#[test]
fn cross_level_continue_two_deep() {
    let r = root_of(
        BytecodeBuilder::new()
            .label("outer_head")
            .load_bool(0, true)
            .branch(0, "outer_body", "outer_exit")
            .label("outer_body")
            .label("inner_head")
            .load_bool(1, true)
            .branch(1, "inner_body", "inner_exit")
            .label("inner_body")
            .load_bool(2, true)
            .branch(2, "do_continue_outer", "after_inner")
            .label("do_continue_outer")
            .jump("outer_head")
            .label("after_inner")
            .nop()
            .jump("inner_head")
            .label("inner_exit")
            .jump("outer_head")
            .label("outer_exit")
            .ret(&[]),
    );
    fn has_continue_level_one(r: &Region) -> bool {
        match r {
            Region::Term(Termination::Continue { level: 1 }) => true,
            Region::Seq(parts) => parts.iter().any(has_continue_level_one),
            Region::If {
                then_branch,
                else_branch,
                ..
            } => has_continue_level_one(then_branch) || has_continue_level_one(else_branch),
            Region::Switch { branches, .. } => branches.iter().any(has_continue_level_one),
            Region::While { header, body, .. } => {
                has_continue_level_one(header) || has_continue_level_one(body)
            }
            Region::LabeledBlock { body } => has_continue_level_one(body),
            _ => false,
        }
    }
    assert!(
        has_continue_level_one(&r),
        "expected Term(Continue{{level:1}}) somewhere in {r:#?}"
    );
}

/// `while (c) { match t { A => break; B => continue; C => continue; } }`.
/// Tests that switch-arm recursion correctly handles break/continue
/// terminations: arm A's jump-to-exit fires `is_break(level=0)`, arms
/// B and C's jump-to-head fires the step-through-Jump-to-continue-target
/// guard followed by `is_continue(level=0)`. The two natural loops
/// share the header (one back-edge per continue), but the step-through
/// guard sidesteps the LoopIndex first-write-wins ambiguity by
/// resolving via the jump's destination rather than the bridge block's
/// loop-body membership.
#[test]
fn switch_in_loop_with_break_and_continue_arms() {
    let r = root_of(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "body", "exit")
            .label("body")
            .load_u64(1, 0)
            .variant_switch(1, &["a", "b", "c"])
            .label("a")
            .jump("exit")
            .label("b")
            .jump("head")
            .label("c")
            .jump("head")
            .label("exit")
            .ret(&[]),
    );
    // Drill into the While's body, find the Switch.
    let body = match &r {
        Region::Seq(parts) => match &parts[0] {
            Region::While { body, .. } => body.as_ref(),
            other => panic!("expected outer While, got {other:?}"),
        },
        other => panic!("expected outer Seq, got {other:?}"),
    };
    let body_parts = match body {
        Region::Seq(v) => v,
        other => panic!("expected body=Seq, got {other:?}"),
    };
    assert_eq!(body_parts.len(), 2, "body: {body_parts:?}");
    let (switch_at, branches) = match &body_parts[1] {
        Region::Switch {
            switch_at,
            branches,
        } => (*switch_at, branches),
        other => panic!("expected Switch in body, got {other:?}"),
    };
    assert_eq!(switch_at, 5);
    assert_eq!(branches.len(), 3);
    // Arm A: Seq([Basic{6..=6}, Term(Break{level:0})]) -- the
    // jump-to-exit bridge's label-only Basic is preserved before the
    // break fires at the leaf single-successor dispatch. (Pre-fix, the
    // top-of-iter is_break short-circuited any block outside the loop
    // body into a bare Term(Break), which lost meaningful Basic content
    // in non-trivial break pads -- see rand_level.)
    let arm_a_parts = match &branches[0] {
        Region::Seq(v) => v,
        other => panic!("expected arm A Seq, got {other:?}"),
    };
    assert_eq!(arm_a_parts.len(), 2);
    assert!(matches!(
        arm_a_parts[0],
        Region::Basic { lower: 6, upper: 6 }
    ));
    assert!(matches!(
        arm_a_parts[1],
        Region::Term(Termination::Break { level: 0 })
    ));
    // Arm B: Seq([Basic{8..=8}, Term(Continue{0})]) -- step-through
    // pushes the bridge label as a Basic, then is_continue emits
    // explicit Continue.
    let arm_b_parts = match &branches[1] {
        Region::Seq(v) => v,
        other => panic!("expected arm B Seq, got {other:?}"),
    };
    assert_eq!(arm_b_parts.len(), 2);
    assert!(matches!(
        arm_b_parts[0],
        Region::Basic { lower: 8, upper: 8 }
    ));
    assert!(matches!(
        arm_b_parts[1],
        Region::Term(Termination::Continue { level: 0 })
    ));
    // Arm C: same shape as arm B with PC 10's label.
    let arm_c_parts = match &branches[2] {
        Region::Seq(v) => v,
        other => panic!("expected arm C Seq, got {other:?}"),
    };
    assert_eq!(arm_c_parts.len(), 2);
    assert!(matches!(
        arm_c_parts[0],
        Region::Basic {
            lower: 10,
            upper: 10
        }
    ));
    assert!(matches!(
        arm_c_parts[1],
        Region::Term(Termination::Continue { level: 0 })
    ));
}

/// `while outer { while middle { while inner { if (x) break_outer; } } }`
/// -- a 3-deep nest where the innermost if jumps past all three loops
/// to the outermost exit. `is_break` from inside the inner body sees
/// `do_break_outer` (the bridge block) outside all three loop bodies
/// and emits `Term(Break { level: 2 })`. This pins the level-2
/// behavior alongside the existing level-1 cross-level-break fixture.
#[test]
fn cross_level_break_three_deep() {
    let r = root_of(
        BytecodeBuilder::new()
            .label("outer_head")
            .load_bool(0, true)
            .branch(0, "outer_body", "outer_exit")
            .label("outer_body")
            .label("middle_head")
            .load_bool(1, true)
            .branch(1, "middle_body", "middle_exit")
            .label("middle_body")
            .label("inner_head")
            .load_bool(2, true)
            .branch(2, "inner_body", "inner_exit")
            .label("inner_body")
            .load_bool(3, true)
            .branch(3, "do_break_outer", "after_inner")
            .label("do_break_outer")
            .jump("outer_exit")
            .label("after_inner")
            .nop()
            .jump("inner_head")
            .label("inner_exit")
            .jump("middle_head")
            .label("middle_exit")
            .jump("outer_head")
            .label("outer_exit")
            .ret(&[]),
    );
    fn has_break_at_level(r: &Region, level: u32) -> bool {
        match r {
            Region::Term(Termination::Break { level: l }) if *l == level => true,
            Region::Seq(parts) => parts.iter().any(|p| has_break_at_level(p, level)),
            Region::If {
                then_branch,
                else_branch,
                ..
            } => has_break_at_level(then_branch, level) || has_break_at_level(else_branch, level),
            Region::Switch { branches, .. } => {
                branches.iter().any(|b| has_break_at_level(b, level))
            }
            Region::While { header, body, .. } => {
                has_break_at_level(header, level) || has_break_at_level(body, level)
            }
            _ => false,
        }
    }
    assert!(
        has_break_at_level(&r, 2),
        "expected Term(Break{{level:2}}) somewhere in: {r:#?}"
    );
}

/// Regression: a Branch arm that points **directly** at the loop header
/// (not via a Jump-only bridge) must surface as `Term(Continue{level:0})`,
/// not be silently structured as a recursive call into the header.
///
/// Pre-fix, `skip_loop_checks` fired on the recursive `structure()`
/// invocation entered from the body's Branch handler -- because
/// `current == start == loop_header && is_continue(loop_stack, current)`
/// is `Some(0)`. The check was originally written for `emit_while`'s
/// header recursion (where suppressing the continue on iter 1 is
/// necessary, since the recursion is *meant* to structure from the
/// loop_header), but it also matched any Branch arm that happened to
/// land on the header, causing a post-dom cycle:
/// `structure(latch, stop=exit)` -> `structure(header, stop=exit)` ->
/// dispatch If at header -> `structure(latch, stop=exit)` -> ... ->
/// `RecursionLimit { depth: 2049 }`.
///
/// The fix gates `skip_loop_checks` on `body_of_while=true` so only
/// `emit_while`'s recursions get the first-iteration skip; a Branch
/// arm targeting the header correctly emits a `Term(Continue)`.
///
/// `move_stl::skip_list_u128::rand_level` is the wild-caught
/// reproducer (16 lines of Move source). This fixture is the minimal
/// structural skeleton: a simple `while (c1) { ...; if (c2) break }`
/// where the implicit else-branch of `if (c2)` falls *directly* back
/// to the loop header instead of via an intermediate Jump block.
#[test]
fn branch_arm_targets_loop_header_directly() {
    // PC 0: label "head"
    // PC 1: load_bool 0, true
    // PC 2: branch 0 -> "body" / "exit"
    // PC 3: label "body"
    // PC 4: nop
    // PC 5: load_bool 1, true
    // PC 6: branch 1 -> "exit" / "head"   <-- else arm points AT the loop header
    // PC 7: label "exit"
    // PC 8: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "body", "exit")
            .label("body")
            .nop()
            .load_bool(1, true)
            .branch(1, "exit", "head")
            .label("exit")
            .ret(&[]),
    );
    // Top-level shape: Seq([While, Basic{exit}, Term(Return)]).
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
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
    // Body: Seq([Basic{3,5}, If{ cond_at: 6, ..., else: Term(Continue{0}) }]).
    let body_parts = match body {
        Region::Seq(v) => v,
        other => panic!("expected body=Seq, got {other:?}"),
    };
    assert_eq!(body_parts.len(), 2, "body parts: {body_parts:?}");
    assert!(matches!(
        body_parts[0],
        Region::Basic { lower: 3, upper: 5 }
    ));
    let (inner_cond_at, else_branch) = match &body_parts[1] {
        Region::If {
            cond_at,
            else_branch,
            ..
        } => (*cond_at, else_branch.as_ref()),
        other => panic!("expected inner If, got {other:?}"),
    };
    assert_eq!(inner_cond_at, 6);
    // The else arm of the inner If -- pre-fix, this would have caused
    // unbounded recursion; post-fix it's a direct innermost continue.
    assert!(
        matches!(
            *else_branch,
            Region::Term(Termination::Continue { level: 0 })
        ),
        "expected else=Term(Continue{{level:0}}), got {else_branch:?}"
    );
}

/// Regression: a while body whose outer If's then-arm contains a
/// nested If with two distinct break sites (each carrying its own
/// pre-Jump Basic) must preserve all four leaf Basics + their Breaks
/// in stage 1's structured CFG. Pre-fix, the top-of-iter `is_break`
/// short-circuit fired on the outer-then block (which sits outside
/// the natural-loop body, since both its arms break out of the loop)
/// and collapsed the entire nested If + four assignments into a single
/// `Term(Break)` -- losing every assignment.
///
/// `move_stl::skip_list_u128::rand_level` is the wild-caught case:
/// `if (level > list.level) { if (level >= list.max_level) {
/// level = list.max_level; break } else { level = list.level + 1;
/// break } }` becomes structurally invisible to the rest of the
/// pipeline.
///
/// Post-fix: descend into the outer-then block normally, dispatch its
/// Branch, structure each inner arm. The leaf single-successor
/// dispatch emits `Term(Break)` when the fall-through target is
/// outside the loop body, preserving the pre-Jump Basic in each arm.
#[test]
fn nested_if_in_outer_then_preserves_break_assignments() {
    // PC  0: label "head"
    // PC  1: load_bool 0, true
    // PC  2: branch 0 -> "body" / "exit"
    // PC  3: label "body"
    // PC  4: nop                                  -- some body work
    // PC  5: load_bool 1, true
    // PC  6: branch 1 -> "outer_then" / "head"    -- if (cond1) goto outer_then else continue
    // PC  7: label "outer_then"                   -- outside natural-loop body
    // PC  8: load_bool 2, true
    // PC  9: branch 2 -> "inner_then" / "inner_else"   -- nested if
    // PC 10: label "inner_then"
    // PC 11: nop                                  -- "level = list.max_level"
    // PC 12: jump "exit"
    // PC 13: label "inner_else"
    // PC 14: nop                                  -- "level = list.level + 1"
    // PC 15: jump "exit"
    // PC 16: label "exit"
    // PC 17: ret []
    let r = root_of(
        BytecodeBuilder::new()
            .label("head")
            .load_bool(0, true)
            .branch(0, "body", "exit")
            .label("body")
            .nop()
            .load_bool(1, true)
            .branch(1, "outer_then", "head")
            .label("outer_then")
            .load_bool(2, true)
            .branch(2, "inner_then", "inner_else")
            .label("inner_then")
            .nop()
            .jump("exit")
            .label("inner_else")
            .nop()
            .jump("exit")
            .label("exit")
            .ret(&[]),
    );
    // Drill into the While's body, then the outer If's then-arm,
    // then the inner If's both arms.
    let parts = match r {
        Region::Seq(parts) => parts,
        other => panic!("expected Seq, got {other:?}"),
    };
    let body = match &parts[0] {
        Region::While { body, .. } => body.as_ref(),
        other => panic!("expected While, got {other:?}"),
    };
    let body_parts = match body {
        Region::Seq(v) => v,
        other => panic!("expected body=Seq, got {other:?}"),
    };
    // body = Seq([Basic{3,5}, If{cond_at=6, then=<outer-then>, else=Continue}]).
    assert_eq!(body_parts.len(), 2);
    let (outer_then, outer_else) = match &body_parts[1] {
        Region::If {
            then_branch,
            else_branch,
            ..
        } => (then_branch.as_ref(), else_branch.as_ref()),
        other => panic!("expected outer If, got {other:?}"),
    };
    assert!(
        matches!(outer_else, Region::Term(Termination::Continue { level: 0 })),
        "outer else should be Continue{{0}}, got {outer_else:?}"
    );
    // outer_then = Seq([Basic{7,8}, InnerIf{cond_at=9, then=<...>, else=<...>}]).
    let outer_then_parts = match outer_then {
        Region::Seq(v) => v,
        other => panic!("expected outer_then=Seq (pre-fix collapsed to bare Break), got {other:?}"),
    };
    assert_eq!(
        outer_then_parts.len(),
        2,
        "outer_then: {outer_then_parts:?}"
    );
    assert!(matches!(
        outer_then_parts[0],
        Region::Basic { lower: 7, upper: 8 }
    ));
    let (inner_then, inner_else) = match &outer_then_parts[1] {
        Region::If {
            cond_at,
            then_branch,
            else_branch,
        } => {
            assert_eq!(*cond_at, 9);
            (then_branch.as_ref(), else_branch.as_ref())
        }
        other => panic!("expected inner If, got {other:?}"),
    };
    // Each inner arm = Seq([Basic{<pre-Jump>}, Term(Break{level:0})]),
    // preserving its pre-Jump assignment.
    let inner_then_parts = match inner_then {
        Region::Seq(v) => v,
        other => panic!("expected inner_then=Seq, got {other:?}"),
    };
    assert_eq!(inner_then_parts.len(), 2);
    assert!(matches!(
        inner_then_parts[0],
        Region::Basic {
            lower: 10,
            upper: 11
        }
    ));
    assert!(matches!(
        inner_then_parts[1],
        Region::Term(Termination::Break { level: 0 })
    ));
    let inner_else_parts = match inner_else {
        Region::Seq(v) => v,
        other => panic!("expected inner_else=Seq, got {other:?}"),
    };
    assert_eq!(inner_else_parts.len(), 2);
    assert!(matches!(
        inner_else_parts[0],
        Region::Basic {
            lower: 13,
            upper: 14
        }
    ));
    assert!(matches!(
        inner_else_parts[1],
        Region::Term(Termination::Break { level: 0 })
    ));
}
