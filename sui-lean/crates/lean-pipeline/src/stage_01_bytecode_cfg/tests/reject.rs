//! Rejection-case fixtures.
//!
//! Hand-constructing reject cases is tricky because Move bytecode rules
//! constrain block boundaries: a block ends only at branch *destinations*
//! or at end-of-code, so "unreachable trap labels" don't materialize as
//! their own blocks. The fixture below puts a guarded loop behind a
//! `Branch` so the loop's natural-loop block has a `Jump` terminator
//! without an in-loop / out-of-loop branch -- the structural shape that
//! Move's `loop { ... }` produces.

use super::cfg_from;
use super::BytecodeBuilder;
use super::Stage1Error;

/// Move-style `if cond { abort } else { loop { ... } }` wraps a
/// `loop {}` (no break) in a guard so the `loop` block has its own
/// natural loop and an unreachable abort terminator at the function
/// exit. The natural loop's header has a `Jump` terminator (not a
/// `Branch`), so `find_cond_at` can't find one with an in-loop /
/// out-of-loop arm, and the structurer rejects with
/// `UnsupportedLoop`.
#[test]
fn loop_with_no_break_rejects() {
    // PC 0: load_bool 0, true        (dummy guard)
    // PC 1: branch 0 -> "head" / "trap"
    // PC 2: label "head"
    // PC 3: nop
    // PC 4: jump "head"              (back-edge to itself)
    // PC 5: label "trap"
    // PC 6: abort 0                  (terminates the function)
    let err = cfg_from(
        BytecodeBuilder::new()
            .load_bool(0, true)
            .branch(0, "head", "trap")
            .label("head")
            .nop()
            .jump("head")
            .label("trap")
            .abort(0),
    )
    .expect_err("loop with no break should be UnsupportedLoop");
    assert!(
        matches!(err, Stage1Error::UnsupportedLoop { .. }),
        "expected UnsupportedLoop, got {err:?}"
    );
}
