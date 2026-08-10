/// Regression: a pure helper written in early-return style must keep the code
/// after the early return.
///
/// `conditional_merge_insertion` used to emit its pending if-then-else merges
/// before merging the multiple `Ret`s, which shifted every code offset the
/// return-merge walk was still indexing with. The walk then failed to find the
/// tail's `Ret`, substituted the fallthrough, and the helper collapsed to the
/// early-returned constant -- with the real predicate computed into a dead
/// temporary. Any `requires`/`ensures` built on such a helper contributed no
/// constraint, so specs verified vacuously.
///
/// The generated Boogie is snapshotted below: `in_range$pure` must contain the
/// real `<=` comparison, not a constant.
module 0x42::pure_boogie_early_return_tail;

#[spec_only]
use prover::prover::{ensures, requires};

/// Early-return spelling -- the shape that regressed.
#[ext(pure)]
fun in_range(x: u64, lo: u64, hi: u64): bool {
    if (lo == 0) {
        return true
    };
    let mut bound = hi;
    if (hi > lo) {
        bound = hi - lo;
    };
    x <= bound
}

/// Control: the same predicate spelled without an early return. This is the
/// workaround shape, and it must translate to the same logic.
#[ext(pure)]
fun in_range_nested(x: u64, lo: u64, hi: u64): bool {
    if (lo == 0) {
        true
    } else {
        let bound = if (hi > lo) { hi - lo } else { hi };
        x <= bound
    }
}

/// Early-return helper used in `requires` position. `fits(x, cap)` is exactly
/// `x <= cap`: when `x == 0` it short-circuits to true, and otherwise
/// `x <= cap - 1 || x == cap`.
#[ext(pure)]
fun fits(x: u64, cap: u64): bool {
    if (x == 0) {
        return true
    };
    let mut limit = cap;
    if (cap > 0) {
        limit = cap - 1;
    };
    x <= limit || x == cap
}

public fun call_in_range(x: u64, lo: u64, hi: u64): bool {
    in_range(x, lo, hi)
}

public fun call_in_range_nested(x: u64, lo: u64, hi: u64): bool {
    in_range_nested(x, lo, hi)
}

public fun sub_capped(x: u64, cap: u64): u64 {
    cap - x
}

/// The catcher: `in_range(50, 10, 20)` is `50 <= 20 - 10`, i.e. false. A helper
/// that collapsed to a constant `true` fails this `ensures` instead of
/// satisfying it trivially.
#[spec(prove)]
fun test_in_range_false(): bool {
    let r = call_in_range(50, 10, 20);
    ensures(r == false);
    r
}

#[spec(prove)]
fun test_in_range_true(): bool {
    let r = call_in_range(5, 10, 20);
    ensures(r == true);
    r
}

/// The early return itself still has to work.
#[spec(prove)]
fun test_in_range_early(): bool {
    let r = call_in_range(50, 0, 20);
    ensures(r == true);
    r
}

/// The control spelling must agree with the early-return one.
#[spec(prove)]
fun test_in_range_nested_false(): bool {
    let r = call_in_range_nested(50, 10, 20);
    ensures(r == false);
    r
}

/// `requires` position: without the real `x <= cap` constraint, `cap - x`
/// underflows and this spec fails on an abort instead of verifying.
#[spec(prove)]
fun sub_capped_spec(x: u64, cap: u64): u64 {
    requires(fits(x, cap));
    let r = sub_capped(x, cap);
    ensures(r == cap - x);
    r
}
