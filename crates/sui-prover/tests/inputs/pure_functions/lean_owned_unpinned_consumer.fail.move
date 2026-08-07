/// A Boogie-verified spec whose precondition names a Lean-owned pure helper.
/// The helper is uninterpreted here, so the `requires` constrains nothing and
/// the spec would silently prove less than it reads. That is an error, not a
/// warning: the fix is to pin the spec to the same backend as the helper.
module 0x42::lean_owned_unpinned_consumer;

#[spec_only]
use prover::prover::{requires, ensures};

#[spec_only, ext(pure, backend=b"lean")]
fun bounded(x: u64, bound: u64): bool {
    x <= bound
}

public fun double(x: u64): u64 {
    x * 2
}

#[spec(prove)]
fun double_spec(x: u64): u64 {
    requires(bounded(x, 100));
    let result = double(x);
    ensures(result == x * 2);
    result
}
