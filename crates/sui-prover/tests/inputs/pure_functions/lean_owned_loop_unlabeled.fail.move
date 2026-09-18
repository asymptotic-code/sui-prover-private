/// Regression guard for `lean_owned_loop.ok.move`: without the backend label
/// the very same helper is Boogie-owned and still has to satisfy the pure
/// function body restrictions.
module 0x42::lean_owned_loop_unlabeled;

#[mode(spec), ext(spec_only)]
use prover::prover::{requires, ensures};

fun count_up(n: u64): u64 {
    let mut i = 0;
    while (i < n) {
        i = i + 1;
    };
    i
}

#[mode(spec), ext(spec_only, pure)]
fun counts_up_to(n: u64, bound: u64): bool {
    count_up(n) <= bound
}

public fun double(x: u64): u64 {
    x * 2
}

#[mode(spec), ext(spec(prove))]
fun double_spec(x: u64): u64 {
    requires(counts_up_to(x, 100));
    requires(x <= 100);
    let result = double(x);
    ensures(result == x * 2);
    result
}
