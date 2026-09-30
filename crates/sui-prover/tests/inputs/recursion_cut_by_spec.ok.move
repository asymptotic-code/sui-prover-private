module 0x42::foo;

#[mode(spec), ext(spec_only)]
use prover::prover::{requires, ensures};

// Recursive, but every recursive call is replaced by the contract of
// `count_spec`: the call graph has no inlined cycle, and the recursive use of
// the contract is nested inside `count`'s own execution (induction).
public fun count(n: u64): u64 {
    if (n == 0) { 0 } else { 1 + count(n - 1) }
}

public fun twice(n: u64): u64 {
    count(n) + count(n)
}

#[mode(spec), ext(spec(prove))]
public fun count_spec(n: u64): u64 {
    requires(n <= 1000);
    let result = count(n);
    ensures(result == n);
    result
}

#[mode(spec), ext(spec(prove))]
public fun twice_spec(n: u64): u64 {
    requires(n <= 1000);
    let result = twice(n);
    ensures(result == 2 * n);
    result
}
