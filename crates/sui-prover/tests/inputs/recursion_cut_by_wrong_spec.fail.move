module 0x42::foo;

#[mode(spec), ext(spec_only)]
use prover::prover::{requires, ensures};

// The recursion is cut by a contract, but the contract is false: the
// induction must not make it verify.
public fun count(n: u64): u64 {
    if (n == 0) { 0 } else { 1 + count(n - 1) }
}

#[mode(spec), ext(spec(prove))]
public fun count_spec(n: u64): u64 {
    requires(n <= 1000);
    let result = count(n);
    ensures(result == n + 1);
    result
}
