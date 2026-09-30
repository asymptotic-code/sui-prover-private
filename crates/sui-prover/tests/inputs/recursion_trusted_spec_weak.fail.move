module 0x42::foo;

#[mode(spec), ext(spec_only)]
use prover::prover::{requires, ensures};

// The trusted spec says too little for the caller: the caller must fail, not
// see the real body.
public fun count(n: u64): u64 {
    if (n == 0) { 0 } else { 1 + count(n - 1) }
}

public fun double(n: u64): u64 {
    count(n) * 2
}

#[mode(spec), ext(spec)]
public fun count_spec(n: u64): u64 {
    requires(n <= 1000);
    let result = count(n);
    ensures(result <= n);
    result
}

#[mode(spec), ext(spec(prove))]
public fun double_spec(n: u64): u64 {
    requires(n <= 500);
    let result = double(n);
    ensures(result == 2 * n);
    result
}
