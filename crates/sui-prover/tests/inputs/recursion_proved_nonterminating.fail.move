module 0x42::foo;

#[mode(spec), ext(spec_only)]
use prover::prover::ensures;

// Proving a spec that cuts its own recursion assumes the spec to prove it;
// with no termination check this "proves" a contradiction.
public fun spin(n: u64): u64 {
    spin(n)
}

#[mode(spec), ext(spec(prove))]
public fun spin_spec(n: u64): u64 {
    let result = spin(n);
    ensures(result == 0);
    ensures(result == 1);
    result
}
