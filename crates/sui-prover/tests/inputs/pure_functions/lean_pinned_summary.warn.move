/// A Boogie-verified spec whose target calls a function whose own spec is
/// pinned to Lean. Only that one summary is missing here, which weakens the
/// proof rather than voiding it, so this is a warning and verification runs.
module 0x42::lean_pinned_summary;

#[mode(spec), ext(spec_only)]
use prover::prover::ensures;

public fun is_zero(x: u64): bool {
    x == 0
}

#[mode(spec), ext(spec(prove), backend=b"lean")]
fun is_zero_spec(x: u64): bool {
    let result = is_zero(x);
    ensures(result == (x == 0));
    result
}

public fun zero_or_one(x: u64): u64 {
    if (is_zero(x)) 0 else 1
}

#[mode(spec), ext(spec(prove))]
fun zero_or_one_spec(x: u64): u64 {
    let result = zero_or_one(x);
    ensures(result <= 1);
    result
}
