module backend_comparison::boogie_only;

#[mode(spec), ext(spec_only)]
use prover::prover::ensures;

public fun identity(value: u64): u64 {
    value
}

/// This specification is deliberately assigned only to Boogie. The Lean
/// backend must not generate a proof obligation for it.
#[mode(spec), ext(spec(prove), backend=b"boogie")]
fun identity_spec(value: u64): u64 {
    let result = identity(value);
    ensures(result == value);
    result
}
