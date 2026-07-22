module backend_comparison::boogie_only;

#[spec_only]
use prover::prover::ensures;

public fun identity(value: u64): u64 {
    value
}

/// This specification is deliberately assigned only to Boogie. The Lean
/// backend must not generate a proof obligation for it.
#[ext(backend=b"boogie")]
#[spec(prove)]
fun identity_spec(value: u64): u64 {
    let result = identity(value);
    ensures(result == value);
    result
}
