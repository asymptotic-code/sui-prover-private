/// A lean-owned pure helper that probes a copy through a mutable reference.
/// Boogie cannot model such a body as a function, but it never has to: the
/// helper is emitted as an uninterpreted declaration.
module 0x42::lean_owned_mut_ref;

#[spec_only]
use prover::prover::{requires, ensures, val, drop};

#[spec_only, ext(pure, backend=b"lean")]
fun grows_by_one(v: &vector<u64>): bool {
    let old_len = v.length();
    let mut probe = val(v);
    probe.push_back(0);
    let new_len = probe.length();
    drop(probe);
    new_len == old_len + 1
}

public fun first_or_zero(v: &vector<u64>): u64 {
    if (v.is_empty()) 0 else v[0]
}

#[spec(prove)]
fun first_or_zero_spec(v: &vector<u64>): u64 {
    requires(grows_by_one(v));
    let result = first_or_zero(v);
    ensures(result == if (v.is_empty()) 0 else v[0]);
    result
}
