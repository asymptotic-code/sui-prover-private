/// A quantifier body declared `#[ext(no_abort)]` rather than `#[ext(pure)]`.
///
/// `validate_function_pattern_requirements` admits either kind as the body of a
/// `forall!`, and the translation of the quantifier always emits the body's
/// `$pure` name. The `$pure` DECLARATION, though, is only emitted for pure
/// functions, pure callees and axiom functions, so a `no_abort` body that no
/// pure function happens to reach was referenced and never declared -- Boogie
/// rejected the whole program with "use of undeclared function".
///
/// Nothing here is reachable from an `#[ext(pure)]` function, which is what
/// keeps `entry_within_cap` out of the pure-callee closure.
module 0x42::quantifiers_no_abort_body;

#[spec_only]
use prover::prover::{ensures, requires, forall};

public struct Registry has copy, drop {
    cap: u64,
}

#[spec_only, ext(no_abort)]
fun entry_within_cap(x: &u64, r: &Registry): bool {
    r.cap == 0 || *x <= r.cap
}

#[spec_only, ext(no_abort)]
fun all_entries_within_cap(r: &Registry): bool {
    forall!<u64>(|x| entry_within_cap(x, r))
}

public fun cap(r: &Registry): u64 {
    r.cap
}

#[spec(prove)]
fun cap_spec(r: &Registry): u64 {
    requires(all_entries_within_cap(r));
    let result = cap(r);
    ensures(result == r.cap);
    result
}
