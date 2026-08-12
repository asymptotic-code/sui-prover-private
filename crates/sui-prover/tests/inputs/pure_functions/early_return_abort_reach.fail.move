/// The other direction of `early_return_abort_guard.ok`: an abort the source
/// CAN reach must not disappear.
///
/// The early `return` here guards nothing — `a != 0` says nothing about
/// `a >= b` — so `a - b` genuinely underflows and both spellings must report
/// it. A translation that lost the obligation for the early-`return` form
/// would be a false `no_abort` foundation for everything quantified over it.
module 0x42::early_return_abort_reach;

#[spec_only]
use prover::prover::ensures;

#[spec_only, ext(pure)]
fun unguarded_sub_early(a: u64, b: u64): u64 {
    if (a == 0) {
        return 0
    };
    a - b
}

#[spec_only, ext(pure)]
fun unguarded_sub_nested(a: u64, b: u64): u64 {
    if (a == 0) {
        0
    } else {
        a - b
    }
}

public fun pick(a: u64, b: u64): u64 {
    if (a == 0) 0 else a - b
}

#[spec(prove)]
fun pick_spec(a: u64, b: u64): u64 {
    let r = pick(a, b);
    ensures(r == unguarded_sub_early(a, b));
    ensures(r == unguarded_sub_nested(a, b));
    r
}
