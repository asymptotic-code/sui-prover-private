/// An early `return` that GUARDS downstream arithmetic must translate to the
/// same abort obligation as the identical nested if/else spelling.
///
/// `guarded_sub_early` and `guarded_sub_nested` are the same function written
/// two ways. Neither can reach `a - b` with `a <= b`, so neither aborts, and
/// `funs_abort_check` must accept both.
module 0x42::early_return_abort_guard;

#[mode(spec), ext(spec_only)]
use prover::prover::ensures;

#[mode(spec), ext(spec_only, pure)]
fun guarded_sub_early(a: u64, b: u64): u64 {
    if (a <= b) {
        return 0
    };
    a - b
}

#[mode(spec), ext(spec_only, pure)]
fun guarded_sub_nested(a: u64, b: u64): u64 {
    if (a <= b) {
        0
    } else {
        a - b
    }
}

public fun diff(a: u64, b: u64): u64 {
    if (a <= b) 0 else a - b
}

#[mode(spec), ext(spec(prove))]
fun diff_spec(a: u64, b: u64): u64 {
    let r = diff(a, b);
    ensures(r == guarded_sub_early(a, b));
    ensures(r == guarded_sub_nested(a, b));
    r
}
