/// A pure helper whose definition belongs to the Lean backend. Under Boogie it
/// is an uninterpreted function: its body is never modelled, so the loop is not
/// an error and `count_up` is not dragged into the pure pipeline.
///
/// Only the Lean-pinned spec may name it -- a Boogie spec that did would get
/// no content out of the condition, which `check_backend_mixing` rejects.
module 0x42::lean_owned_loop;

#[spec_only]
use prover::prover::{requires, ensures};

fun count_up(n: u64): u64 {
    let mut i = 0;
    while (i < n) {
        i = i + 1;
    };
    i
}

#[spec_only, ext(pure, backend=b"lean")]
fun counts_up_to(n: u64, bound: u64): bool {
    count_up(n) <= bound
}

public fun double(x: u64): u64 {
    x * 2
}

#[ext(backend=b"lean")]
#[spec(prove)]
fun double_spec(x: u64): u64 {
    requires(counts_up_to(x, 100));
    requires(x <= 100);
    let result = double(x);
    ensures(result == x * 2);
    result
}

public fun triple(x: u64): u64 {
    x * 3
}

#[spec(prove)]
fun triple_spec(x: u64): u64 {
    requires(x <= 100);
    let result = triple(x);
    ensures(result == x * 3);
    result
}
