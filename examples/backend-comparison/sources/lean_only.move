module backend_comparison::lean_only;

#[spec_only]
use prover::prover::ensures;

/// A square is never congruent to 2 modulo 4.
///
/// The input is widened before multiplication, so the computation cannot
/// overflow: `u8::MAX² < u64::MAX`.
public fun square_mod_four(value: u8): u64 {
    let wide = value as u64;
    (wide * wide) % 4
}

#[ext(backend=b"lean")]
#[spec(prove)]
fun square_mod_four_spec(value: u8): u64 {
    let result = square_mod_four(value);
    ensures(result != 2);
    result
}
