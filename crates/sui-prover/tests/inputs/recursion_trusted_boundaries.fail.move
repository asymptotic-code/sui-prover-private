module 0x42::foo;

#[mode(spec), ext(spec_only)]
use prover::prover::{requires, ensures};

public fun count(n: u64): u64 {
    if (n == 0) { 0 } else { 1 + count(n - 1) }
}

public fun is_even(n: u64): bool {
    if (n == 0) { true } else { is_odd(n - 1) }
}

public fun is_odd(n: u64): bool {
    if (n == 0) { false } else { is_even(n - 1) }
}

// count(n + 1) - count(n)
public fun step(n: u64): u64 {
    count(n + 1) - count(n)
}

// Parity flips between n and n + 1.
public fun flips(n: u64): bool {
    is_even(n) != is_even(n + 1)
}

#[mode(spec), ext(spec)]
public fun count_spec(n: u64): u64 {
    requires(n <= 1000);
    let result = count(n);
    ensures(result == n);
    result
}

#[mode(spec), ext(spec)]
public fun is_even_spec(n: u64): bool {
    let result = is_even(n);
    ensures(result == (n % 2 == 0));
    result
}

#[mode(spec), ext(spec)]
public fun is_odd_spec(n: u64): bool {
    let result = is_odd(n);
    ensures(result == (n % 2 == 1));
    result
}

// The same boundaries with false claims: each must fail.
#[mode(spec), ext(spec(prove))]
fun count_zero_is_one() {
    let zero = count(0);
    ensures(zero == 1);
}

#[mode(spec), ext(spec(prove))]
fun count_one_is_zero() {
    let one = count(1);
    ensures(one == 0);
}

#[mode(spec), ext(spec(prove))]
fun count_n_equals_n_plus_one(n: u64) {
    requires(n < 1000);
    let a = count(n);
    let b = count(n + 1);
    ensures(a == b);
}

// Outside the trusted spec's `requires` (n <= 1000).
#[mode(spec), ext(spec(prove))]
fun count_past_max() {
    let r = count(1001);
    ensures(r == 1001);
}

#[mode(spec), ext(spec(prove))]
public fun step_spec(n: u64): u64 {
    requires(n < 1000);
    let result = step(n);
    ensures(result == 0);
    result
}

#[mode(spec), ext(spec(prove))]
fun parity_one_is_even() {
    let e1 = is_even(1);
    ensures(e1);
}

#[mode(spec), ext(spec(prove))]
public fun flips_spec(n: u64): bool {
    requires(n < 18446744073709551615);
    let result = flips(n);
    ensures(!result);
    result
}
