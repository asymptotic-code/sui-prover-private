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

// Boundary values through the trusted contracts: all true, all proven.
#[mode(spec), ext(spec(prove))]
fun count_zero_one_max() {
    let zero = count(0);
    let one = count(1);
    let max = count(1000);
    ensures(zero == 0);
    ensures(one == 1);
    ensures(max == 1000);
}

#[mode(spec), ext(spec(prove))]
fun count_n_and_n_plus_one(n: u64) {
    requires(n < 1000);
    let a = count(n);
    let b = count(n + 1);
    ensures(b == a + 1);
    ensures(a < b);
}

#[mode(spec), ext(spec(prove))]
public fun step_spec(n: u64): u64 {
    requires(n < 1000);
    let result = step(n);
    ensures(result == 1);
    result
}

#[mode(spec), ext(spec(prove))]
fun parity_zero_one() {
    let e0 = is_even(0);
    let o0 = is_odd(0);
    let e1 = is_even(1);
    let o1 = is_odd(1);
    ensures(e0);
    ensures(!o0);
    ensures(!e1);
    ensures(o1);
}

#[mode(spec), ext(spec(prove))]
public fun flips_spec(n: u64): bool {
    requires(n < 18446744073709551615);
    let result = flips(n);
    ensures(result);
    result
}
