module 0x42::foo;

#[mode(spec), ext(spec_only)]
use prover::prover::{requires, ensures};

// Recursion cut by trusted specs. Every caller below is proven normally
// against their contracts.
public fun count(n: u64): u64 {
    if (n == 0) { 0 } else { 1 + count(n - 1) }
}

public fun is_even(n: u64): bool {
    if (n == 0) { true } else { is_odd(n - 1) }
}

public fun is_odd(n: u64): bool {
    if (n == 0) { false } else { is_even(n - 1) }
}

public fun double(n: u64): u64 {
    count(n) * 2
}

public fun sum_two(a: u64, b: u64): u64 {
    count(a) + count(b)
}

public fun withdraw(balance: u64, n: u64): u64 {
    balance - count(n)
}

public fun double_is_even(n: u64): bool {
    is_even(double(n))
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

#[mode(spec), ext(spec(prove))]
public fun double_spec(n: u64): u64 {
    requires(n <= 500);
    let result = double(n);
    ensures(result == 2 * n);
    result
}

#[mode(spec), ext(spec(prove))]
public fun sum_two_spec(a: u64, b: u64): u64 {
    requires(a <= 1000);
    requires(b <= 1000);
    let result = sum_two(a, b);
    ensures(result == a + b);
    result
}

#[mode(spec), ext(spec(prove))]
public fun withdraw_spec(balance: u64, n: u64): u64 {
    requires(n <= 1000);
    requires(n <= balance);
    let result = withdraw(balance, n);
    ensures(result == balance - n);
    result
}

#[mode(spec), ext(spec(prove))]
public fun double_is_even_spec(n: u64): bool {
    requires(n <= 500);
    let result = double_is_even(n);
    ensures(result);
    result
}
