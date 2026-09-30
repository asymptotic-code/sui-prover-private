module 0x42::foo;

#[mode(spec), ext(spec_only)]
use prover::prover::ensures;

// Mutual recursion cut by `is_even_spec` / `is_odd_spec`, both proved: each
// proof would assume the other spec, and so, through the recursion, itself.

public fun is_even(n: u64): bool {
    if (n == 0) { true } else { is_odd(n - 1) }
}

public fun is_odd(n: u64): bool {
    if (n == 0) { false } else { is_even(n - 1) }
}

#[mode(spec), ext(spec(prove))]
public fun is_even_spec(n: u64): bool {
    let result = is_even(n);
    ensures(result == (n % 2 == 0));
    result
}

#[mode(spec), ext(spec(prove))]
public fun is_odd_spec(n: u64): bool {
    let result = is_odd(n);
    ensures(result == (n % 2 == 1));
    result
}
