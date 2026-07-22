module backend_comparison::basic;

#[spec_only]
use prover::prover::{asserts, ensures};
use std::option;

/// Return the larger of two values.
public fun max(a: u64, b: u64): u64 {
    if (a >= b) a else b
}

/// Increment a value. Move aborts when `value` is already `u64::MAX`.
public fun increment(value: u64): u64 {
    value + 1
}

/// Exercise a standard-library datatype shared by both translations.
public fun wrapped_value_is_some(value: u64): bool {
    option::some(value).is_some()
}

#[ext(backend=b"both")]
#[spec(prove)]
fun max_spec(a: u64, b: u64): u64 {
    let result = max(a, b);
    ensures(result >= a);
    ensures(result >= b);
    ensures(result == a || result == b);
    result
}

#[spec(prove)]
fun increment_spec(value: u64): u64 {
    asserts(value < std::u64::max_value!());
    let result = increment(value);
    ensures(result == value + 1);
    ensures(result > value);
    result
}

#[spec(prove)]
fun wrapped_value_is_some_spec(value: u64): bool {
    let result = wrapped_value_is_some(value);
    ensures(result);
    result
}
