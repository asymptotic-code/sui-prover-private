module lean_demo::math;

#[spec_only]
use prover::prover::{ensures, implies, requires};

public fun max(a: u64, b: u64): u64 {
    if (a >= b) a else b
}

#[spec(prove)]
fun max_spec(a: u64, b: u64): u64 {
    let result = max(a, b);
    ensures(result >= a);
    ensures(result >= b);
    ensures(result == a || result == b);
    result
}

public fun clamp(value: u64, low: u64, high: u64): u64 {
    if (value < low) {
        low
    } else if (value > high) {
        high
    } else {
        value
    }
}

#[spec(prove)]
fun clamp_spec(value: u64, low: u64, high: u64): u64 {
    requires(low <= high);
    let result = clamp(value, low, high);
    ensures(result >= low);
    ensures(result <= high);
    ensures(result == low || result == value || result == high);
    result
}

public fun distance(a: u64, b: u64): u64 {
    if (a >= b) {
        a - b
    } else {
        b - a
    }
}

#[spec(prove)]
fun distance_spec(a: u64, b: u64): u64 {
    let result = distance(a, b);
    ensures(result <= a || result <= b);
    ensures(implies(a == b, result == 0));
    ensures(implies(result == 0, a == b));
    result
}
