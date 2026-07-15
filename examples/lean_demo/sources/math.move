module lean_demo::math;

#[spec_only]
use prover::prover::{asserts, ensures, implies, requires};

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

const EInsufficientBalance: u64 = 0;
const EBalanceOverflow: u64 = 1;

public struct Balance has store {
    value: u64,
}

public fun withdraw(balance: &mut Balance, amount: u64): u64 {
    assert!(amount <= balance.value, EInsufficientBalance);
    balance.value = balance.value - amount;
    amount
}

#[spec(prove)]
fun withdraw_spec(balance: &mut Balance, amount: u64): u64 {
    let balance_before = balance.value;
    asserts(amount <= balance_before);
    let result = withdraw(balance, amount);
    ensures(result == amount);
    ensures(balance.value == balance_before - amount);
    result
}

public fun transfer(from: &mut Balance, to: &mut Balance, amount: u64) {
    assert!(to.value <= std::u64::max_value!() - amount, EBalanceOverflow);
    let withdrawn = withdraw(from, amount);
    to.value = to.value + withdrawn;
}

#[spec(prove)]
fun transfer_spec(from: &mut Balance, to: &mut Balance, amount: u64) {
    let from_before = from.value;
    let to_before = to.value;
    asserts(amount <= from_before);
    asserts(to_before <= std::u64::max_value!() - amount);
    transfer(from, to, amount);
    ensures(from.value == from_before - amount);
    ensures(to.value == to_before + amount);
    ensures(
        (from.value as u128) + (to.value as u128) == (from_before as u128) + (to_before as u128),
    );
}
