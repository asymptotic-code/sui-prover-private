module 0x42::occupancy;
use sui::dynamic_field as df;
use sui::object;
use prover::prover::{asserts, ensures};

public fun insert(uid: &mut UID, key: u64, value: u64) {
    df::add(uid, key, value);
}

#[mode(spec), ext(spec(prove))]
fun insert_spec(uid: &mut UID, key: u64, value: u64) {
    asserts(!df::exists<u64>(uid, key));
    insert(uid, key, value);
    ensures(df::exists<u64>(uid, key));
    ensures(df::exists_with_type<u64, u64>(uid, key));
    ensures(*df::borrow<u64, u64>(uid, key) == value);
}

public fun replace_type(uid: &mut UID, key: u64, value: bool): u64 {
    let previous = df::remove<u64, u64>(uid, key);
    df::add(uid, key, value);
    previous
}

#[mode(spec), ext(spec(prove))]
fun replace_type_spec(uid: &mut UID, key: u64, value: bool): u64 {
    asserts(df::exists_with_type<u64, u64>(uid, key));
    let previous = *df::borrow<u64, u64>(uid, key);
    let result = replace_type(uid, key, value);
    ensures(result == previous);
    ensures(df::exists<u64>(uid, key));
    ensures(!df::exists_with_type<u64, u64>(uid, key));
    ensures(df::exists_with_type<u64, bool>(uid, key));
    ensures(*df::borrow<u64, bool>(uid, key) == value);
    result
}

public fun fresh(ctx: &mut TxContext): bool {
    let mut uid = object::new(ctx);
    let before = df::exists<u64>(&uid, 7);
    df::add(&mut uid, 7u64, true);
    let removed = df::remove<u64, bool>(&mut uid, 7);
    let after = df::exists<u64>(&uid, 7);
    object::delete(uid);
    !before && removed && !after
}

#[mode(spec), ext(spec(prove))]
fun fresh_spec(ctx: &mut TxContext): bool {
    let result = fresh(ctx);
    ensures(!result);
    result
}
