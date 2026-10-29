module 0x42::occupancy;
use sui::dynamic_field as df;
use prover::prover::{requires, ensures};

public fun insert(uid: &mut UID, key: u64) {
    df::add(uid, key, true);
}

#[mode(spec), ext(spec(prove))]
fun insert_spec(uid: &mut UID, key: u64) {
    requires(!df::exists_with_type<u64, bool>(uid, key));
    insert(uid, key);
    ensures(df::exists_with_type<u64, bool>(uid, key));
}
