module 0x42::foo;
use sui::dynamic_field as df;
use sui::object;
use prover::prover::ensures;

public struct Child has key, store {
    id: UID,
    value: u64,
}

public fun roundtrip(value: u64, ctx: &mut TxContext): u64 {
    let mut parent = object::new(ctx);
    let child = Child { id: object::new(ctx), value: 0 };
    df::add(&mut parent, 7u64, child);
    let child_ref: &mut Child = df::borrow_mut(&mut parent, 7u64);
    child_ref.value = value;
    let Child { id, value: result } = df::remove<u64, Child>(&mut parent, 7u64);
    object::delete(id);
    object::delete(parent);
    result
}

#[mode(spec), ext(spec(prove))]
fun roundtrip_spec(value: u64, ctx: &mut TxContext): u64 {
    let result = roundtrip(value, ctx);
    ensures(result != value);
    result
}
