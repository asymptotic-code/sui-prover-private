module 0x42::share_observation;
use sui::object::{Self, UID};
use sui::transfer;
use specs::transfer_spec::{SpecShareAddress, SpecShareAddressExists};
use prover::ghost;
use prover::prover::ensures;
public struct Shared has key { id: UID }
fun share(value: Shared) { transfer::share_object(value); }
#[mode(spec), ext(backend = b"boogie", spec(prove, target = share))]
fun share_spec(value: Shared) {
    let expected = object::id(&value).to_address();
    ghost::declare_global_mut<SpecShareAddress, address>();
    ghost::declare_global_mut<SpecShareAddressExists, bool>();
    share(value);
    ensures(ghost::global<SpecShareAddressExists, bool>() == true);
    ensures(ghost::global<SpecShareAddress, address>() == expected);
}
