module 0x42::share_payload;
use sui::object::{Self, UID};
use sui::transfer;
use sui::tx_context::TxContext;
use specs::transfer_spec::{SpecShareObject, SpecShareAddress, SpecShareAddressExists};
use prover::ghost;
use prover::prover::ensures;
public struct Shared has key { id: UID, amount: u64 }
fun create_and_share(amount: u64, ctx: &mut TxContext) {
    transfer::share_object(Shared { id: object::new(ctx), amount });
}
#[mode(spec), ext(backend = b"boogie", spec(prove, target = create_and_share))]
fun create_and_share_spec(amount: u64, ctx: &mut TxContext) {
    ghost::declare_global_mut<SpecShareObject<Shared>, Shared>();
    ghost::declare_global_mut<SpecShareAddressExists, bool>();
    ghost::declare_global_mut<SpecShareAddress, address>();
    create_and_share(amount, ctx);
    ensures(*ghost::global<SpecShareAddressExists, bool>());
    ensures(ghost::global<SpecShareObject<Shared>, Shared>().amount == amount);
}
