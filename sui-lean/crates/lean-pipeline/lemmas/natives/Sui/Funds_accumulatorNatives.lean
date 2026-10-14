-- Native implementations for sui::funds_accumulator

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.World
import Sui.ObjectNatives

namespace Funds_accumulator

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

-- Move source: `public struct Withdrawal<phantom T: store> has drop {
-- owner: address, limit: u256 }`. Phantom type parameter -- no
-- `T`-typed fields.
structure Withdrawal (T : Type) where
  owner : Address
  limit : BoundedNat (2^256)
deriving DecidableEq
instance (T : Type) : Inhabited (Withdrawal T) where default := ⟨default, default⟩

-- `funds_accumulator::withdraw_from_accumulator_address<T>(accumulator: address,
-- owner: address, value: u256): T`. Reached via `accumulator_address`
-- (world-threading through `object::sui_accumulator_root_address`), so the call
-- site threads World and expects `(T, World)` back. We return a value-carrying
-- `T` of the withdrawn `value` (via `FromAccumValue`) and saturatingly debit the
-- World accumulator ledger.
--
-- KEY: the raw funds-`owner` address, NOT the derived `accumulator` slot. All
-- four funds_accumulator natives key the ledger uniformly by the funds-owner
-- identity (`owner` / `recipient`), so deposit and withdraw of the same logical
-- balance hit the same entry regardless of which path reached the native. The
-- protocol's `accumulator_address<T>(owner)` is injective in `(T, owner)`, so for
-- a fixed `T` the raw-owner key is equivalence-class-identical to the derived
-- slot, and our typeless single-amount ledger cannot discriminate `T` anyway.
-- The `accumulator` slot the caller derived is the protocol's dynamic-field
-- location, unused here.
--
-- The Move insufficient-balance abort (`value > balance`) lives in this native's
-- body (no Move source), so it is NOT injected here -- the ledger is debit-only
-- bookkeeping that a future `.aborts` companion can gate by reading
-- `accum_balance world owner`.
def withdraw_from_accumulator_address (_tv0 : Type) [BEq _tv0] [Inhabited _tv0] [FromAccumValue _tv0] (_accumulator : Address) (_owner : Address) (_value : BoundedNat (2^256)) (world : World) : (_tv0 × World) :=
  (FromAccumValue.ofValue _value, Prover.World.World.accum_sub world _owner _value)

-- `funds_accumulator::add_to_accumulator_address<T>(accumulator: address,
-- recipient: address, value: T)`. Same world-threaded reach as the withdraw
-- companion; the call site expects the threaded `World` back. We credit the World
-- accumulator ledger at the raw funds-`recipient` key (the uniform funds-owner
-- key shared by all four natives -- see `withdraw_from_accumulator_address`; the
-- derived `accumulator` slot is unused) with the deposited amount
-- (`ToAccumValue.toValue value`; the real `value` field for `Balance`, 0
-- otherwise).
def add_to_accumulator_address (tv0 : Type) [BEq tv0] [Inhabited tv0] [ToAccumValue tv0] (_accumulator : Address) (_recipient : Address) (_value : tv0) (world : World) : World :=
  Prover.World.World.accum_add world _recipient (ToAccumValue.toValue _value)

-- `funds_accumulator::redeem<T>(withdrawal: Withdrawal<T>, _: internal::Permit<T>): T`.
-- Move body destructures the withdrawal and calls `withdraw_impl(owner, value)`,
-- which routes through `accumulator::accumulator_address` (world-threading via
-- `object::sui_accumulator_root_address`) into the `withdraw_from_accumulator_address`
-- native. The `Withdrawal` already carries the exact withdrawn amount in `limit`
-- (`withdraw_from_object` packs it), so we reconstruct the redeemed value
-- faithfully via `FromAccumValue.ofValue` -- the RETURN value never depends on the
-- ledger. For `T = balance::Balance<C>` this yields a balance of the withdrawn
-- amount (and 0 for a genuine zero-withdrawal); for other `T` it falls back to the
-- value-blind default. We also saturatingly debit the ledger at the withdrawal's
-- raw `owner` key -- the uniform funds-owner key all four natives share (see
-- `withdraw_from_accumulator_address`). For a matched deposit/withdraw pair the
-- deposit `recipient` equals this `owner` (the protocol's own balance invariant,
-- inherited here), so credits and debits land on the same entry; the threaded
-- World otherwise carries that single change.
-- The `internal::Permit<T>` argument is a generated MoveStdlib type; its Lean type
-- is kept implicit so this global shim never imports a generated module (a package
-- that doesn't render `internal` would otherwise fail to compile this shim). The
-- permit is ignored anyway.
def redeem (tv0 : Type) [BEq tv0] [Inhabited tv0] [FromAccumValue tv0] {permitT : Type}
    (_withdrawal : Withdrawal tv0) (_permit : permitT) (world : World) : (tv0 × World) :=
  (FromAccumValue.ofValue _withdrawal.limit, Prover.World.World.accum_sub world _withdrawal.owner _withdrawal.limit)

-- `funds_accumulator::add_impl<T>(value: T, recipient: address)`. Move body
-- derives the recipient's accumulator address (`accumulator_address`,
-- world-threading) and calls the `add_to_accumulator_address` native. We credit
-- the World accumulator ledger at the raw `recipient` key -- the uniform
-- funds-owner key all four natives share (see `withdraw_from_accumulator_address`)
-- -- with the deposited amount (`ToAccumValue.toValue value`); the call site
-- expects the threaded `World` back.
def add_impl (tv0 : Type) [BEq tv0] [Inhabited tv0] [ToAccumValue tv0]
    (_value : tv0) (_recipient : Address) (world : World) : World :=
  Prover.World.World.accum_add world _recipient (ToAccumValue.toValue _value)

-- `funds_accumulator::withdraw_from_object<T>(obj: &mut UID, limit: u256): Withdrawal<T>`.
-- Move body asserts a protocol-config feature flag (the abort path the `.aborts`
-- companion models), reads `obj.to_address()` as the owner, and packs
-- `Withdrawal { owner, limit }`. The `&mut UID` threads the object value back out
-- and the protocol-config read threads World. We model the owner faithfully from
-- the object's address (`obj.id.bytes`), so a redeemed withdrawal still carries a
-- meaningful owner.
def withdraw_from_object (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (obj : _root_.Object.UID) (limit : BoundedNat (2^256)) (world : World) :
    (Withdrawal tv0 × _root_.Object.UID × World) :=
  ({ owner := obj.id.bytes, limit := limit }, obj, world)

-- Reservation bookkeeping is not modeled (the ledger is debited on redeem).
def reserve_object_funds_for_withdrawal (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (_owner : Address) (_limit : BoundedNat (2^256)) (world : World) : World :=
  world

end Funds_accumulator
