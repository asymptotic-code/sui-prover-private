-- Native implementations for sui::random.
-- Move struct definitions live here (the renderer treats `sui::random`
-- as a native module since the package has native fun decls; the
-- struct definitions don't fall out of translation, so they must be
-- hand-written).

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.World
import Sui.ObjectNatives
import Sui.Tx_contextNatives
import Sui.Versioned
import Sui.RandomInnerNatives
import Prelude.Universe
import Sui.BagNatives
import Sui.TransferNatives

namespace Random

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

-- Move source: `public struct Random has key { id: UID, inner: Versioned }`.
structure Random where
  id    : Object.UID
  inner : Versioned.Versioned
deriving DecidableEq
instance : Inhabited Random where default := ⟨default, default⟩

-- Framework native object: the renderer only emits `HasObjectId` for
-- user `key` structs (cf. BagNatives), so provide it here.
instance : Object.HasObjectId Random where
  uid r := r.id

-- Move source: `public struct RandomGenerator has drop {
--   seed: vector<u8>, counter: u16, buffer: vector<u8> }`.
structure RandomGenerator where
  seed    : List (BoundedNat (2^8))
  counter : BoundedNat (2^16)
  buffer  : List (BoundedNat (2^8))
deriving DecidableEq
instance : Inhabited RandomGenerator where
  default := ⟨[], default, []⟩

-- 32 zero bytes — deterministic and unobservable for tests that don't
-- depend on cryptographic randomness.
def generate_rand_seed_for_testing : List (BoundedNat (2^8)) :=
  List.replicate 32 ⟨0, by decide⟩

-- ---------------------------------------------------------------------------
-- RNG natives.
--
-- `random::new_generator(rnd: &Random, ctx: &mut TxContext): RandomGenerator`
-- and the `random::generate_u<N>(gen: &mut RandomGenerator): u<N>`
-- family. Stage 3 mut-to-let augments any `&mut` parameter; the
-- natives below ship the augmented value-form return shape (one
-- output per `&mut` slot). Bytes returned are abstract defaults --
-- the verification harness models real randomness as ghost state.
-- ---------------------------------------------------------------------------

/-- `random::new_generator(rnd: &Random, ctx: &mut TxContext): RandomGenerator`.
Stage 3 augments TxContext return. -/
def new_generator (_rnd : Random) (ctx : Tx_context.TxContext)
    : RandomGenerator × Tx_context.TxContext :=
  -- Seed the generator's counter from the tx sender so distinct
  -- transactions/senders produce distinct byte streams. The prior stub
  -- returned `default` (counter 0) for every call, so any test that
  -- generated two random values across transactions got identical
  -- output and tripped uniqueness checks. Deterministic (no real
  -- entropy) but varying -- enough for tests that only assert on
  -- length / uniqueness, not specific random values.
  ({ seed := [], counter := ⟨ctx.sender.bytes.val % 2^16, Nat.mod_lt _ (by decide)⟩, buffer := [] }, ctx)

def new_generator.aborts (_rnd : Random) (_ctx : Tx_context.TxContext) : Bool := false

/-- `random::generate_bytes(gen: &mut RandomGenerator, num_of_bytes: u16): vector<u8>`.
Returns `(bytes, augmented_gen)`. -/
def generate_bytes (gen : RandomGenerator) (_num_of_bytes : BoundedNat (2^16))
    : List (BoundedNat (2^8)) × RandomGenerator :=
  ([], gen)

def generate_bytes.aborts (_gen : RandomGenerator) (_num_of_bytes : BoundedNat (2^16)) : Bool := false

/-- `random::generate_u8(gen: &mut RandomGenerator): u8`.
Stage 3 augments: `(u8, RandomGenerator)`. -/
def generate_u8 (gen : RandomGenerator) : BoundedNat (2^8) × RandomGenerator :=
  -- Derive a byte from the counter and advance it, so successive draws
  -- differ. Deterministic but non-constant (the prior stub returned a
  -- fixed `default`, making every generated string identical).
  (⟨gen.counter.val % 2^8, Nat.mod_lt _ (by decide)⟩,
   { gen with counter := ⟨(gen.counter.val + 1) % 2^16, Nat.mod_lt _ (by decide)⟩ })

def generate_u8.aborts (_gen : RandomGenerator) : Bool := false

/-- `random::generate_u16(gen: &mut RandomGenerator): u16`. -/
def generate_u16 (gen : RandomGenerator) : BoundedNat (2^16) × RandomGenerator :=
  (default, gen)

def generate_u16.aborts (_gen : RandomGenerator) : Bool := false

/-- `random::generate_u32(gen: &mut RandomGenerator): u32`. -/
def generate_u32 (gen : RandomGenerator) : BoundedNat (2^32) × RandomGenerator :=
  (default, gen)

def generate_u32.aborts (_gen : RandomGenerator) : Bool := false

/-- `random::generate_u64(gen: &mut RandomGenerator): u64`. -/
def generate_u64 (gen : RandomGenerator) : BoundedNat (2^64) × RandomGenerator :=
  (default, gen)

def generate_u64.aborts (_gen : RandomGenerator) : Bool := false

/-- `random::generate_u128(gen: &mut RandomGenerator): u128`. -/
def generate_u128 (gen : RandomGenerator) : BoundedNat (2^128) × RandomGenerator :=
  (default, gen)

def generate_u128.aborts (_gen : RandomGenerator) : Bool := false

/-- `random::generate_u256(gen: &mut RandomGenerator): u256`. -/
def generate_u256 (gen : RandomGenerator) : BoundedNat (2^256) × RandomGenerator :=
  (default, gen)

def generate_u256.aborts (_gen : RandomGenerator) : Bool := false

/-- `random::generate_bool(gen: &mut RandomGenerator): bool`. -/
def generate_bool (gen : RandomGenerator) : Bool × RandomGenerator := (false, gen)

def generate_bool.aborts (_gen : RandomGenerator) : Bool := false

-- ---------------------------------------------------------------------------
-- `random::generate_u<N>_in_range(gen: &mut RandomGenerator, min, max): u<N>`.
--
-- The framework builds all five on one `uint_in_range` macro, which
-- `assert!(min <= max, EInvalidRange)` and then returns a value in
-- `[min, max]`. The value returned here is `min` rather than `default`:
-- unlike the plain `generate_u<N>` family above, this one has a
-- FRAMEWORK SPEC (`specs::random_spec::u128_in_range_spec` ships
-- `ensures(result >= min)` / `ensures(result <= max)` under
-- `asserts(min <= max)`), and that spec is trusted, i.e. it becomes an
-- axiom over this model. `default` (0) would make that axiom false for
-- every `min > 0` -- an inconsistent axiom, not a weak one. `min` is
-- degenerate but satisfies the contract for every admitted input.
--
-- No `.aborts` companion, deliberately. `EInvalidRange` is a REAL abort
-- condition (`min > max`), so a `:= false` companion would be a lie, and
-- a real one would have to be listed in `NATIVES_WITH_ABORTS_COMPANIONS`
-- to be visible to stage 7 at all -- which changes the `.aborts` face of
-- every caller fleet-wide. With no companion the natives stay `Partial`
-- in `native_effects` and stage 7 keeps the coarse, sound `true`.
-- ---------------------------------------------------------------------------

/-- `random::generate_u8_in_range(gen: &mut RandomGenerator, min: u8, max: u8): u8`. -/
def generate_u8_in_range (gen : RandomGenerator) (min _max : BoundedNat (2^8))
    : BoundedNat (2^8) × RandomGenerator :=
  (min, gen)

/-- `random::generate_u16_in_range(gen: &mut RandomGenerator, min: u16, max: u16): u16`. -/
def generate_u16_in_range (gen : RandomGenerator) (min _max : BoundedNat (2^16))
    : BoundedNat (2^16) × RandomGenerator :=
  (min, gen)

/-- `random::generate_u32_in_range(gen: &mut RandomGenerator, min: u32, max: u32): u32`. -/
def generate_u32_in_range (gen : RandomGenerator) (min _max : BoundedNat (2^32))
    : BoundedNat (2^32) × RandomGenerator :=
  (min, gen)

/-- `random::generate_u64_in_range(gen: &mut RandomGenerator, min: u64, max: u64): u64`. -/
def generate_u64_in_range (gen : RandomGenerator) (min _max : BoundedNat (2^64))
    : BoundedNat (2^64) × RandomGenerator :=
  (min, gen)

/-- `random::generate_u128_in_range(gen: &mut RandomGenerator, min: u128, max: u128): u128`. -/
def generate_u128_in_range (gen : RandomGenerator) (min _max : BoundedNat (2^128))
    : BoundedNat (2^128) × RandomGenerator :=
  (min, gen)

/-- `random::create_for_testing(ctx: &mut TxContext)` (test-only).
Move return is `()`; the function calls `create(ctx)` which shares
the Random object via `transfer::share_object`. Stage 4 (effects)
threads `world`. Stage 3 augments `&mut TxContext` to a return
slot, giving the call shape `(ctx: TxContext, world: World) ->
(TxContext, World)`. The stub returns the inputs unchanged. -/
def create_for_testing
    {ObjUniv : Type} [Universe ObjUniv] [HasCode ObjUniv Random]
    (ctx : Tx_context.TxContext)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : Tx_context.TxContext × Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry :=
  -- Real `random::create_for_testing` creates a `Random` shared object.
  -- The prior stub returned `(ctx, world)` unchanged, so `world.shared`
  -- never held a Random and any `take_shared<Random>` aborted (code 3 in
  -- the test_scenario model). Create a fresh UID, build the Random, and
  -- register it as shared so `take_shared` can retrieve it.
  let (uid, ctx', world') := Object.new ctx world
  let r : Random := { id := uid, inner := default }
  let id_u : Nat := Object.uidKey uid
  (ctx', Prover.World.World.share world' id_u (Transfer.Object.toEntry Random r))

def create_for_testing.aborts (_ctx : Tx_context.TxContext) (_world : World) : Bool := false

end Random
