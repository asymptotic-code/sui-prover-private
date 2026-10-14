-- Native implementations for sui::tx_context.
--
-- The new-pipeline renderer emits a per-package stub
-- `Sui/Tx_context.lean` that does `import Sui.Tx_contextNatives`, then
-- user code references identifiers as `Tx_context.<name>`. The hand-
-- written contents below therefore live in `namespace Tx_context`.
--
-- IMPORTANT: Move's `tx_context.move` distinguishes two kinds of
-- accessors. The struct-bound ones (`sender(&TxContext): address`,
-- `epoch(&TxContext): u64`, ...) just read fields of the passed-in
-- TxContext value — pure, no `world` threading. The top-level natives
-- (`native_sender()`, `native_epoch()`, ..., `fresh_id()`) query the
-- prover's current transaction state, which the new-pipeline's
-- stage 4 (effects) models by threading `world : World` through. So
-- their Lean signature is `(world : World) : (T × World)`, not just
-- `: T`. Spec functions (`SuiSpecs.Tx_context_spec`) call the
-- top-level natives by their `Tx_context.<name>` qualified name and
-- the IR-rendered spec body destructures `(t_t0_0, world_1) :=
-- (Tx_context.<name> world)` — which only type-checks if the natives
-- are world-threaded.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.World

namespace Tx_context

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

-- Move source: `public struct TxContext has drop { sender: address,
-- tx_hash: vector<u8>, epoch: u64, epoch_timestamp_ms: u64,
-- ids_created: u64 }`. The new pipeline keeps the struct value-form
-- and the renderer threads it through `&mut TxContext` arguments via
-- `Mutation TxContext` at the IR boundary (stage 3 augmented return),
-- but native callees take and return the unwrapped form (renderer
-- auto-strips `.val` on native-Call args; see
-- `render::expr::render_call`'s `callee_is_native` branch).
structure TxContext where
  sender             : Address
  tx_hash            : List (BoundedNat (2^8))
  epoch              : BoundedNat (2^64)
  epoch_timestamp_ms : BoundedNat (2^64)
  ids_created        : BoundedNat (2^64)
deriving DecidableEq

instance : Inhabited TxContext where
  default := { sender := default, tx_hash := [], epoch := default,
               epoch_timestamp_ms := default, ids_created := default }

-- ==== Top-level natives ====
-- These mirror the `native fun ...` declarations in `tx_context.move`.
-- Each is effectful (queries the current tx state); stage 4 threads
-- `world` and the rendered spec / impl bodies destructure the
-- `(value, world')` pair.

def native_sender (world : World) : (Address × World) := (default, world)

def native_epoch (world : World) : (BoundedNat (2^64) × World) := (default, world)

def native_epoch_timestamp_ms (world : World) : (BoundedNat (2^64) × World) :=
  (default, world)

def native_rgp (world : World) : (BoundedNat (2^64) × World) := (default, world)

def native_gas_price (world : World) : (BoundedNat (2^64) × World) := (default, world)

def native_ids_created (world : World) : (BoundedNat (2^64) × World) := (default, world)

def native_gas_budget (world : World) : (BoundedNat (2^64) × World) := (default, world)

def native_sponsor (world : World) : ((List Address) × World) := ([], world)

-- `fresh_id` is the low-level native called by
-- `fresh_object_address(&mut TxContext): address`. It produces a
-- fresh ID derived from `tx_hash` + `ids_created`, so it is
-- effectful and stage 4 threads `world` here too.
def fresh_id (world : World) : (Address × World) := (default, world)

def last_created_id (world : World) : (Address × World) := (default, world)

-- `derive_id(tx_hash, ids_created): address` -- the private `native fun derive_id`
-- of tx_context.move ("deriving an ID via hash(tx_hash || ids_created)"). This is
-- the SAME address derivation `object::new` uses for its candidate UID: encode the
-- tx_hash bytes big-endian, combine with the counter (2^32 headroom for the per-tx
-- counter), take the low 256 bits. `Object.uid_from_parts` is refactored to reuse
-- `derive_id_key`/`derive_id_addr`, so the object::new candidate address is
-- definitionally `derive_id_addr ctx.tx_hash (new_count ctx)`. The `#[test_only]`
-- module extension `tx_context::next_object_address(ctx)` names that fresh address
-- at a spec boundary.
--
-- `derive_id_key` (unbounded) is the object's model `key` (freshness must not wrap
-- at 2^256); `derive_id_addr` is the low-256-bit address. The registered native
-- `derive_id` itself is world-threaded by stage 4's default native effect (its
-- trusted `derive_id_spec` and the `next_object_address` extension both call it as
-- `(… × World)`), but it is a pure hash so the world passes through unchanged.
def derive_id_key (tx_hash : List (BoundedNat (2^8))) (ids_created : BoundedNat (2^64)) : Nat :=
  (tx_hash.foldl (fun acc b => acc * 256 + b.val) 0) * (2^32) + ids_created.val

def derive_id_addr (tx_hash : List (BoundedNat (2^8))) (ids_created : BoundedNat (2^64)) : Address :=
  { bytes := ⟨ derive_id_key tx_hash ids_created % (2^256), Nat.mod_lt _ (by decide) ⟩ }

def derive_id (tx_hash : List (BoundedNat (2^8))) (ids_created : BoundedNat (2^64)) (world : World) :
    (Address × World) :=
  (derive_id_addr tx_hash ids_created, world)

-- `replace` is a test-only API that overwrites the tx context state.
-- Stage 4 threads `world` because the mutation must be observable.
def replace (_sender : Address) (_tx_hash : List (BoundedNat (2^8))) (_epoch : BoundedNat (2^64))
    (_epoch_timestamp_ms : BoundedNat (2^64)) (_ids_created : BoundedNat (2^64))
    (_rgp : BoundedNat (2^64)) (_gas_price : BoundedNat (2^64)) (_gas_budget : BoundedNat (2^64))
    (_sponsor : List Address) (world : World) : World := world

-- ==== Public Move-level operations (struct-bound) ====
-- These take `&TxContext` (= value-form `self : TxContext`) and read
-- a struct field directly. Move's `sender(&self)` returns `self.sender`
-- — pure, no `world` threading.

/-- `tx_context::sender(&TxContext): address`. -/
def sender (self : TxContext) : Address := self.sender

/-- `tx_context::digest(&TxContext): &vector<u8>`. The reference is
    erased at the prelude boundary (the field is `copy`-able after
    deref via `.val`). -/
def digest (self : TxContext) : List (BoundedNat (2^8)) := self.tx_hash

/-- `tx_context::epoch(&TxContext): u64`. -/
def epoch (self : TxContext) : BoundedNat (2^64) := self.epoch

/-- `tx_context::epoch_timestamp_ms(&TxContext): u64`. -/
def epoch_timestamp_ms (self : TxContext) : BoundedNat (2^64) := self.epoch_timestamp_ms

/-- `tx_context::reference_gas_price(&TxContext): u64`. Returns the
    minimum gas price set by the validators for this epoch; modeled
    here as a per-tx native query (delegates to `native_rgp` if a
    world is in scope; without one, returns `default` as a
    conservative placeholder). The struct doesn't carry rgp, so we
    can't read a field. -/
def reference_gas_price (_self : TxContext) : BoundedNat (2^64) := default

/-- `tx_context::gas_price(&TxContext): u64`. Same as above —
    struct doesn't carry it directly. -/
def gas_price (_self : TxContext) : BoundedNat (2^64) := default

/-- `tx_context::ids_created(&TxContext): u64`. -/
def ids_created (self : TxContext) : BoundedNat (2^64) := self.ids_created

/-- `tx_context::fresh_object_address(&mut TxContext): address`. Move
    `&mut TxContext` => stage-3 augmented return `(address, TxContext)`.
    Per `16f34e1c` this op is `PurePartial`, so no `world` threading. -/
def fresh_object_address (ctx : TxContext) : (Address × TxContext) :=
  (default, ctx)

/-- Ghost-augmented variant (read-pattern): the ghost `SpecFreshObjectAddress`
    NAMES the fresh address, so this `__ghost` def RETURNS the threaded ghost as
    its result (making `result == value` hold in `fresh_object_address_spec`).
    The renderer routes a threaded call here. Read-only (`imm`) ⇒ no counter. -/
def fresh_object_address__ghost (ctx : TxContext) (__ghost : Address) :
    (Address × TxContext × Address) :=
  (__ghost, ctx, __ghost)

/-- `#[test_only] public fun new_from_hint(addr, hint, epoch, ts, ids): TxContext`.
    The new pipeline's stage 4 (effects) threads `world` through any
    function that can produce a fresh ID (this one does, via the Move
    `new(..., dummy_tx_hash_with_hint(hint), ...)` body), so the Lean
    call site expects `(TxContext × World)`. Stub returns a value-form
    TxContext with the given epoch / timestamp directly populated. -/
def new_from_hint (addr : Address) (hint : BoundedNat (2^64)) (epoch : BoundedNat (2^64))
    (epoch_timestamp_ms : BoundedNat (2^64)) (ids_created : BoundedNat (2^64)) (world : World)
    : (TxContext × World) :=
  -- Encode `hint` (which `test_scenario::next_tx` passes as the
  -- current txn_number) into `tx_hash` so `Object.new`'s UID
  -- derivation `tx_hash * 2^32 + ids_created` differs across txs.
  -- 8-byte little-endian split is enough for the 64-bit hint;
  -- collisions across tests are not a concern since each test
  -- driver gets its own World.
  let hint_bytes : List (BoundedNat (2^8)) :=
    let v := hint.val
    [ ⟨(v / 1) % 256, Nat.mod_lt _ (by decide)⟩
    , ⟨(v / 256) % 256, Nat.mod_lt _ (by decide)⟩
    , ⟨(v / 65536) % 256, Nat.mod_lt _ (by decide)⟩
    , ⟨(v / 16777216) % 256, Nat.mod_lt _ (by decide)⟩
    , ⟨(v / 4294967296) % 256, Nat.mod_lt _ (by decide)⟩
    , ⟨(v / 1099511627776) % 256, Nat.mod_lt _ (by decide)⟩
    , ⟨(v / 281474976710656) % 256, Nat.mod_lt _ (by decide)⟩
    , ⟨(v / 72057594037927936) % 256, Nat.mod_lt _ (by decide)⟩
    ]
  (({ sender := addr, tx_hash := hint_bytes, epoch := epoch,
      epoch_timestamp_ms := epoch_timestamp_ms, ids_created := ids_created } : TxContext), world)

def new_from_hint.aborts (_addr : Address) (_hint : BoundedNat (2^64))
    (_epoch : BoundedNat (2^64)) (_epoch_timestamp_ms : BoundedNat (2^64))
    (_ids_created : BoundedNat (2^64)) : Bool := false

/-- `tx_context::dummy(): TxContext` (`#[test_only]`). Move source
constructs a TxContext with the fixed hash literal
`x"3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"`,
zero sender / epoch / timestamp / ids. Lean model uses `default`
for fields -- the literal hash bytes aren't observed by any spec
that touches `dummy`. -/
def dummy : TxContext :=
  { sender := default
  , tx_hash := default
  , epoch := default
  , epoch_timestamp_ms := default
  , ids_created := default }

def dummy.aborts : Bool := false

/-- `tx_context::increment_epoch_number(self: &mut TxContext)` -- bumps
the epoch by 1. Model as `epoch := epoch + 1`. Threads `self` as a
pass-back via stage 4. -/
def increment_epoch_number (self : TxContext) : TxContext :=
  -- Bump epoch by 1, modulo 2^64 to match Move's u64 wraparound. The
  -- result type-checks against `BoundedNat (2^64)` via the existing
  -- arithmetic helpers; `BoundedNat.add` would handle overflow, but
  -- we just use the modulo construction since this is a #[test_only]
  -- helper -- specs that observe epoch order should compare values,
  -- not assume non-wrapping arithmetic.
  { self with epoch := BoundedNat.add self.epoch (1 : BoundedNat (2^64)) }

def increment_epoch_number.aborts (_self : TxContext) : Bool := false

end Tx_context
