-- Native implementations for sui::object.
-- Per stage 4 (effects), `object::delete` and `object::new` take and
-- return world. `object::new` also takes &mut TxContext (stage-3
-- augmented return threads the TxContext value through value-form per
-- the renderer's `strip_mutable_ref` of native return types).

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.ProgramState
import Prelude.World
import Sui.Tx_contextNatives
-- NOTE: `Sui.AddressNatives` is deliberately NOT imported. The byte natives
-- below need the address serialisation, but that encoder lives in
-- `Prelude.Helpers` as `Address.toBytesBE` (already imported above) precisely
-- so this file does not have to. See the note on `Address.toBytesBE`.

namespace Object

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

-- Struct definitions needed for the natives (defined first)
structure ID where
  bytes : Address
deriving DecidableEq

structure UID where
  id : ID
  key : Nat := id.bytes.bytes.val
deriving DecidableEq

/-- Numeric map key for a Sui UID in the Lean world model. Generated concrete
    UIDs default this to the address value; `object::new` can set an unbounded
    model key so freshness does not wrap at `2^256` in arbitrary proof worlds.
    Dynamic-field storage uses the same projection for parent ids. -/
def uidKey (u : UID) : Nat := u.key

/-- Verification-only canonical token for semantic UID identity. The unary
encoding is intentionally proof-oriented: token equality reduces to equality
of lengths, hence to equality of the unbounded world key. -/
def uid_token (uid : UID) : List (BoundedNat (2^8)) :=
  List.replicate (uidKey uid) (0 : BoundedNat (2^8))

@[simp] theorem length_uid_token (uid : UID) :
    (uid_token uid).length = uidKey uid := by
  simp [uid_token]

@[simp] theorem uid_token_eq_iff_uidKey_eq (left right : UID) :
    uid_token left = uid_token right ↔ uidKey left = uidKey right := by
  constructor
  · intro h
    have hlength := congrArg List.length h
    rw [length_uid_token, length_uid_token] at hlength
    exact hlength
  · intro h
    simp [uid_token, h]

@[simp] theorem uid_token_ne_iff_uidKey_ne (left right : UID) :
    uid_token left ≠ uid_token right ↔ uidKey left ≠ uidKey right := by
  simp only [ne_eq, uid_token_eq_iff_uidKey_eq]

@[simp] theorem uid_token_beq (left right : UID) :
    (uid_token left == uid_token right) = (uidKey left == uidKey right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, uid_token_eq_iff_uidKey_eq]

instance : Inhabited ID where
  default := { bytes := Address.mk 0 }

instance : Inhabited UID where
  default := { id := default }

/-- `HasObjectId T` says `T` is a Sui object: it has a `UID` field
    that the test_scenario natives + transfer natives use as the
    object's identity in the World. Renderer emits one instance per
    object struct (every Move `key`-ability struct, which by Move
    rules has `id : UID` as its first field). -/
class HasObjectId (T : Type) where
  uid : T → UID

-- Native function stubs

def new_count (ctx : Tx_context.TxContext) : BoundedNat (2^64) :=
  BoundedNat.add ctx.ids_created (1 : BoundedNat (2^64))

def uid_from_parts (tx_hash : List (BoundedNat (2^8))) (count : BoundedNat (2^64)) : UID :=
  -- Encode tx_hash bytes as a Nat (big-endian), then combine with the counter
  -- (`2^32` headroom for `ids_created` within a tx). Shared with the
  -- `tx_context::derive_id` native so a spec-boundary peek can NAME this address:
  -- the inner id.bytes is `Tx_context.derive_id tx_hash count` (the low 256 bits)
  -- and the unbounded model `key` is `Tx_context.derive_id_key tx_hash count` (so
  -- freshness does not wrap at 2^256 in arbitrary proof worlds).
  { id := { bytes := Tx_context.derive_id_addr tx_hash count },
    key := Tx_context.derive_id_key tx_hash count }

-- @[simp] bridge: the object::new CANDIDATE uid's address is exactly the pure
-- `tx_context::derive_id` derivation, so a spec `requires` phrased over
-- `tx_context::next_object_address(ctx)` (value form = `derive_id_addr ctx.tx_hash
-- (ids_created+1)` = `derive_id_addr ctx.tx_hash (new_count ctx)`) names the same
-- address the abort face reads off the freshly-minted pool UID.
@[simp] theorem uid_from_parts_bytes (tx_hash : List (BoundedNat (2^8))) (count : BoundedNat (2^64)) :
    (uid_from_parts tx_hash count).id.bytes = Tx_context.derive_id_addr tx_hash count := rfl

def uid_from_key (key : Nat) : UID :=
  let uid_addr : Address :=
    { bytes := ⟨ key % (2^256), Nat.mod_lt _ (by decide) ⟩ }
  { id := { bytes := uid_addr }, key := key }

@[simp] theorem uidKey_uid_from_key (key : Nat) :
    uidKey (uid_from_key key) = key := rfl

def next_uid (ctx : Tx_context.TxContext) : UID :=
  uid_from_parts ctx.tx_hash (new_count ctx)

-- `object::new(ctx: &mut TxContext): UID`. Move's `&mut TxContext`
-- => stage-3 augmented return `(UID, TxContext)`. The Lean model also
-- threads `World` so allocation freshness is explicit. Native returns
-- value-form `TxContext` per the renderer's `strip_mutable_ref` on
-- native return types.
def new (ctx : Tx_context.TxContext) (world : World) : (UID × Tx_context.TxContext × World) :=
  -- Bump `ctx.ids_created` and derive a UID from the new counter.
  -- This gives each `Object.new` call within a tx a distinct UID,
  -- which is what the typed `Transfer.*` / `Test_scenario.take_*`
  -- natives rely on to disambiguate entries in `world.shared` /
  -- `world.owned` / `world.frozen`. Without this, every shared
  -- object gets id 0 and the typed retrieval can't tell them apart.
  --
  -- Note: this uses a per-tx counter. Cross-tx uniqueness relies on
  -- `Tx_context.new_from_hint` populating `ctx.tx_hash` from the
  -- txn_number hint so the encoding `tx_hash * 2^32 + ids_created`
  -- stays globally unique within a single test driver. See
  -- `Tx_contextNatives.new_from_hint`.
  let count := new_count ctx
  let new_ctx : Tx_context.TxContext := { ctx with ids_created := count }
  let candidate : UID := uid_from_parts ctx.tx_hash count
  let uid : UID :=
    if Prover.World.World.validForNewId (uidKey candidate) world then
      candidate
    else
      uid_from_key (Prover.World.World.fresh_id world)
  (uid, new_ctx, Prover.World.World.allocate_id world (uidKey uid))

/-- Allocation-frame pack (2/6): `object::new`'s only world action is one
    `World.allocate_id`, so dynamic-field storage is carried through
    untouched. Every container constructor delegates here, so this rung
    plus `World.allocate_id_df_entries` normalises the `df_entries` of any
    allocation chain back to the base world without unfolding a native. -/
@[simp] theorem new_world_df_entries
    (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).df_entries = world.df_entries := rfl

/-- Bag-store twin of `new_world_df_entries`: `object::new`'s one world
    action (`World.allocate_id`) leaves bag-valued dynamic-field storage
    untouched, so `store_bag_*` obligations see through the mint. -/
@[simp] theorem new_world_df_bag_entries
    (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).df_bag_entries = world.df_bag_entries := rfl

-- Pass 2: the full per-field frame set for `object::new`'s world (its one
-- action is `World.allocate_id`, so every field except `allocated_ids` is
-- carried through untouched). All rfl `@[simp]` frames.

@[simp] theorem new_world_events (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).events = world.events := rfl
@[simp] theorem new_world_owned (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).owned = world.owned := rfl
@[simp] theorem new_world_shared (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).shared = world.shared := rfl
@[simp] theorem new_world_frozen (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).frozen = world.frozen := rfl
@[simp] theorem new_world_deleted (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).deleted = world.deleted := rfl
@[simp] theorem new_world_received (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).received = world.received := rfl
@[simp] theorem new_world_gas_used (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).gas_used = world.gas_used := rfl
@[simp] theorem new_world_bag_entries (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).bag_entries = world.bag_entries := rfl
@[simp] theorem new_world_tx_user_events (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).tx_user_events = world.tx_user_events := rfl
@[simp] theorem new_world_tx_created (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).tx_created = world.tx_created := rfl
@[simp] theorem new_world_accumulator (ctx : Tx_context.TxContext) (world : World) :
    ((new ctx world).2.2).accumulator = world.accumulator := rfl

/-- The transport form: `object::new`'s world IS one `allocate_id` at the
    minted uid. Citation-only (the retired WorldFrameLemmas island's
    `object_new_world` discipline: the RHS names the minted
    uid, so it is not a smaller term). -/
theorem new_world_eq_allocate_id (ctx : Tx_context.TxContext) (world : World) :
    (new ctx world).2.2 =
      Prover.World.World.allocate_id world (uidKey (new ctx world).1) := rfl

@[simp] theorem new_uid_validForNewId_eq_true
    (ctx : Tx_context.TxContext) (world : World) :
    Prover.World.World.validForNewId (uidKey (new ctx world).1) world = true := by
  unfold new
  by_cases h :
      Prover.World.World.validForNewId
        (uidKey (uid_from_parts ctx.tx_hash (new_count ctx))) world = true
  · simp [h]
  · have hfalse :
        Prover.World.World.validForNewId
          (uidKey (uid_from_parts ctx.tx_hash (new_count ctx))) world = false := by
      cases hval :
          Prover.World.World.validForNewId
            (uidKey (uid_from_parts ctx.tx_hash (new_count ctx))) world <;>
        simp [hval] at h ⊢
    simp [hfalse]

theorem new_uidKey_ne_new_uidKey_after_new
    (ctx : Tx_context.TxContext) (world : World) :
    uidKey (new ctx world).1 ≠
      uidKey (new (new ctx world).2.1 (new ctx world).2.2).1 := by
  intro heq
  have hfresh :=
    new_uid_validForNewId_eq_true (new ctx world).2.1 (new ctx world).2.2
  have hallocated :
      Prover.World.World.validForNewId
        (uidKey (new ctx world).1) (new ctx world).2.2 = false := by
    unfold new
    simp
  rw [← heq, hallocated] at hfresh
  contradiction

theorem new_uid_ne_new_after_new
    (ctx : Tx_context.TxContext) (world : World) :
    (new ctx world).1 ≠
      (new (new ctx world).2.1 (new ctx world).2.2).1 := by
  intro heq
  exact new_uidKey_ne_new_uidKey_after_new ctx world (congrArg uidKey heq)

theorem new_uid_token_ne_new_uid_token_after_new
    (ctx : Tx_context.TxContext) (world : World) :
    uid_token (new ctx world).1 ≠
      uid_token (new (new ctx world).2.1 (new ctx world).2.2).1 := by
  rw [uid_token_ne_iff_uidKey_ne]
  exact new_uidKey_ne_new_uidKey_after_new ctx world

def next_uid_key (ctx : Tx_context.TxContext) : Nat :=
  uidKey (next_uid ctx)

/-- Pre-allocation freshness check for the normal tx-derived UID. `object::new`
    uses that UID when it is fresh and falls back to `World.fresh_id` only for
    arbitrary proof worlds where the tx-derived id is already represented. -/
def valid_for_object_new (ctx : Tx_context.TxContext) (world : World) : Bool :=
  Prover.World.World.validForNewId (next_uid_key ctx) world

/-- Ghost-augmented variant of `new` (read-pattern): the ghost
    `SpecObjectNewValue` NAMES the created object, so this `__ghost` def RETURNS
    the threaded ghost UID as its result (making `result == value` hold in
    `new_spec`). It still advances `ctx` via the real `new` (the impl's counter
    bump); only the named id is the threaded ghost. The renderer routes a
    threaded `object::new` call here. Read-only (`imm`) ⇒ no counter. -/
def new__ghost (ctx : Tx_context.TxContext) (world : World) (__ghost : UID) :
    (UID × Tx_context.TxContext × World × UID) :=
  let count := new_count ctx
  let new_ctx : Tx_context.TxContext := { ctx with ids_created := count }
  let new_world := Prover.World.World.allocate_id world (uidKey __ghost)
  (__ghost, new_ctx, new_world, __ghost)

/-- Ghost-threaded `object::new` has the same one world action
    (`World.allocate_id`) as the plain form, so the same two df frames hold
    at its world component. -/
@[simp] theorem new__ghost_world_df_entries
    (ctx : Tx_context.TxContext) (world : World) (ghost : UID) :
    ((new__ghost ctx world ghost).2.2.1).df_entries = world.df_entries := rfl

@[simp] theorem new__ghost_world_df_bag_entries
    (ctx : Tx_context.TxContext) (world : World) (ghost : UID) :
    ((new__ghost ctx world ghost).2.2.1).df_bag_entries = world.df_bag_entries := rfl

/-- Same transport for the ghost-threaded form (its world is `allocate_id`
    at the ghost uid). Unlike the plain form this IS `@[simp]` (the retired
    WorldFrameLemmas island's `object_new_ghost_world` behavior): the RHS
    mentions only the ghost variable, so the `allocate_id` frames take over
    with no term growth. -/
@[simp] theorem new__ghost_world_eq_allocate_id
    (ctx : Tx_context.TxContext) (world : World) (ghost : UID) :
    (new__ghost ctx world ghost).2.2.1 =
      Prover.World.World.allocate_id world (uidKey ghost) := rfl

-- `object::new` cannot abort at the Lean modeling layer (gas is not
-- tracked); the `.aborts` companion is `false`. Stage 7's
-- `expr_aborts` consults this companion via the `spec_target`
-- back-reference registered in `stage_02_ir_cfg::module_lift`.
def new.aborts (_ctx : Tx_context.TxContext) (_world : World) : Bool := false
@[simp] theorem new_aborts_eq_false (ctx : Tx_context.TxContext) (world : World) :
    new.aborts ctx world = false := rfl

-- ---------------------------------------------------------------------------
-- UID freshness vs dynamic-field storage (M5 part c).
--
-- Move-VM justification: `object::new` (equivalently
-- `tx_context::fresh_object_address`) derives a fresh address from the tx hash
-- plus a monotone `ids_created` counter; addresses are globally unique and
-- never reused, so a freshly allocated UID cannot alias any existing
-- dynamic-field parent. This is the semantics under which Boogie discharges
-- the create-side envelopes (`versioned::create`, `validator_wrapper::create_v1`,
-- the request-add-validator-candidate create branch).
--
-- IMPORTANT: this is NOT a new trusted axiom -- the World model already
-- ENCODES this freshness. `Prover.World.World.id_list` (Prelude/World.lean)
-- deliberately counts `df_entries` parent ids among the ids a new object must
-- avoid ("a freshly allocated object must not already have storage hanging off
-- its uid"), and `object::new` returns a uid satisfying `validForNewId ... world`
-- (`new_uid_validForNewId_eq_true` above, falling back to `World.fresh_id` for
-- arbitrary proof worlds). So freshness w.r.t. df storage is DERIVABLE, and the
-- facts below are proven theorems, not model axioms -- strictly stronger than
-- the planned axiom (zero added trust, Boogie parity holds definitionally).
-- The consumer @[simp] corollary is `dynamic_field_add_aborts_object_new_eq_false`
-- (Dynamic_fieldNatives.lean), which discharges `dynamic_field::add.aborts` at a
-- fresh uid. Precedent for a World-freshness lemma of this shape:
-- `Dynamic_field.store_bag_has_eq_false_of_validForNewId`.
-- ---------------------------------------------------------------------------

/-- Freshness -> no df entry: an id that is `validForNewId` in `world` keys no
entry in `world.df_entries` (that store's parent ids are part of `id_list`, so a
fresh id cannot occur among them). -/
theorem df_entries_any_eq_false_of_validForNewId
    {Ev Ob De Be : Type} (id : Nat) (world : Prover.World.World Ev Ob De Be)
    (h : Prover.World.World.validForNewId id world = true) :
    world.df_entries.any (fun e => e.1 == id) = false := by
  apply Bool.eq_false_iff.mpr
  intro hany
  have hcontains : Prover.World.World.contains_id world id = true := by
    rw [Prover.World.World.contains_id, List.any_eq_true]
    simp only [List.any_eq_true] at hany
    rcases hany with ⟨entry, hmem, hkey⟩
    have hmem_id : entry.1 ∈ Prover.World.World.id_list world := by
      rw [Prover.World.World.id_list]
      apply List.mem_append.mpr; left
      apply List.mem_append.mpr; right
      exact List.mem_map.mpr ⟨entry, hmem, rfl⟩
    exact ⟨entry.1, hmem_id, hkey⟩
  rw [Prover.World.World.validForNewId, hcontains] at h
  simp at h

/-- The UID returned by `object::new` keys no entry in the world `new` returns:
`new` records the allocation in `allocated_ids` (leaving `df_entries` untouched)
and returns a `validForNewId` uid, so the freshness lemma above applies. This is
the source fact the create-side `dynamic_field::add.aborts` reads. -/
theorem new_uid_no_df_entry {Ev Ob De Be : Type}
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob De Be) :
    ((new ctx world).2.2).df_entries.any (fun e => e.1 == uidKey (new ctx world).1) = false := by
  have hdf : ((new ctx world).2.2).df_entries = world.df_entries := by
    unfold new; rfl
  rw [hdf]
  exact df_entries_any_eq_false_of_validForNewId (uidKey (new ctx world).1) world
    (new_uid_validForNewId_eq_true ctx world)

-- `object::delete(uid: UID)`. Stage 4 threads world.
def delete (_uid : UID) (world : World) : World := world

/-- World frame for `object::delete`: the model does not record tombstones
    for plain uid deletion (only `World.delete_object`, driven by the
    transfer layer, does), so the world passes through unchanged and every
    observer sees straight through the call. -/
@[simp] theorem delete_world (uid : UID) (world : World) :
    delete uid world = world := rfl

-- `object::delete_impl(id: address): ()`. Low-level native called by
-- the public `delete`. Stage 4 threads world.
def delete_impl (_id : Address) (world : World) : World := world

@[simp] theorem delete_impl_world (id : Address) (world : World) :
    delete_impl id world = world := rfl

-- borrow_uid borrows the UID from an object
def borrow_uid (tv0 : Type) [BEq tv0] [Inhabited tv0] (_obj : tv0) : UID :=
  default

-- record_new_uid is called during object creation to register a new UID.
-- Classified PurePartial (advances the &mut ctx counter; no global
-- side effect beyond that), so stage 4 does NOT thread world.
def record_new_uid (_id : Address) : Unit := ()

-- Same classification as `record_new_uid`.
def record_new_uid_from_hash (_parent _bytes : Address) : Unit := ()

-- `object::id<T: key>(obj: &T): ID` -- return the ID of a Sui object.
-- Pure read; no world threading. Returns default for now -- generic
-- callers (test_scenario.return_shared etc.) don't have a HasObjectId
-- constraint propagated, so they can't extract a real ID. The
-- transfer + test_scenario natives that ARE concrete use
-- `HasObjectId.uid obj` directly.
def id (tv0 : Type) [BEq tv0] [Inhabited tv0] [HasObjectId tv0] (obj : tv0) : ID :=
  (HasObjectId.uid obj).id

-- `object::borrow_id<T: key>(obj: &T): &ID` -- Move body is
-- `&borrow_uid(obj).id`. The renderer drops the leading `&`, so this is
-- the same value as `id`, with the same `[HasObjectId tv0]` bound that
-- `obj_type_universe.rs` already taints `borrow_id`'s `T` for. Listed in
-- `NATIVE_FUNCTIONS`, so the Move body is discarded; without this model
-- every caller rendered an unknown `_root_.Object.borrow_id`.
def borrow_id (tv0 : Type) [BEq tv0] [Inhabited tv0] [HasObjectId tv0] (obj : tv0) : ID :=
  (HasObjectId.uid obj).id

@[simp] theorem borrow_id_eq_id (tv0 : Type) [BEq tv0] [Inhabited tv0] [HasObjectId tv0]
    (obj : tv0) : borrow_id tv0 obj = id tv0 obj := rfl

-- `object::id_address<T: key>(obj: &T): address`.
def id_address (tv0 : Type) [BEq tv0] [Inhabited tv0] [HasObjectId tv0] (obj : tv0) : Address :=
  (HasObjectId.uid obj).id.bytes

-- `object::id_bytes<T: key>(obj: &T): vector<u8>`. Move body is
-- `bcs::to_bytes(&borrow_uid(obj).id.bytes)`, i.e. `to_bytes (id_address obj)`
-- -- the same 32-byte address serialisation as its two siblings below.
--
-- STUBBED ON PURPOSE, and this `[]` is a KNOWN-WRONG value rather than an
-- oversight: unlike `id` / `id_address` next door, this signature carries no
-- `[HasObjectId tv0]` bound, so from an arbitrary `tv0` there is NO accessor
-- that reaches a `UID` -- there is nothing to serialise. The two routes out
-- both fail here:
--   * `uid_to_bytes (borrow_uid tv0 obj)` type-checks, but `borrow_uid` is
--     itself a stub returning `default`, so it would report a CONFIDENT
--     32 zero bytes for every object -- strictly worse than an obviously
--     empty answer, because it reads as a real serialisation.
--   * adding `[HasObjectId tv0]` and returning
--     `Address.toBytesBE (id_address tv0 obj)` would be faithful, and
--     `obj_type_universe.rs` already taints this native's `T` into the object
--     universe alongside `id` / `id_address`. It is NOT done here because
--     NOTHING in the fleet calls it: there are zero `object::id_bytes` call
--     sites across the six client corpora and zero `Object.id_bytes`
--     occurrences in any generated tree, so the instance-resolution half of
--     that change cannot be validated by any corpus -- a green audit
--     afterwards would prove only that nothing broke. A future client that
--     calls it gets an honest `[]` today; make the change when there is a
--     call site to test it against.
def id_bytes (tv0 : Type) [BEq tv0] [Inhabited tv0] (_obj : tv0) : List (BoundedNat (2^8)) :=
  []

-- `object::uid_to_inner(uid: &UID): ID` -- project the ID out of a UID.
def uid_to_inner (uid : UID) : ID :=
  uid.id

-- `object::uid_as_inner(uid: &UID): &ID` -- ref-projection alias of
-- `uid_to_inner`; the renderer drops the leading `&` so the stub
-- shape is identical.
def uid_as_inner (uid : UID) : ID :=
  uid.id

def uid_as_inner.aborts (_uid : UID) : Bool := false
@[simp] theorem uid_as_inner_aborts_eq_false (uid : UID) :
    uid_as_inner.aborts uid = false := rfl

-- `object::uid_to_address(uid: &UID): address`.
def uid_to_address (uid : UID) : Address :=
  uid.id.bytes

-- `object::uid_to_bytes(uid: &UID): vector<u8>` -- Move body is
-- `bcs::to_bytes(&uid.id.bytes)`, which is exactly `address::to_bytes` of the
-- address `uid_to_address` already projects. Composed rather than reaching
-- into `.id.bytes` so the two models cannot drift apart again.
def uid_to_bytes (uid : UID) : List (BoundedNat (2^8)) :=
  Address.toBytesBE (uid_to_address uid)

-- `object::id_to_address(id: &ID): address`.
def id_to_address (id : ID) : Address :=
  id.bytes

-- `object::id_to_bytes(id: &ID): vector<u8>` -- Move body is
-- `bcs::to_bytes(&id.bytes)`, the same 32-byte address serialisation as
-- `address::to_bytes(id_to_address(id))`. Was `[]`, which made any spec
-- relating the two refutable for EVERY input (navi's
-- `Adaptor_switchboard_specs::get_identifier_to_vector_correct`: the
-- implementation returned the empty list while the `ensures` demanded the
-- 32-byte serialisation of the same address). Boogie could not see the gap --
-- there both sides are one uninterpreted `bcs::to_bytes`.
def id_to_bytes (id : ID) : List (BoundedNat (2^8)) :=
  Address.toBytesBE (id_to_address id)

-- Regression pins for the `= []` defect above. Both are `rfl` by
-- construction -- that is the point: they stop elaborating if a future edit
-- re-stubs either native, or re-implements it by reaching into `.id.bytes`
-- instead of composing the accessor. `Address.toBytesBE` IS
-- `address::to_bytes` (pinned on the other side by
-- `Address.to_bytes_eq_toBytesBE`, which this file cannot state because it
-- must not import `Sui.AddressNatives`); the two rfl pins compose to
-- `object::id_to_bytes id = address::to_bytes (object::id_to_address id)`,
-- the equation navi's `get_identifier_to_vector_correct` asserts.
theorem id_to_bytes_eq_toBytesBE_of_id_to_address (id : ID) :
    id_to_bytes id = Address.toBytesBE (id_to_address id) := rfl

theorem uid_to_bytes_eq_toBytesBE_of_uid_to_address (uid : UID) :
    uid_to_bytes uid = Address.toBytesBE (uid_to_address uid) := rfl

-- The length half: the navi `ensures` compares against a 32-byte
-- `address::to_bytes`, and the old `[]` had length 0 -- refutable for every
-- input on the length alone.
theorem length_id_to_bytes (id : ID) : (id_to_bytes id).length = 32 :=
  Address.length_toBytesBE _

theorem length_uid_to_bytes (uid : UID) : (uid_to_bytes uid).length = 32 :=
  Address.length_toBytesBE _

/-- The `uid_to_inner` / `id_to_address` route and the direct `uid_to_address`
    route agree, so a spec may serialise a UID either way. -/
theorem uid_to_bytes_eq_id_to_bytes_of_uid_to_inner (uid : UID) :
    uid_to_bytes uid = id_to_bytes (uid_to_inner uid) := rfl

-- `object::id_from_address(a: address): ID`.
def id_from_address (a : Address) : ID :=
  { bytes := a }

-- `peek_new_id_after(ctx, allocations_before)` names the ID that
-- `object::new` will mint after recursively simulating `allocations_before`
-- preceding allocations. The zero offset names the next allocation. Each
-- simulated allocation threads both the updated transaction context and world,
-- so the result covers the candidate and `fresh_id` fallback branches of
-- `object::new`. The original world is returned unchanged.
def peek_new_id_after
    (ctx : Tx_context.TxContext)
    (allocations_before : BoundedNat (2^64))
    (world : World) : (ID × World) :=
  let rec go : Nat → Tx_context.TxContext → World → ID
    | 0, ctx, world => (new ctx world).1.id
    | remaining + 1, ctx, world =>
      let allocated := new ctx world
      go remaining allocated.2.1 allocated.2.2
  (go allocations_before.val ctx world, world)

@[simp] theorem peek_new_id_after_world
    (ctx : Tx_context.TxContext)
    (allocations_before : BoundedNat (2^64))
    (world : World) :
    (peek_new_id_after ctx allocations_before world).2 = world := rfl

@[simp] theorem peek_new_id_after_zero
    (ctx : Tx_context.TxContext) (world : World) :
    (peek_new_id_after ctx (0 : BoundedNat (2^64)) world).1 =
      (new ctx world).1.id := rfl

@[simp] theorem peek_new_id_after_one
    (ctx : Tx_context.TxContext) (world : World) :
    (peek_new_id_after ctx (1 : BoundedNat (2^64)) world).1 =
      (new (new ctx world).2.1 (new ctx world).2.2).1.id := rfl

-- `object::id_from_bytes(b: vector<u8>): ID`. Derive a real ID from
-- the bytes (big-endian fold into a 256-bit address, mirroring
-- `address::from_bytes`). The previous `default` stub made EVERY
-- `id_from_bytes(...)` collapse to ID 0, so byte-derived keys collided:
-- factory `new_pool_key<A,B>(ts) = id_from_bytes(blake2b256(a_bytes ++
-- b_bytes ++ ts))` returned 0 for every coin pair, so the 2nd
-- `register_permission_pair` saw the pool key as already present and
-- aborted EPoolKeyAlreadyRegistered.
def id_from_bytes (b : List (BoundedNat (2^8))) : ID :=
  { bytes := Address.mk ⟨(b.foldl (fun acc x => (acc * 256 + x.val) % (2 ^ 256)) 0) % (2 ^ 256), Nat.mod_lt _ (by decide)⟩ }

-- `object::new_uid_from_hash(parent: address, bytes: address): UID`. Wraps a
-- caller-computed (already hashed) address straight into a UID, so the inner
-- ID address is exactly `bytes` -- e.g. `derived_object` precomputes the hash
-- and asks for a UID at that address. World-threaded per the call site, passed
-- through unchanged (UID identity lives in the returned value, not the World).
def new_uid_from_hash (_parent bytes : Address) (world : World) : (UID × World) :=
  ({ id := { bytes := bytes } }, world)

@[simp] theorem new_uid_from_hash_world (parent bytes : Address) (world : World) :
    (new_uid_from_hash parent bytes world).2 = world := rfl

-- `object::sui_accumulator_root_address(): address`. The fixed system address
-- of the accumulator root subtree. We don't model accumulator state, so any
-- stable sentinel works: `accumulator::accumulator_address` only feeds this
-- into `hash_type_and_key(root, key)` together with the per-owner key, and the
-- downstream `funds_accumulator` add/withdraw natives are themselves stubs, so
-- the concrete root value never affects a modeled outcome. World-threaded per
-- the call site, unchanged.
def sui_accumulator_root_address (world : World) : (Address × World) :=
  (Address.mk 0, world)

@[simp] theorem sui_accumulator_root_address_world (world : World) :
    (sui_accumulator_root_address world).2 = world := rfl

-- `object::sui_coin_registry_address(): address`. The fixed system address of
-- the singleton `CoinRegistry` object (reserved system address `0xb`). We don't
-- model the registry's receiving side, so the concrete value only matters as a
-- stable, distinct sentinel: `coin_registry::finalize` sends an OTW currency's
-- `Currency` object here via `transfer::transfer(currency, this_address)`, and
-- nothing in the model inspects where it landed. Using the real `0xb` keeps it
-- distinguishable from the accumulator root (address 0). World-threaded per the
-- call site, unchanged.
def sui_coin_registry_address (world : World) : (Address × World) :=
  (Address.mk 11, world)

@[simp] theorem sui_coin_registry_address_world (world : World) :
    (sui_coin_registry_address world).2 = world := rfl

end Object
