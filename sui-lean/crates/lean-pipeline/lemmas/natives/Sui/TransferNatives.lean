-- Native implementations for sui::transfer.
--
-- Per stage 4 (effects), `transfer::*` operations take a world and
-- return a world. The high-level wrappers (`transfer`,
-- `public_transfer`, `share_object`, `public_share_object`,
-- `freeze_object`, `public_freeze_object`) carry a `[HasCode ObjUniv T]
-- [Object.HasObjectId T]` pair and pack the value as a typed
-- `Bag.Entry ObjUniv` pushed into the world's
-- `owned` / `shared` / `frozen` list via the prelude's
-- `Prover.World.World.{transfer_to, share, freeze}` helpers, so the
-- typed payload survives across the call and `test_scenario::take_*`
-- can pull it back at the right type.
--
-- The `_impl` variants stay polymorphic on `T` (no typeclass
-- constraints): they are pre-existing call targets in lemma
-- packages such as `SuiSpecs::Transfer_spec`, and in Move-defined
-- library wrappers like `test_scenario::return_shared`, which do
-- not propagate `HasObjectId` / `HasCode ObjType` constraints.
-- Their world-update is a no-op; the World mutation happens in the
-- high-level wrappers that user Move code actually calls
-- (`transfer::transfer`, `transfer::public_transfer`, etc.).

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.Universe
import Prelude.World
import Sui.BagNatives
import Sui.ObjectNatives

namespace Transfer

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

-- Move source: `public struct Receiving<phantom T: key> has drop {
-- id: ID, version: u64 }`. Phantom type parameter renders as a Lean
-- type-level parameter; the struct itself has no `T`-typed fields.
structure Receiving (T : Type) where
  id      : Object.ID
  version : BoundedNat (2^64)
deriving DecidableEq
instance (T : Type) : Inhabited (Receiving T) where default := ⟨default, default⟩

-- `transfer::receive_impl<T>(parent: address, to_receive: ID,
-- version: u64): T`. The low-level native takes `parent: address`
-- (value, NOT `&mut UID`) and returns just `T`. Stage 4 threads
-- world: `(T) -> (T × World)`. (Don't confuse this with the
-- public `transfer::receive` which takes `&mut UID`; that one is
-- Move-defined, not native, so it doesn't appear here.)
--
-- Looks the object up in `world.owned` by id and removes the entry
-- (receiving takes the object out of the parent's custody), mirroring
-- `Test_scenario.take_from_address_by_id`. A stub returning `default`
-- here made every received object lose its identity, which is exactly
-- what a test's `object::id(&cap) == expected_id` assert then catches.
def receive_impl
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [hcT : HasCode ObjUniv tv0]
    (_parent : Address) (id : Object.ID) (_version : BoundedNat (2^64))
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : (tv0 × Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry) :=
  let id_u : Nat := id.bytes.bytes.val
  let value? : Option tv0 := world.owned.findSome? (fun p =>
    let (_, eid, entry) := p
    if eid = id_u then
      match Universe.decEq entry.kc hcT.code with
      | isTrue h => some (hcT.proof ▸ h ▸ entry.k)
      | isFalse _ => none
    else none)
  let value := value?.getD default
  let new_owned := world.owned.filter (fun p =>
    let (_, eid, _) := p
    eid != id_u)
  (value, { world with owned := new_owned })

-- `transfer::make_receiver<T: key>(id: ID, version: u64): Receiving<T>`
-- (#[test_only]). Move body is exactly `Receiving { id, version }`; the
-- model constructs the same value. Stage 4 threads world:
-- `Receiving<T> -> (Receiving<T> × World)`; the world passes through
-- untouched.
def make_receiver
    (tv0 : Type)
    (id : Object.ID) (version : BoundedNat (2^64))
    (world : World) : (Receiving tv0 × World) :=
  (⟨id, version⟩, world)

-- ---- Polymorphic `_impl` stubs (used by SuiSpecs and by Move-defined wrappers) ----

def freeze_object_impl (tv0 : Type) [BEq tv0] [Inhabited tv0] (_obj : tv0) (world : World) : World := world
def share_object_impl  (tv0 : Type) [BEq tv0] [Inhabited tv0] (_obj : tv0) (world : World) : World := world
-- `transfer_impl` is the genuine `native fun` that performs the transfer;
-- it (and its ghost variant) are defined in the typed-wrapper section below
-- so they can record the `World.transfer_to` effect. The Move-level
-- `public_transfer` / `transfer` are regular funs that call it and are lifted.

-- Ghost-augmented variant of `share_object_impl` (Part 2). The renderer routes
-- a threaded `share_object_impl` Call here (`render::expr::call`); non-ghost
-- callers (e.g. the framework `share_object_impl_spec`, rendered in clients
-- WITHOUT the share markers) keep hitting the plain stub above. Writes the
-- shared object's address + exists flag: `share_object_impl_spec` ensures
-- `SpecShareAddress == object::id(obj).to_address()` (= `Object.id_address`)
-- and `SpecShareAddressExists == true`. Needs `[Object.HasObjectId]` to read
-- the id; all callers are `T: key`, so the instance is always available. The
-- two trailing slots are the threaded ghost vars (positional, sorted by marker
-- struct_id: Address, then Bool); their incoming values are overwritten.
def share_object_impl__ghost
    (tv0 : Type) [BEq tv0] [Inhabited tv0] [Object.HasObjectId tv0]
    (obj : tv0) (world : World)
    (_g_addr : Address) (_g_exists : Bool)
    : (World × Address × Bool) :=
  (world, Object.id_address tv0 obj, true)

def party_transfer_impl
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (_obj : tv0) (_default : BoundedNat (2^64)) (_addresses : List Address)
    (_permissions : List (BoundedNat (2^64))) (world : World) : World :=
  world

-- ---- Typed high-level wrappers ----
-- These declare the world parameter explicitly with `Bag.Entry ObjUniv`
-- in the Object slot rather than using the file-level `World` notation,
-- so Lean can unify `ObjUniv` with the project's `_root_.ObjType` at
-- call sites. The Bag.Entry payload carries the value with its
-- universe code -- `Test_scenario.take_*` rebuilds the original
-- `tv0` from the entry by checking the code matches.

def Object.toEntry
    {ObjUniv : Type} [Universe ObjUniv] (tv0 : Type)
    [hcT : HasCode ObjUniv tv0] (obj : tv0) : Bag.Entry ObjUniv :=
  { kc := hcT.code, k := hcT.proof.symm ▸ obj
  , vc := hcT.code, v := hcT.proof.symm ▸ obj }

def transfer
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0] [Object.HasObjectId tv0]
    (obj : tv0) (recipient : Address)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry :=
  let uid : Object.UID := Object.HasObjectId.uid obj
  let id_u : Nat := Object.uidKey uid
  Prover.World.World.transfer_to world id_u recipient (Object.toEntry tv0 obj)

-- `transfer_impl` is the genuine `native fun transfer_impl<T: key>(obj, r)`:
-- the real transfer effect. `World.transfer_to` records the object moving
-- to `recipient`. The Move-level `public_transfer` / `transfer` wrappers call
-- this; `public_transfer` is lifted, so its callers reach this def.
def transfer_impl
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0] [Object.HasObjectId tv0]
    (obj : tv0) (recipient : Address)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry :=
  let uid : Object.UID := Object.HasObjectId.uid obj
  let id_u : Nat := Object.uidKey uid
  Prover.World.World.transfer_to world id_u recipient (Object.toEntry tv0 obj)

-- Ghost-augmented variant (Part 2): does the transfer effect AND threads +
-- WRITES the spec-only transfer ghosts. The renderer routes a threaded
-- `transfer::transfer_impl` Call here (`program.ghost_vars` carries it -- see
-- `render::expr::call`), so non-ghost callers keep hitting the plain
-- `transfer_impl` above and never see ghost params. The two trailing typed
-- slots are the threaded ghost vars (positional; order matches the IR sig
-- sorted by marker struct_id: Address, then Bool). `transfer_impl_spec`
-- ensures Address == recipient, Exists == true, so the incoming ghost values
-- are overwritten; it returns `(world', recipient, true)`. The static native
-- must NOT name the SuiSpecs markers.
def transfer_impl__ghost
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0] [Object.HasObjectId tv0]
    (obj : tv0) (recipient : Address)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    (_g_addr : Address) (_g_exists : Bool)
    : (Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry × Address × Bool) :=
  let uid : Object.UID := Object.HasObjectId.uid obj
  let id_u : Nat := Object.uidKey uid
  let new_world := Prover.World.World.transfer_to world id_u recipient (Object.toEntry tv0 obj)
  (new_world, recipient, true)

-- Ghost-augmented variant of the plain `transfer::transfer` native. `transfer`
-- is modeled as a native (`Transfer.transfer` above) rather than lifted, so --
-- unlike `public_transfer`, whose lifted body reaches `transfer_impl__ghost` --
-- its callers need this dedicated ghost variant. The renderer routes a
-- ghost-threaded `transfer::transfer` Call here (`transfer` inherits
-- `transfer_impl`'s ghost markers in `derive_native_ghost_seed`, so
-- `program.ghost_vars` carries it -- see `render::expr::call`), while non-ghost
-- callers keep hitting the plain `transfer` above. Body is identical to
-- `transfer_impl__ghost`: does the `World.transfer_to` effect AND writes the
-- transfer ghosts (Address == recipient, Exists == true).
def transfer__ghost
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0] [Object.HasObjectId tv0]
    (obj : tv0) (recipient : Address)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    (_g_addr : Address) (_g_exists : Bool)
    : (Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry × Address × Bool) :=
  let uid : Object.UID := Object.HasObjectId.uid obj
  let id_u : Nat := Object.uidKey uid
  let new_world := Prover.World.World.transfer_to world id_u recipient (Object.toEntry tv0 obj)
  (new_world, recipient, true)

def share_object
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0] [Object.HasObjectId tv0]
    (obj : tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry :=
  let uid : Object.UID := Object.HasObjectId.uid obj
  let id_u : Nat := Object.uidKey uid
  Prover.World.World.share world id_u (Object.toEntry tv0 obj)

def public_share_object
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0] [Object.HasObjectId tv0]
    (obj : tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry :=
  let uid : Object.UID := Object.HasObjectId.uid obj
  let id_u : Nat := Object.uidKey uid
  Prover.World.World.share world id_u (Object.toEntry tv0 obj)

def freeze_object
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0] [Object.HasObjectId tv0]
    (obj : tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry :=
  let uid : Object.UID := Object.HasObjectId.uid obj
  let id_u : Nat := Object.uidKey uid
  Prover.World.World.freeze world id_u (Object.toEntry tv0 obj)

def public_freeze_object
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0] [Object.HasObjectId tv0]
    (obj : tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry :=
  let uid : Object.UID := Object.HasObjectId.uid obj
  let id_u : Nat := Object.uidKey uid
  Prover.World.World.freeze world id_u (Object.toEntry tv0 obj)

-- `transfer::receive<T>(parent: &mut UID, to_receive: Receiving<T>): T`
-- and `public_receive<T>`. Move's `&mut UID` flows through stage 3
-- mut-to-let as augmented returns: the Lean shape is
-- `(parent: UID) (to_receive: Receiving<T>) (world: World) :
--  (T × UID × World)`. The wrapper unpacks the Receiving's id /
-- version into `receive_impl`'s low-level form, converts the UID
-- to an address for `receive_impl`, and propagates the parent UID
-- back as the augmented-return slot.
def receive
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0]
    (parent : Object.UID) (to_receive : Receiving tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : (tv0 × Object.UID × Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry) :=
  let (received, world_1) :=
    receive_impl tv0 (Object.uid_to_address parent) to_receive.id to_receive.version world
  (received, parent, world_1)

def public_receive
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0]
    (parent : Object.UID) (to_receive : Receiving tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : (tv0 × Object.UID × Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry) :=
  let (received, world_1) :=
    receive_impl tv0 (Object.uid_to_address parent) to_receive.id to_receive.version world
  (received, parent, world_1)

-- Ghost-augmented variant of `public_receive` (read-pattern): the ghost
-- `SpecPublicReceiveValue : T` NAMES the received value, so this `__ghost` def
-- RETURNS the threaded ghost (typed `tv0`) as its result (making
-- `result == value` hold in `public_receive_spec`), still threading the
-- parent UID + world. The renderer routes a threaded `public_receive` Call
-- here. Read-only (`imm`) ⇒ no counter.
def public_receive__ghost
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0]
    (parent : Object.UID) (to_receive : Receiving tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    (__ghost : tv0)
    : (tv0 × Object.UID × Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry × tv0) :=
  let (_, parent_1, world_1) := public_receive tv0 parent to_receive world
  (__ghost, parent_1, world_1, __ghost)


-- ============================================================================
-- Lemma layer: ownership-transition faces, frames, cross-object reads,
-- and freshness interplay for the world-writing transfer natives.
--
-- Model honesty notes (verified against the definitions above and
-- `Prelude/World.lean`):
--   * The ownership stores are APPEND-ONLY under transfer/share/freeze:
--     `World.transfer_to` / `share` / `freeze` append `(id, payload)` at the
--     tail of `owned` / `shared` / `frozen` and never remove the id from the
--     other two stores. Ownership exclusivity is enforced by Move's type
--     system upstream (the value is consumed), not by the model, so the
--     honest negative polarity of each transition is its frame set, NOT a
--     removal face.
--   * Every commit also appends the uid to `tx_created` (the per-transaction
--     created list read by `test_scenario::end_transaction`).
--   * `allocated_ids` is untouched: allocation (`object::new`) and commit
--     (transfer/share/freeze) are separate world actions.
--   * Freshness: a committed uid is represented in `World.id_list` (via its
--     store AND `tx_created`), so `validForNewId` is `false` for it afterwards
--     -- a committed object's id can never be re-minted -- while any OTHER
--     id's freshness reads through a commit unchanged.
--
-- Attribute discipline (lemma-wave standard): `@[simp]` ONLY on rfl-class
-- unconditional one-directional faces/frames; every conditional or
-- membership-shaped lemma is citation-only. No `@[move_effect]` (this file
-- has no precedent for it).
-- ============================================================================

/-- `toEntry` stores the object under its type's universe code (key slot). -/
@[simp] theorem Object.toEntry_kc {ObjUniv : Type} [Universe ObjUniv] (tv0 : Type)
    [hcT : HasCode ObjUniv tv0] (o : tv0) :
    (Object.toEntry (ObjUniv := ObjUniv) tv0 o).kc = hcT.code := rfl

/-- `toEntry` stores the object under its type's universe code (value slot). -/
@[simp] theorem Object.toEntry_vc {ObjUniv : Type} [Universe ObjUniv] (tv0 : Type)
    [hcT : HasCode ObjUniv tv0] (o : tv0) :
    (Object.toEntry (ObjUniv := ObjUniv) tv0 o).vc = hcT.code := rfl

section WorldWriterLemmas

variable {ObjUniv : Type} [Universe ObjUniv]
variable (tv0 : Type) [BEq tv0] [Inhabited tv0]
variable [HasCode ObjUniv tv0] [Object.HasObjectId tv0]
variable (obj : tv0) (recipient : Address)
variable (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)


-- ---- `transfer`: transition faces, frames, cross-object reads, freshness ----

/-- Transition face: `transfer` appends the object (keyed by its `uidKey`) to
    `owned`, at the tail. It does NOT remove the id from any other ownership
    store -- exclusivity is enforced by Move's type system upstream, not by the
    model; the negative polarity is exactly the frame lemmas below. -/
@[simp] theorem transfer_owned :
    (transfer tv0 obj recipient world).owned = world.owned ++ [(recipient, Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj)] := rfl

/-- `transfer` records the commit in the current transaction's `tx_created`. -/
@[simp] theorem transfer_tx_created :
    (transfer tv0 obj recipient world).tx_created = world.tx_created ++ [Object.uidKey (Object.HasObjectId.uid obj)] := rfl

@[simp] theorem transfer_events :
    (transfer tv0 obj recipient world).events = world.events := rfl
@[simp] theorem transfer_shared :
    (transfer tv0 obj recipient world).shared = world.shared := rfl
@[simp] theorem transfer_frozen :
    (transfer tv0 obj recipient world).frozen = world.frozen := rfl
@[simp] theorem transfer_deleted :
    (transfer tv0 obj recipient world).deleted = world.deleted := rfl
@[simp] theorem transfer_received :
    (transfer tv0 obj recipient world).received = world.received := rfl
@[simp] theorem transfer_gas_used :
    (transfer tv0 obj recipient world).gas_used = world.gas_used := rfl
@[simp] theorem transfer_bag_entries :
    (transfer tv0 obj recipient world).bag_entries = world.bag_entries := rfl
@[simp] theorem transfer_df_entries :
    (transfer tv0 obj recipient world).df_entries = world.df_entries := rfl
@[simp] theorem transfer_df_bag_entries :
    (transfer tv0 obj recipient world).df_bag_entries = world.df_bag_entries := rfl
@[simp] theorem transfer_tx_user_events :
    (transfer tv0 obj recipient world).tx_user_events = world.tx_user_events := rfl
@[simp] theorem transfer_allocated_ids :
    (transfer tv0 obj recipient world).allocated_ids = world.allocated_ids := rfl
@[simp] theorem transfer_accumulator :
    (transfer tv0 obj recipient world).accumulator = world.accumulator := rfl

/-- Membership face: the committed record is in the owned store. -/
theorem transfer_mem_owned :
    (recipient, Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj) ∈ (transfer tv0 obj recipient world).owned := by simp

/-- Complete membership characterization of the post-`transfer` owned store. -/
theorem transfer_mem_owned_iff {p : Address × Nat × Bag.Entry ObjUniv} :
    p ∈ (transfer tv0 obj recipient world).owned
      ↔ p ∈ world.owned ∨ p = (recipient, Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj) := by simp

/-- Keyed-lookup face: the committed uid is present in owned. -/
theorem transfer_owned_any_self :
    ((transfer tv0 obj recipient world).owned.any (fun p => p.2.1 == Object.uidKey (Object.HasObjectId.uid obj))) = true := by
  simp [List.any_append]

/-- Cross-object frame: a keyed lookup for any OTHER uid reads through
    `transfer` unchanged. -/
theorem transfer_owned_any_ne (k : Nat) (hk : k ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    (transfer tv0 obj recipient world).owned.any (fun p => p.2.1 == k)
      = world.owned.any (fun p => p.2.1 == k) := by
  simp [List.any_append, beq_eq_false_iff_ne.mpr (Ne.symm hk)]

/-- Cross-object frame, filter form: the sub-store keyed by any OTHER uid
    is untouched by `transfer`. -/
theorem transfer_owned_filter_ne (k : Nat) (hk : k ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    (transfer tv0 obj recipient world).owned.filter (fun p => p.2.1 == k)
      = world.owned.filter (fun p => p.2.1 == k) := by
  simp [List.filter_append, beq_eq_false_iff_ne.mpr (Ne.symm hk)]

/-- Freshness face: a committed object's id is represented in the world, so it
    can never be re-minted by `object::new` (`validForNewId` is false). -/
theorem transfer_validForNewId_self_eq_false :
    Prover.World.World.validForNewId (Object.uidKey (Object.HasObjectId.uid obj)) (transfer tv0 obj recipient world) = false := by
  simp [Prover.World.World.validForNewId, Prover.World.World.contains_id,
    Prover.World.World.id_list, transfer, Prover.World.World.transfer_to, List.any_append]

theorem transfer_contains_id_self :
    Prover.World.World.contains_id (transfer tv0 obj recipient world) (Object.uidKey (Object.HasObjectId.uid obj)) = true := by
  simp [Prover.World.World.contains_id,
    Prover.World.World.id_list, transfer, Prover.World.World.transfer_to, List.any_append]

/-- Freshness frame: any OTHER id's world-representation (hence its
    `validForNewId` freshness) reads through `transfer` unchanged. -/
theorem transfer_contains_id_ne (x : Nat) (hx : x ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    Prover.World.World.contains_id (transfer tv0 obj recipient world) x
      = Prover.World.World.contains_id world x := by
  simp only [Prover.World.World.contains_id, Prover.World.World.id_list,
    transfer, Prover.World.World.transfer_to, List.map_append, List.any_append]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hx)]

theorem transfer_validForNewId_ne (x : Nat) (hx : x ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    Prover.World.World.validForNewId x (transfer tv0 obj recipient world)
      = Prover.World.World.validForNewId x world := by
  simp only [Prover.World.World.validForNewId, Prover.World.World.contains_id,
    Prover.World.World.id_list, transfer, Prover.World.World.transfer_to, List.map_append, List.any_append]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hx)]

-- ---- `transfer_impl`: transition faces, frames, cross-object reads, freshness ----

/-- Transition face: `transfer_impl` appends the object (keyed by its `uidKey`) to
    `owned`, at the tail. It does NOT remove the id from any other ownership
    store -- exclusivity is enforced by Move's type system upstream, not by the
    model; the negative polarity is exactly the frame lemmas below. -/
@[simp] theorem transfer_impl_owned :
    (transfer_impl tv0 obj recipient world).owned = world.owned ++ [(recipient, Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj)] := rfl

/-- `transfer_impl` records the commit in the current transaction's `tx_created`. -/
@[simp] theorem transfer_impl_tx_created :
    (transfer_impl tv0 obj recipient world).tx_created = world.tx_created ++ [Object.uidKey (Object.HasObjectId.uid obj)] := rfl

@[simp] theorem transfer_impl_events :
    (transfer_impl tv0 obj recipient world).events = world.events := rfl
@[simp] theorem transfer_impl_shared :
    (transfer_impl tv0 obj recipient world).shared = world.shared := rfl
@[simp] theorem transfer_impl_frozen :
    (transfer_impl tv0 obj recipient world).frozen = world.frozen := rfl
@[simp] theorem transfer_impl_deleted :
    (transfer_impl tv0 obj recipient world).deleted = world.deleted := rfl
@[simp] theorem transfer_impl_received :
    (transfer_impl tv0 obj recipient world).received = world.received := rfl
@[simp] theorem transfer_impl_gas_used :
    (transfer_impl tv0 obj recipient world).gas_used = world.gas_used := rfl
@[simp] theorem transfer_impl_bag_entries :
    (transfer_impl tv0 obj recipient world).bag_entries = world.bag_entries := rfl
@[simp] theorem transfer_impl_df_entries :
    (transfer_impl tv0 obj recipient world).df_entries = world.df_entries := rfl
@[simp] theorem transfer_impl_df_bag_entries :
    (transfer_impl tv0 obj recipient world).df_bag_entries = world.df_bag_entries := rfl
@[simp] theorem transfer_impl_tx_user_events :
    (transfer_impl tv0 obj recipient world).tx_user_events = world.tx_user_events := rfl
@[simp] theorem transfer_impl_allocated_ids :
    (transfer_impl tv0 obj recipient world).allocated_ids = world.allocated_ids := rfl
@[simp] theorem transfer_impl_accumulator :
    (transfer_impl tv0 obj recipient world).accumulator = world.accumulator := rfl

/-- Membership face: the committed record is in the owned store. -/
theorem transfer_impl_mem_owned :
    (recipient, Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj) ∈ (transfer_impl tv0 obj recipient world).owned := by simp

/-- Complete membership characterization of the post-`transfer_impl` owned store. -/
theorem transfer_impl_mem_owned_iff {p : Address × Nat × Bag.Entry ObjUniv} :
    p ∈ (transfer_impl tv0 obj recipient world).owned
      ↔ p ∈ world.owned ∨ p = (recipient, Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj) := by simp

/-- Keyed-lookup face: the committed uid is present in owned. -/
theorem transfer_impl_owned_any_self :
    ((transfer_impl tv0 obj recipient world).owned.any (fun p => p.2.1 == Object.uidKey (Object.HasObjectId.uid obj))) = true := by
  simp [List.any_append]

/-- Cross-object frame: a keyed lookup for any OTHER uid reads through
    `transfer_impl` unchanged. -/
theorem transfer_impl_owned_any_ne (k : Nat) (hk : k ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    (transfer_impl tv0 obj recipient world).owned.any (fun p => p.2.1 == k)
      = world.owned.any (fun p => p.2.1 == k) := by
  simp [List.any_append, beq_eq_false_iff_ne.mpr (Ne.symm hk)]

/-- Cross-object frame, filter form: the sub-store keyed by any OTHER uid
    is untouched by `transfer_impl`. -/
theorem transfer_impl_owned_filter_ne (k : Nat) (hk : k ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    (transfer_impl tv0 obj recipient world).owned.filter (fun p => p.2.1 == k)
      = world.owned.filter (fun p => p.2.1 == k) := by
  simp [List.filter_append, beq_eq_false_iff_ne.mpr (Ne.symm hk)]

/-- Freshness face: a committed object's id is represented in the world, so it
    can never be re-minted by `object::new` (`validForNewId` is false). -/
theorem transfer_impl_validForNewId_self_eq_false :
    Prover.World.World.validForNewId (Object.uidKey (Object.HasObjectId.uid obj)) (transfer_impl tv0 obj recipient world) = false := by
  simp [Prover.World.World.validForNewId, Prover.World.World.contains_id,
    Prover.World.World.id_list, transfer_impl, Prover.World.World.transfer_to, List.any_append]

theorem transfer_impl_contains_id_self :
    Prover.World.World.contains_id (transfer_impl tv0 obj recipient world) (Object.uidKey (Object.HasObjectId.uid obj)) = true := by
  simp [Prover.World.World.contains_id,
    Prover.World.World.id_list, transfer_impl, Prover.World.World.transfer_to, List.any_append]

/-- Freshness frame: any OTHER id's world-representation (hence its
    `validForNewId` freshness) reads through `transfer_impl` unchanged. -/
theorem transfer_impl_contains_id_ne (x : Nat) (hx : x ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    Prover.World.World.contains_id (transfer_impl tv0 obj recipient world) x
      = Prover.World.World.contains_id world x := by
  simp only [Prover.World.World.contains_id, Prover.World.World.id_list,
    transfer_impl, Prover.World.World.transfer_to, List.map_append, List.any_append]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hx)]

theorem transfer_impl_validForNewId_ne (x : Nat) (hx : x ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    Prover.World.World.validForNewId x (transfer_impl tv0 obj recipient world)
      = Prover.World.World.validForNewId x world := by
  simp only [Prover.World.World.validForNewId, Prover.World.World.contains_id,
    Prover.World.World.id_list, transfer_impl, Prover.World.World.transfer_to, List.map_append, List.any_append]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hx)]

-- ---- `share_object`: transition faces, frames, cross-object reads, freshness ----

/-- Transition face: `share_object` appends the object (keyed by its `uidKey`) to
    `shared`, at the tail. It does NOT remove the id from any other ownership
    store -- exclusivity is enforced by Move's type system upstream, not by the
    model; the negative polarity is exactly the frame lemmas below. -/
@[simp] theorem share_object_shared :
    (share_object tv0 obj world).shared = world.shared ++ [(Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj)] := rfl

/-- `share_object` records the commit in the current transaction's `tx_created`. -/
@[simp] theorem share_object_tx_created :
    (share_object tv0 obj world).tx_created = world.tx_created ++ [Object.uidKey (Object.HasObjectId.uid obj)] := rfl

@[simp] theorem share_object_events :
    (share_object tv0 obj world).events = world.events := rfl
@[simp] theorem share_object_owned :
    (share_object tv0 obj world).owned = world.owned := rfl
@[simp] theorem share_object_frozen :
    (share_object tv0 obj world).frozen = world.frozen := rfl
@[simp] theorem share_object_deleted :
    (share_object tv0 obj world).deleted = world.deleted := rfl
@[simp] theorem share_object_received :
    (share_object tv0 obj world).received = world.received := rfl
@[simp] theorem share_object_gas_used :
    (share_object tv0 obj world).gas_used = world.gas_used := rfl
@[simp] theorem share_object_bag_entries :
    (share_object tv0 obj world).bag_entries = world.bag_entries := rfl
@[simp] theorem share_object_df_entries :
    (share_object tv0 obj world).df_entries = world.df_entries := rfl
@[simp] theorem share_object_df_bag_entries :
    (share_object tv0 obj world).df_bag_entries = world.df_bag_entries := rfl
@[simp] theorem share_object_tx_user_events :
    (share_object tv0 obj world).tx_user_events = world.tx_user_events := rfl
@[simp] theorem share_object_allocated_ids :
    (share_object tv0 obj world).allocated_ids = world.allocated_ids := rfl
@[simp] theorem share_object_accumulator :
    (share_object tv0 obj world).accumulator = world.accumulator := rfl

/-- Membership face: the committed record is in the shared store. -/
theorem share_object_mem_shared :
    (Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj) ∈ (share_object tv0 obj world).shared := by simp

/-- Complete membership characterization of the post-`share_object` shared store. -/
theorem share_object_mem_shared_iff {p : Nat × Bag.Entry ObjUniv} :
    p ∈ (share_object tv0 obj world).shared
      ↔ p ∈ world.shared ∨ p = (Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj) := by simp

/-- Keyed-lookup face: the committed uid is present in shared. -/
theorem share_object_shared_any_self :
    ((share_object tv0 obj world).shared.any (fun p => p.fst == Object.uidKey (Object.HasObjectId.uid obj))) = true := by
  simp [List.any_append]

/-- Cross-object frame: a keyed lookup for any OTHER uid reads through
    `share_object` unchanged. -/
theorem share_object_shared_any_ne (k : Nat) (hk : k ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    (share_object tv0 obj world).shared.any (fun p => p.fst == k)
      = world.shared.any (fun p => p.fst == k) := by
  simp [List.any_append, beq_eq_false_iff_ne.mpr (Ne.symm hk)]

/-- Cross-object frame, filter form: the sub-store keyed by any OTHER uid
    is untouched by `share_object`. -/
theorem share_object_shared_filter_ne (k : Nat) (hk : k ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    (share_object tv0 obj world).shared.filter (fun p => p.fst == k)
      = world.shared.filter (fun p => p.fst == k) := by
  simp [List.filter_append, beq_eq_false_iff_ne.mpr (Ne.symm hk)]

/-- Freshness face: a committed object's id is represented in the world, so it
    can never be re-minted by `object::new` (`validForNewId` is false). -/
theorem share_object_validForNewId_self_eq_false :
    Prover.World.World.validForNewId (Object.uidKey (Object.HasObjectId.uid obj)) (share_object tv0 obj world) = false := by
  simp [Prover.World.World.validForNewId, Prover.World.World.contains_id,
    Prover.World.World.id_list, share_object, Prover.World.World.share, List.any_append]

theorem share_object_contains_id_self :
    Prover.World.World.contains_id (share_object tv0 obj world) (Object.uidKey (Object.HasObjectId.uid obj)) = true := by
  simp [Prover.World.World.contains_id,
    Prover.World.World.id_list, share_object, Prover.World.World.share, List.any_append]

/-- Freshness frame: any OTHER id's world-representation (hence its
    `validForNewId` freshness) reads through `share_object` unchanged. -/
theorem share_object_contains_id_ne (x : Nat) (hx : x ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    Prover.World.World.contains_id (share_object tv0 obj world) x
      = Prover.World.World.contains_id world x := by
  simp only [Prover.World.World.contains_id, Prover.World.World.id_list,
    share_object, Prover.World.World.share, List.map_append, List.any_append]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hx)]

theorem share_object_validForNewId_ne (x : Nat) (hx : x ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    Prover.World.World.validForNewId x (share_object tv0 obj world)
      = Prover.World.World.validForNewId x world := by
  simp only [Prover.World.World.validForNewId, Prover.World.World.contains_id,
    Prover.World.World.id_list, share_object, Prover.World.World.share, List.map_append, List.any_append]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hx)]

-- ---- `public_share_object`: transition faces, frames, cross-object reads, freshness ----

/-- Transition face: `public_share_object` appends the object (keyed by its `uidKey`) to
    `shared`, at the tail. It does NOT remove the id from any other ownership
    store -- exclusivity is enforced by Move's type system upstream, not by the
    model; the negative polarity is exactly the frame lemmas below. -/
@[simp] theorem public_share_object_shared :
    (public_share_object tv0 obj world).shared = world.shared ++ [(Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj)] := rfl

/-- `public_share_object` records the commit in the current transaction's `tx_created`. -/
@[simp] theorem public_share_object_tx_created :
    (public_share_object tv0 obj world).tx_created = world.tx_created ++ [Object.uidKey (Object.HasObjectId.uid obj)] := rfl

@[simp] theorem public_share_object_events :
    (public_share_object tv0 obj world).events = world.events := rfl
@[simp] theorem public_share_object_owned :
    (public_share_object tv0 obj world).owned = world.owned := rfl
@[simp] theorem public_share_object_frozen :
    (public_share_object tv0 obj world).frozen = world.frozen := rfl
@[simp] theorem public_share_object_deleted :
    (public_share_object tv0 obj world).deleted = world.deleted := rfl
@[simp] theorem public_share_object_received :
    (public_share_object tv0 obj world).received = world.received := rfl
@[simp] theorem public_share_object_gas_used :
    (public_share_object tv0 obj world).gas_used = world.gas_used := rfl
@[simp] theorem public_share_object_bag_entries :
    (public_share_object tv0 obj world).bag_entries = world.bag_entries := rfl
@[simp] theorem public_share_object_df_entries :
    (public_share_object tv0 obj world).df_entries = world.df_entries := rfl
@[simp] theorem public_share_object_df_bag_entries :
    (public_share_object tv0 obj world).df_bag_entries = world.df_bag_entries := rfl
@[simp] theorem public_share_object_tx_user_events :
    (public_share_object tv0 obj world).tx_user_events = world.tx_user_events := rfl
@[simp] theorem public_share_object_allocated_ids :
    (public_share_object tv0 obj world).allocated_ids = world.allocated_ids := rfl
@[simp] theorem public_share_object_accumulator :
    (public_share_object tv0 obj world).accumulator = world.accumulator := rfl

/-- Membership face: the committed record is in the shared store. -/
theorem public_share_object_mem_shared :
    (Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj) ∈ (public_share_object tv0 obj world).shared := by simp

/-- Complete membership characterization of the post-`public_share_object` shared store. -/
theorem public_share_object_mem_shared_iff {p : Nat × Bag.Entry ObjUniv} :
    p ∈ (public_share_object tv0 obj world).shared
      ↔ p ∈ world.shared ∨ p = (Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj) := by simp

/-- Keyed-lookup face: the committed uid is present in shared. -/
theorem public_share_object_shared_any_self :
    ((public_share_object tv0 obj world).shared.any (fun p => p.fst == Object.uidKey (Object.HasObjectId.uid obj))) = true := by
  simp [List.any_append]

/-- Cross-object frame: a keyed lookup for any OTHER uid reads through
    `public_share_object` unchanged. -/
theorem public_share_object_shared_any_ne (k : Nat) (hk : k ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    (public_share_object tv0 obj world).shared.any (fun p => p.fst == k)
      = world.shared.any (fun p => p.fst == k) := by
  simp [List.any_append, beq_eq_false_iff_ne.mpr (Ne.symm hk)]

/-- Cross-object frame, filter form: the sub-store keyed by any OTHER uid
    is untouched by `public_share_object`. -/
theorem public_share_object_shared_filter_ne (k : Nat) (hk : k ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    (public_share_object tv0 obj world).shared.filter (fun p => p.fst == k)
      = world.shared.filter (fun p => p.fst == k) := by
  simp [List.filter_append, beq_eq_false_iff_ne.mpr (Ne.symm hk)]

/-- Freshness face: a committed object's id is represented in the world, so it
    can never be re-minted by `object::new` (`validForNewId` is false). -/
theorem public_share_object_validForNewId_self_eq_false :
    Prover.World.World.validForNewId (Object.uidKey (Object.HasObjectId.uid obj)) (public_share_object tv0 obj world) = false := by
  simp [Prover.World.World.validForNewId, Prover.World.World.contains_id,
    Prover.World.World.id_list, public_share_object, Prover.World.World.share, List.any_append]

theorem public_share_object_contains_id_self :
    Prover.World.World.contains_id (public_share_object tv0 obj world) (Object.uidKey (Object.HasObjectId.uid obj)) = true := by
  simp [Prover.World.World.contains_id,
    Prover.World.World.id_list, public_share_object, Prover.World.World.share, List.any_append]

/-- Freshness frame: any OTHER id's world-representation (hence its
    `validForNewId` freshness) reads through `public_share_object` unchanged. -/
theorem public_share_object_contains_id_ne (x : Nat) (hx : x ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    Prover.World.World.contains_id (public_share_object tv0 obj world) x
      = Prover.World.World.contains_id world x := by
  simp only [Prover.World.World.contains_id, Prover.World.World.id_list,
    public_share_object, Prover.World.World.share, List.map_append, List.any_append]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hx)]

theorem public_share_object_validForNewId_ne (x : Nat) (hx : x ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    Prover.World.World.validForNewId x (public_share_object tv0 obj world)
      = Prover.World.World.validForNewId x world := by
  simp only [Prover.World.World.validForNewId, Prover.World.World.contains_id,
    Prover.World.World.id_list, public_share_object, Prover.World.World.share, List.map_append, List.any_append]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hx)]

-- ---- `freeze_object`: transition faces, frames, cross-object reads, freshness ----

/-- Transition face: `freeze_object` appends the object (keyed by its `uidKey`) to
    `frozen`, at the tail. It does NOT remove the id from any other ownership
    store -- exclusivity is enforced by Move's type system upstream, not by the
    model; the negative polarity is exactly the frame lemmas below. -/
@[simp] theorem freeze_object_frozen :
    (freeze_object tv0 obj world).frozen = world.frozen ++ [(Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj)] := rfl

/-- `freeze_object` records the commit in the current transaction's `tx_created`. -/
@[simp] theorem freeze_object_tx_created :
    (freeze_object tv0 obj world).tx_created = world.tx_created ++ [Object.uidKey (Object.HasObjectId.uid obj)] := rfl

@[simp] theorem freeze_object_events :
    (freeze_object tv0 obj world).events = world.events := rfl
@[simp] theorem freeze_object_owned :
    (freeze_object tv0 obj world).owned = world.owned := rfl
@[simp] theorem freeze_object_shared :
    (freeze_object tv0 obj world).shared = world.shared := rfl
@[simp] theorem freeze_object_deleted :
    (freeze_object tv0 obj world).deleted = world.deleted := rfl
@[simp] theorem freeze_object_received :
    (freeze_object tv0 obj world).received = world.received := rfl
@[simp] theorem freeze_object_gas_used :
    (freeze_object tv0 obj world).gas_used = world.gas_used := rfl
@[simp] theorem freeze_object_bag_entries :
    (freeze_object tv0 obj world).bag_entries = world.bag_entries := rfl
@[simp] theorem freeze_object_df_entries :
    (freeze_object tv0 obj world).df_entries = world.df_entries := rfl
@[simp] theorem freeze_object_df_bag_entries :
    (freeze_object tv0 obj world).df_bag_entries = world.df_bag_entries := rfl
@[simp] theorem freeze_object_tx_user_events :
    (freeze_object tv0 obj world).tx_user_events = world.tx_user_events := rfl
@[simp] theorem freeze_object_allocated_ids :
    (freeze_object tv0 obj world).allocated_ids = world.allocated_ids := rfl
@[simp] theorem freeze_object_accumulator :
    (freeze_object tv0 obj world).accumulator = world.accumulator := rfl

/-- Membership face: the committed record is in the frozen store. -/
theorem freeze_object_mem_frozen :
    (Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj) ∈ (freeze_object tv0 obj world).frozen := by simp

/-- Complete membership characterization of the post-`freeze_object` frozen store. -/
theorem freeze_object_mem_frozen_iff {p : Nat × Bag.Entry ObjUniv} :
    p ∈ (freeze_object tv0 obj world).frozen
      ↔ p ∈ world.frozen ∨ p = (Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj) := by simp

/-- Keyed-lookup face: the committed uid is present in frozen. -/
theorem freeze_object_frozen_any_self :
    ((freeze_object tv0 obj world).frozen.any (fun p => p.fst == Object.uidKey (Object.HasObjectId.uid obj))) = true := by
  simp [List.any_append]

/-- Cross-object frame: a keyed lookup for any OTHER uid reads through
    `freeze_object` unchanged. -/
theorem freeze_object_frozen_any_ne (k : Nat) (hk : k ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    (freeze_object tv0 obj world).frozen.any (fun p => p.fst == k)
      = world.frozen.any (fun p => p.fst == k) := by
  simp [List.any_append, beq_eq_false_iff_ne.mpr (Ne.symm hk)]

/-- Cross-object frame, filter form: the sub-store keyed by any OTHER uid
    is untouched by `freeze_object`. -/
theorem freeze_object_frozen_filter_ne (k : Nat) (hk : k ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    (freeze_object tv0 obj world).frozen.filter (fun p => p.fst == k)
      = world.frozen.filter (fun p => p.fst == k) := by
  simp [List.filter_append, beq_eq_false_iff_ne.mpr (Ne.symm hk)]

/-- Freshness face: a committed object's id is represented in the world, so it
    can never be re-minted by `object::new` (`validForNewId` is false). -/
theorem freeze_object_validForNewId_self_eq_false :
    Prover.World.World.validForNewId (Object.uidKey (Object.HasObjectId.uid obj)) (freeze_object tv0 obj world) = false := by
  simp [Prover.World.World.validForNewId, Prover.World.World.contains_id,
    Prover.World.World.id_list, freeze_object, Prover.World.World.freeze, List.any_append]

theorem freeze_object_contains_id_self :
    Prover.World.World.contains_id (freeze_object tv0 obj world) (Object.uidKey (Object.HasObjectId.uid obj)) = true := by
  simp [Prover.World.World.contains_id,
    Prover.World.World.id_list, freeze_object, Prover.World.World.freeze, List.any_append]

/-- Freshness frame: any OTHER id's world-representation (hence its
    `validForNewId` freshness) reads through `freeze_object` unchanged. -/
theorem freeze_object_contains_id_ne (x : Nat) (hx : x ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    Prover.World.World.contains_id (freeze_object tv0 obj world) x
      = Prover.World.World.contains_id world x := by
  simp only [Prover.World.World.contains_id, Prover.World.World.id_list,
    freeze_object, Prover.World.World.freeze, List.map_append, List.any_append]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hx)]

theorem freeze_object_validForNewId_ne (x : Nat) (hx : x ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    Prover.World.World.validForNewId x (freeze_object tv0 obj world)
      = Prover.World.World.validForNewId x world := by
  simp only [Prover.World.World.validForNewId, Prover.World.World.contains_id,
    Prover.World.World.id_list, freeze_object, Prover.World.World.freeze, List.map_append, List.any_append]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hx)]

-- ---- `public_freeze_object`: transition faces, frames, cross-object reads, freshness ----

/-- Transition face: `public_freeze_object` appends the object (keyed by its `uidKey`) to
    `frozen`, at the tail. It does NOT remove the id from any other ownership
    store -- exclusivity is enforced by Move's type system upstream, not by the
    model; the negative polarity is exactly the frame lemmas below. -/
@[simp] theorem public_freeze_object_frozen :
    (public_freeze_object tv0 obj world).frozen = world.frozen ++ [(Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj)] := rfl

/-- `public_freeze_object` records the commit in the current transaction's `tx_created`. -/
@[simp] theorem public_freeze_object_tx_created :
    (public_freeze_object tv0 obj world).tx_created = world.tx_created ++ [Object.uidKey (Object.HasObjectId.uid obj)] := rfl

@[simp] theorem public_freeze_object_events :
    (public_freeze_object tv0 obj world).events = world.events := rfl
@[simp] theorem public_freeze_object_owned :
    (public_freeze_object tv0 obj world).owned = world.owned := rfl
@[simp] theorem public_freeze_object_shared :
    (public_freeze_object tv0 obj world).shared = world.shared := rfl
@[simp] theorem public_freeze_object_deleted :
    (public_freeze_object tv0 obj world).deleted = world.deleted := rfl
@[simp] theorem public_freeze_object_received :
    (public_freeze_object tv0 obj world).received = world.received := rfl
@[simp] theorem public_freeze_object_gas_used :
    (public_freeze_object tv0 obj world).gas_used = world.gas_used := rfl
@[simp] theorem public_freeze_object_bag_entries :
    (public_freeze_object tv0 obj world).bag_entries = world.bag_entries := rfl
@[simp] theorem public_freeze_object_df_entries :
    (public_freeze_object tv0 obj world).df_entries = world.df_entries := rfl
@[simp] theorem public_freeze_object_df_bag_entries :
    (public_freeze_object tv0 obj world).df_bag_entries = world.df_bag_entries := rfl
@[simp] theorem public_freeze_object_tx_user_events :
    (public_freeze_object tv0 obj world).tx_user_events = world.tx_user_events := rfl
@[simp] theorem public_freeze_object_allocated_ids :
    (public_freeze_object tv0 obj world).allocated_ids = world.allocated_ids := rfl
@[simp] theorem public_freeze_object_accumulator :
    (public_freeze_object tv0 obj world).accumulator = world.accumulator := rfl

/-- Membership face: the committed record is in the frozen store. -/
theorem public_freeze_object_mem_frozen :
    (Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj) ∈ (public_freeze_object tv0 obj world).frozen := by simp

/-- Complete membership characterization of the post-`public_freeze_object` frozen store. -/
theorem public_freeze_object_mem_frozen_iff {p : Nat × Bag.Entry ObjUniv} :
    p ∈ (public_freeze_object tv0 obj world).frozen
      ↔ p ∈ world.frozen ∨ p = (Object.uidKey (Object.HasObjectId.uid obj), Object.toEntry tv0 obj) := by simp

/-- Keyed-lookup face: the committed uid is present in frozen. -/
theorem public_freeze_object_frozen_any_self :
    ((public_freeze_object tv0 obj world).frozen.any (fun p => p.fst == Object.uidKey (Object.HasObjectId.uid obj))) = true := by
  simp [List.any_append]

/-- Cross-object frame: a keyed lookup for any OTHER uid reads through
    `public_freeze_object` unchanged. -/
theorem public_freeze_object_frozen_any_ne (k : Nat) (hk : k ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    (public_freeze_object tv0 obj world).frozen.any (fun p => p.fst == k)
      = world.frozen.any (fun p => p.fst == k) := by
  simp [List.any_append, beq_eq_false_iff_ne.mpr (Ne.symm hk)]

/-- Cross-object frame, filter form: the sub-store keyed by any OTHER uid
    is untouched by `public_freeze_object`. -/
theorem public_freeze_object_frozen_filter_ne (k : Nat) (hk : k ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    (public_freeze_object tv0 obj world).frozen.filter (fun p => p.fst == k)
      = world.frozen.filter (fun p => p.fst == k) := by
  simp [List.filter_append, beq_eq_false_iff_ne.mpr (Ne.symm hk)]

/-- Freshness face: a committed object's id is represented in the world, so it
    can never be re-minted by `object::new` (`validForNewId` is false). -/
theorem public_freeze_object_validForNewId_self_eq_false :
    Prover.World.World.validForNewId (Object.uidKey (Object.HasObjectId.uid obj)) (public_freeze_object tv0 obj world) = false := by
  simp [Prover.World.World.validForNewId, Prover.World.World.contains_id,
    Prover.World.World.id_list, public_freeze_object, Prover.World.World.freeze, List.any_append]

theorem public_freeze_object_contains_id_self :
    Prover.World.World.contains_id (public_freeze_object tv0 obj world) (Object.uidKey (Object.HasObjectId.uid obj)) = true := by
  simp [Prover.World.World.contains_id,
    Prover.World.World.id_list, public_freeze_object, Prover.World.World.freeze, List.any_append]

/-- Freshness frame: any OTHER id's world-representation (hence its
    `validForNewId` freshness) reads through `public_freeze_object` unchanged. -/
theorem public_freeze_object_contains_id_ne (x : Nat) (hx : x ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    Prover.World.World.contains_id (public_freeze_object tv0 obj world) x
      = Prover.World.World.contains_id world x := by
  simp only [Prover.World.World.contains_id, Prover.World.World.id_list,
    public_freeze_object, Prover.World.World.freeze, List.map_append, List.any_append]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hx)]

theorem public_freeze_object_validForNewId_ne (x : Nat) (hx : x ≠ Object.uidKey (Object.HasObjectId.uid obj)) :
    Prover.World.World.validForNewId x (public_freeze_object tv0 obj world)
      = Prover.World.World.validForNewId x world := by
  simp only [Prover.World.World.validForNewId, Prover.World.World.contains_id,
    Prover.World.World.id_list, public_freeze_object, Prover.World.World.freeze, List.map_append, List.any_append]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hx)]


-- ---- Head bridges (both spellings share one body; citation-only) ----

/-- `transfer` and `transfer_impl` have identical model bodies. -/
theorem transfer_eq_transfer_impl :
    transfer tv0 obj recipient world = transfer_impl tv0 obj recipient world := rfl

/-- `public_share_object` and `share_object` have identical model bodies. -/
theorem public_share_object_eq_share_object :
    public_share_object tv0 obj world = share_object tv0 obj world := rfl

/-- `public_freeze_object` and `freeze_object` have identical model bodies. -/
theorem public_freeze_object_eq_freeze_object :
    public_freeze_object tv0 obj world = freeze_object tv0 obj world := rfl

-- ---- Ghost-augmented transfer variants ----
-- The world component is exactly the plain `transfer_impl` world, so the
-- `@[simp]` bridge below routes every `.1`-component goal into the
-- `transfer_impl` face/frame battery; the two trailing components are the
-- written ghosts (recipient address, exists flag).

@[simp] theorem transfer_impl__ghost_world (g1 : Address) (g2 : Bool) :
    (transfer_impl__ghost tv0 obj recipient world g1 g2).1
      = transfer_impl tv0 obj recipient world := rfl

@[simp] theorem transfer_impl__ghost_addr (g1 : Address) (g2 : Bool) :
    (transfer_impl__ghost tv0 obj recipient world g1 g2).2.1 = recipient := rfl

@[simp] theorem transfer_impl__ghost_exists (g1 : Address) (g2 : Bool) :
    (transfer_impl__ghost tv0 obj recipient world g1 g2).2.2 = true := rfl

@[simp] theorem transfer__ghost_world (g1 : Address) (g2 : Bool) :
    (transfer__ghost tv0 obj recipient world g1 g2).1
      = transfer_impl tv0 obj recipient world := rfl

@[simp] theorem transfer__ghost_addr (g1 : Address) (g2 : Bool) :
    (transfer__ghost tv0 obj recipient world g1 g2).2.1 = recipient := rfl

@[simp] theorem transfer__ghost_exists (g1 : Address) (g2 : Bool) :
    (transfer__ghost tv0 obj recipient world g1 g2).2.2 = true := rfl

/-- `transfer__ghost` and `transfer_impl__ghost` have identical model bodies. -/
theorem transfer__ghost_eq_transfer_impl__ghost (g1 : Address) (g2 : Bool) :
    transfer__ghost tv0 obj recipient world g1 g2
      = transfer_impl__ghost tv0 obj recipient world g1 g2 := rfl

end WorldWriterLemmas

-- ---- Pass-through stubs: identity frames (the whole world is unchanged) ----

section PassThroughLemmas

@[simp] theorem share_object_impl_world (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (o : tv0) (world : World) :
    share_object_impl tv0 o world = world := rfl

@[simp] theorem freeze_object_impl_world (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (o : tv0) (world : World) :
    freeze_object_impl tv0 o world = world := rfl

@[simp] theorem party_transfer_impl_world (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (o : tv0) (d : BoundedNat (2^64)) (addrs : List Address)
    (perms : List (BoundedNat (2^64))) (world : World) :
    party_transfer_impl tv0 o d addrs perms world = world := rfl

/-- HONESTY: the ghost share variant records the ghosts but performs NO world
    mutation (matching the `share_object_impl` pass-through stub it augments --
    the real share effect lives in the typed `share_object` wrapper). -/
@[simp] theorem share_object_impl__ghost_world
    (tv0 : Type) [BEq tv0] [Inhabited tv0] [Object.HasObjectId tv0]
    (o : tv0) (world : World) (g1 : Address) (g2 : Bool) :
    (share_object_impl__ghost tv0 o world g1 g2).1 = world := rfl

@[simp] theorem share_object_impl__ghost_addr
    (tv0 : Type) [BEq tv0] [Inhabited tv0] [Object.HasObjectId tv0]
    (o : tv0) (world : World) (g1 : Address) (g2 : Bool) :
    (share_object_impl__ghost tv0 o world g1 g2).2.1 = Object.id_address tv0 o := rfl

@[simp] theorem share_object_impl__ghost_exists
    (tv0 : Type) [BEq tv0] [Inhabited tv0] [Object.HasObjectId tv0]
    (o : tv0) (world : World) (g1 : Address) (g2 : Bool) :
    (share_object_impl__ghost tv0 o world g1 g2).2.2 = true := rfl

-- ---- receive family: owned-store lookup + parent write-back ----
--
-- `receive_impl` now looks the object up in `world.owned` by id and
-- REMOVES the entry (receiving takes it out of the parent's custody),
-- mirroring `Test_scenario.take_from_address_by_id`. The old
-- world-pass-through / value-is-`default` lemmas are gone with the stub;
-- an id that matches no owned entry (or decodes at the wrong type) still
-- falls back to `default`, so the value is only constrained when the
-- object is actually in the store.

@[simp] theorem receive_parent
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0] [HasCode ObjUniv tv0]
    (parent : Object.UID) (tr : Receiving tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry) :
    (receive tv0 parent tr world).2.1 = parent := rfl

@[simp] theorem public_receive_parent
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0] [HasCode ObjUniv tv0]
    (parent : Object.UID) (tr : Receiving tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry) :
    (public_receive tv0 parent tr world).2.1 = parent := rfl

@[simp] theorem public_receive__ghost_value
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0] [HasCode ObjUniv tv0]
    (parent : Object.UID) (tr : Receiving tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    (g : tv0) :
    (public_receive__ghost tv0 parent tr world g).1 = g := rfl

@[simp] theorem public_receive__ghost_parent
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0] [HasCode ObjUniv tv0]
    (parent : Object.UID) (tr : Receiving tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    (g : tv0) :
    (public_receive__ghost tv0 parent tr world g).2.1 = parent := rfl

@[simp] theorem public_receive__ghost_ghost
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0] [HasCode ObjUniv tv0]
    (parent : Object.UID) (tr : Receiving tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    (g : tv0) :
    (public_receive__ghost tv0 parent tr world g).2.2.2 = g := rfl

end PassThroughLemmas


end Transfer
