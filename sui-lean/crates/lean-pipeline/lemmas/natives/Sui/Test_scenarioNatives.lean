-- Native implementations for sui::test_scenario.
--
-- Typed retrieval from the world: `take_shared` / `take_from_address`
-- / `take_immutable` (and their `_by_id` variants) scan the world's
-- typed `Bag.Entry ObjUniv` lists (`shared` / `owned` / `frozen`),
-- find an entry whose universe code matches the target type's
-- `HasCode ObjUniv T` code, and rebuild the typed `T` value via the
-- `proof : Universe.interp code = T` rewrite. Take ops also remove
-- the entry from the list so `was_taken_*` can report it as taken
-- (i.e. absent from the inventory) on the next check.
--
-- These typed natives are the consumer of the typed payloads
-- recorded by the `sui::transfer::*` wrappers in
-- `lemmas/natives/Sui/TransferNatives.lean`. The full round-trip
-- (share -> take, transfer -> take) is type-preserving via the
-- per-project closed-universe `Generated.ObjType` declared by the
-- renderer.
--
-- The `Scenario` and `TransactionEffects` struct types are defined
-- in the renderer-emitted `Sui.Test_scenario` body (sui-framework
-- Move source's `public struct Scenario { ... }` is lifted as a
-- regular -- non-native -- struct, because Move's `begin` packs it
-- directly). Since this natives file is IMPORTED by
-- `Sui.Test_scenario.lean` and elaborated first, those struct
-- definitions are not yet in scope here -- so the few natives that
-- "see" them take the struct type as an abstract parameter and let
-- Lean unify against the concrete struct at the call site.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.Universe
import Prelude.World
import Sui.BagNatives
import Sui.ObjectNatives
import Sui.TransferNatives
import Sui.Tx_contextNatives
import MoveStdlib.MoveOption

namespace Test_scenario

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

-- ---- Helpers ----

/-- Reconstruct an `Object.ID` from the `Nat` key used in
    `Prover.World.World.{shared, owned, frozen}` entries. `n % 2^256`
    keeps the BoundedNat construction total. -/
def idFromNat (n : Nat) : _root_.Object.ID :=
  { bytes := { bytes := ⟨n % (2^256), Nat.mod_lt _ (by decide)⟩ } }

/-- Find the newest entry (last-cons) in `entries` whose universe
    code matches `hcT.code`. Returns its id. -/
def findNewestId
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [hcT : HasCode ObjUniv tv0]
    (entries : List (Nat × Bag.Entry ObjUniv)) : Option Nat :=
  entries.reverse.findSome? (fun p =>
    match Universe.decEq p.snd.kc hcT.code with
    | isTrue _ => some p.fst
    | isFalse _ => none)

/-- Retrieve and decode an entry by id + matching code. Returns
    `(value?, entries)`. The entry list is NOT modified -- used only by
    `take_immutable_by_id` (frozen objects), where `return_immutable`
    updates the entry in place rather than removing/re-appending, so the
    immutable `take -> use -> return_immutable -> take` sequence works
    with the entry kept in place. (Shared and owned takes DO remove the
    entry inline -- see `take_shared_by_id` / `take_from_address_by_id`
    -- so that repeated takes of the same type return distinct objects.) -/
def takeById
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [hcT : HasCode ObjUniv tv0]
    (entries : List (Nat × Bag.Entry ObjUniv)) (id : Nat)
    : (Option tv0 × List (Nat × Bag.Entry ObjUniv)) :=
  let value? : Option tv0 := entries.findSome? (fun p =>
    if p.fst = id then
      match Universe.decEq p.snd.kc hcT.code with
      | isTrue h => some (hcT.proof ▸ h ▸ p.snd.k)
      | isFalse _ => none
    else none)
  (value?, entries)

-- ---- Typed natives ----

def most_recent_id_shared
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0]
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : ((_root_.MoveOption.MoveOption _root_.Object.ID)
       × Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry) :=
  let opt := match findNewestId tv0 world.shared with
    | some n => _root_.MoveOption.MoveOption.mk [idFromNat n]
    | none   => _root_.MoveOption.MoveOption.mk []
  (opt, world)

def most_recent_id_for_address
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [hcT : HasCode ObjUniv tv0]
    (account : Address)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : ((_root_.MoveOption.MoveOption _root_.Object.ID)
       × Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry) :=
  let matching : List (Nat × Bag.Entry ObjUniv) :=
    world.owned.filterMap (fun (addr, id, entry) =>
      if addr == account then some (id, entry) else none)
  let opt := match findNewestId tv0 matching with
    | some n => _root_.MoveOption.MoveOption.mk [idFromNat n]
    | none   => _root_.MoveOption.MoveOption.mk []
  (opt, world)

def most_recent_immutable_id
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0]
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : ((_root_.MoveOption.MoveOption _root_.Object.ID)
       × Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry) :=
  let opt := match findNewestId tv0 world.frozen with
    | some n => _root_.MoveOption.MoveOption.mk [idFromNat n]
    | none   => _root_.MoveOption.MoveOption.mk []
  (opt, world)

-- The `take_*_by_id` natives take the scenario as an abstract type;
-- Lean unifies `ScenT` with the renderer-emitted
-- `Test_scenario.Scenario` at the call site.

def take_shared_by_id
    {ObjUniv : Type} [Universe ObjUniv]
    {ScenT : Type}
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [hcT : HasCode ObjUniv tv0]
    (_scenario : ScenT) (id : _root_.Object.ID)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : (tv0 × Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry) :=
  let id_u : Nat := id.bytes.bytes.val
  let (value?, _) := takeById tv0 world.shared id_u
  let value := value?.getD default
  -- Remove the taken entry so a subsequent `take_shared` of the same
  -- type returns the NEXT object rather than the same (newest) one
  -- again. `return_shared` re-appends it (carrying the test's
  -- modifications). Without this, a test that takes two distinct shared
  -- objects of the same type before returning gets the newest object
  -- twice (`most_recent_id_shared` is stateless). Mirrors
  -- `take_from_address_by_id`, which removes owned entries for the same
  -- reason.
  let new_shared := world.shared.filter (fun p => p.fst != id_u)
  (value, { world with shared := new_shared })

def take_from_address_by_id
    {ObjUniv : Type} [Universe ObjUniv]
    {ScenT : Type}
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [hcT : HasCode ObjUniv tv0]
    (_scenario : ScenT) (_account : Address) (id : _root_.Object.ID)
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
  -- Remove the taken entry so a subsequent `take_from_address` of the
  -- same type from this address returns the NEXT object rather than
  -- the same (newest) one again. `return_to_address` re-appends it.
  -- Without this, a test that takes two distinct objects of the same
  -- type from one address before returning gets the newest object
  -- twice (`most_recent_id_for_address` is stateless). Unlike shared
  -- objects (typically taken once), owned coins are routinely taken
  -- in batches.
  let new_owned := world.owned.filter (fun p =>
    let (_, eid, _) := p
    eid != id_u)
  (value, { world with owned := new_owned })

def take_immutable_by_id
    {ObjUniv : Type} [Universe ObjUniv]
    {ScenT : Type}
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0]
    (_scenario : ScenT) (id : _root_.Object.ID)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : (tv0 × Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry) :=
  let id_u : Nat := id.bytes.bytes.val
  let (value?, remaining) := takeById tv0 world.frozen id_u
  let value := value?.getD default
  (value, { world with frozen := remaining })

-- ---- Typed `return_*` natives ----
--
-- Move's `test_scenario::return_shared` / `return_to_address` /
-- `return_immutable` are Move-defined wrappers around
-- `transfer::share_object_impl` (and friends). With our polymorphic
-- `_impl` pass-through stubs, the modifications a test makes to a
-- taken object would be silently discarded -- the world's shared /
-- owned / frozen list would still carry the pre-take value.
--
-- Override them as natives (registered in
-- `stage_02_ir_cfg/natives.rs::NATIVE_FUNCTIONS`) so we can
-- update the typed entry IN PLACE.
--
-- Identity is by `Object.HasObjectId.uid obj`. If the id isn't found,
-- the entry list is left unchanged -- matching the "object was never
-- shared" case (test won't typically hit this path because
-- `take_shared` succeeds beforehand).

def return_shared
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0] [Object.HasObjectId tv0]
    (obj : tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry :=
  let uid : Object.UID := Object.HasObjectId.uid obj
  let id_u : Nat := Object.uidKey uid
  let new_entry := Transfer.Object.toEntry tv0 obj
  -- `take_shared_by_id` REMOVED the entry on take; re-append it
  -- (carrying the test's modifications) so it is available to take
  -- again. A plain `map` over `world.shared` would find nothing to
  -- update (the entry is gone) and silently drop the object, making
  -- a subsequent `take_shared` of the same type abort. Filter any
  -- stale copy first and append at the tail so `findNewestId` (which
  -- scans from the tail) sees it as newest. Mirrors `return_to_address`.
  let filtered := world.shared.filter (fun p => p.fst != id_u)
  { world with shared := filtered ++ [(id_u, new_entry)] }

def return_to_address
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0] [Object.HasObjectId tv0]
    (account : Address) (obj : tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry :=
  let uid : Object.UID := Object.HasObjectId.uid obj
  let id_u : Nat := Object.uidKey uid
  let new_entry := Transfer.Object.toEntry tv0 obj
  -- `take_from_address_by_id` removed the entry on take; re-append it
  -- (carrying the test's modifications). Filter any stale copy first
  -- so the list stays unique by id and the re-added entry becomes the
  -- newest (matching real Sui semantics where a returned object is
  -- available to take again). Appending at the tail keeps
  -- `findNewestId` (which scans from the tail) consistent.
  let filtered := world.owned.filter (fun p =>
    let (_, eid, _) := p
    eid != id_u)
  { world with owned := filtered ++ [(account, id_u, new_entry)] }

def return_immutable
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [HasCode ObjUniv tv0] [Object.HasObjectId tv0]
    (obj : tv0)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry :=
  let uid : Object.UID := Object.HasObjectId.uid obj
  let id_u : Nat := Object.uidKey uid
  let new_entry := Transfer.Object.toEntry tv0 obj
  let new_frozen := world.frozen.map (fun p =>
    if p.fst = id_u then (p.fst, new_entry) else p)
  { world with frozen := new_frozen }

-- `was_taken_*` reports whether the id used to be in the inventory
-- but has been pulled out. Our model: an id is "taken" iff it is
-- NOT currently in the corresponding world list. This is the
-- correct semantics for tests that share/transfer then take exactly
-- once; tests that take-return-take would need return_shared to
-- re-insert the entry, which the polymorphic `share_object_impl`
-- stub does not do (a known limitation -- see Phase 6 notes).

-- Move's `return_shared` aborts when `was_taken_shared` is false.
-- Our typed `return_shared` native (below) re-appends the entry
-- directly and does not consult `was_taken_shared`, so this guard
-- only matters when Move code calls `test_scenario::was_taken_shared`
-- explicitly. Report "yes, taken" unconditionally to keep such calls
-- (and any return path) a successful no-op.
def was_taken_shared (_id : _root_.Object.ID) (world : World) : (Bool × World) :=
  (true, world)

def was_taken_from_address (_account : Address) (_id : _root_.Object.ID) (world : World) : (Bool × World) :=
  (true, world)

def was_taken_immutable (_id : _root_.Object.ID) (world : World) : (Bool × World) :=
  (true, world)

-- `ids_for_address<T>`: enumerate ids of objects of type T owned by
-- `account`.
def ids_for_address
    {ObjUniv : Type} [Universe ObjUniv]
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    [hcT : HasCode ObjUniv tv0]
    (account : Address)
    (world : Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry)
    : ((List _root_.Object.ID)
       × Prover.World.World __WorldEvent (Bag.Entry ObjUniv) __WorldDfEntry __WorldBagEntry) :=
  let ids := world.owned.filterMap (fun (addr, eid, entry) =>
    if addr == account then
      if _h : entry.kc = hcT.code then some (idFromNat eid) else none
    else none)
  (ids, world)

-- `allocate_receiving_ticket_for_object<T>(id, world): u64`.
def allocate_receiving_ticket_for_object
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (object_id : _root_.Object.ID) (world : World)
    : (BoundedNat (2^64) × World) :=
  let id_u : Nat := object_id.bytes.bytes.val
  (⟨id_u % (2^64), Nat.mod_lt _ (by decide)⟩, world)

def deallocate_receiving_ticket_for_object
    (_object_id : _root_.Object.ID) (world : World) : World :=
  world

-- `end_transaction(world): TransactionEffects`: the renderer emits a
-- `:= default` stub for this one in `Sui/Test_scenario.lean` itself
-- (force-stub override in `render/mod.rs`), because its return type
-- `TransactionEffects` is a Move-defined struct that the natives
-- sibling can't reference (the sibling is imported BEFORE the struct
-- is declared). Stubbing returns `default` for both component, which
-- is fine for the tests we care about -- they pass through
-- end_transaction without inspecting the effects.

-- `unit_test_poison(world): World`. Pass-through.
def unit_test_poison (world : World) : World := world

end Test_scenario
