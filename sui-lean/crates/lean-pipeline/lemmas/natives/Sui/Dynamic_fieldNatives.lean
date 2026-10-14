-- Native implementations for sui::dynamic_field.
-- Low-level VM hooks (child-object functions, no Move source) plus the
-- World-backed df API (borrow / set / remove / has / store_remove_if_exists
-- and the store_bag_* family) that route_df_to_world targets. See
-- plans/lean-pipeline/container-df-unification.md.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.ProgramState
import Prelude.World
import Prelude.Universe
import Prover.MoveAutoAttr
import Sui.ObjectNatives
import Sui.BagNatives
import Sui.TableNatives
import Sui.Object_tableNatives
import Sui.Object_bagNatives
import MoveStdlib.MoveOption

set_option linter.unusedVariables false

namespace Dynamic_field

-- Struct: dynamic_field::Field
structure Field (tv0 : Type) (tv1 : Type) where
  id : Object.UID
  name : tv0
  value : tv1
deriving DecidableEq
instance [Inhabited tv0] [Inhabited tv1] : Inhabited (Field tv0 tv1) where default := ⟨default, default, default⟩

-- hash_type_and_key computes a hash of the type and key for dynamic field lookup
def hash_type_and_key (tv0 : Type) (_parent : Address) (_key : tv0) : Address :=
  Address.mk 0

-- add_child_object adds a child object to a parent
def add_child_object (tv0 : Type) (_parent : Address) (_child : tv0) : Unit :=
  ()

-- has_child_object checks if a child object exists
@[reducible] def has_child_object (_parent : Address) (_id : Address) : Bool :=
  false

-- has_child_object_with_ty checks if a child object of specific type exists
@[reducible] def has_child_object_with_ty (tv0 : Type) (_parent : Address) (_id : Address) : Bool :=
  false

-- borrow_child_object borrows a child object immutably.
-- The dynamic_field_rewriting pass turns most uses into TypedMap.get; this
-- stub catches stragglers and returns the type's default so test bodies
-- evaluate without `sorry`.
def borrow_child_object (tv0 : Type) [Inhabited tv0] (_parent : Object.UID) (_id : Address) : tv0 :=
  default

-- borrow_child_object_mut borrows a child object mutably.
-- Returns a default Mutable wrapper; the .aborts companion already captures
-- the relevant abort condition at the higher-level dynamic_field call sites.
def borrow_child_object_mut (tv0 : Type) [Inhabited tv0] (_parent : Object.UID) (_id : Address) : (Mutable tv0 Object.UID) × Object.UID :=
  (Mutable.mk default (fun _ => default), default)

-- remove_child_object removes and returns a child object
def remove_child_object (tv0 : Type) [Inhabited tv0] (_parent : Address) (_id : Address) : tv0 :=
  default

-- field_info returns UID and address for a dynamic field
def field_info (tv0 : Type) [BEq tv0] [Inhabited tv0] (_object : Object.UID) (_name : tv0) : (Object.UID × Address) :=
  (default, default)

-- field_info_mut is the mutable variant
def field_info_mut (tv0 : Type) [BEq tv0] [Inhabited tv0] (_object : Object.UID) (_name : tv0) : ((Object.UID × Address) × Object.UID) :=
  ((default, default), default)

-- ---------------------------------------------------------------------------
-- (The parent-typed high-level stubs -- borrow / borrow_mut / add /
-- remove / remove_if_exists / exists_ / exists_with_type and their
-- always-false .aborts companions -- were DELETED in step-2 slice C.
-- Every df/dof op routes through the World natives below
-- (route_df_to_world); the stubs were Inhabited-default fallbacks, so
-- a routing gap now fails loudly as an unknown identifier instead of
-- silently reading defaults. See
-- plans/lean-pipeline/container-df-unification.md.)
-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- World-backed dynamic-field storage (new model).
--
-- `dynamic_field::*` no longer move their values onto the owning object
-- struct. The value lives in `World.df_entries`, keyed by
-- `(parent uid low-64 bits, key)`, with the (key, value) pair typed via
-- the project `TyCode` df universe (`Bag.Entry Df`, the entry type the
-- World `DfEntry` parameter is pinned to). This keeps user `_Types.lean`
-- free of the universe, dissolving the `_Types <-> TyCodeInterp` import
-- cycle. The renderer threads `world` (stage 4) and recovers the parent
-- uid + key at each call site. Mirrors `Bag.{borrow,set,remove,contains}`
-- with an added uid match. See
-- `plans/lean-pipeline/dynamic-fields-in-world.md`.
-- ---------------------------------------------------------------------------

/-- Dynamic-field parent key derived from a parent object's `UID`. -/
def uidKey (u : Object.UID) : Nat := Object.uidKey u

/-- `dynamic_field::borrow` / `borrow_mut` initial read. Find the entry
matching parent `uid` and `key`, transport its value to `V` via
`HasCode`, default if absent. -/
def borrow {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [hkc : HasCode Df K] [hvc : HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) Be)
    : V × Prover.World.World Ev Ob (Bag.Entry Df) Be :=
  let found? : Option V :=
    world.df_entries.findSome? (fun e =>
      if e.1 == uidKey uid && Bag.Entry.keyMatches e.2 k then
        if hv : e.2.vc = hvc.code then
          some (hvc.proof ▸ hv ▸ e.2.v)
        else none
      else none)
  (found?.getD default, world)

/-- The upsert primitive: `dynamic_field::add` and the `borrow_mut`
writeback. Overwrite (or insert) the value at `(uid, key)`: drop any
prior entry with the same uid+key, then cons-prepend the new one.
(Move's df API has no `set`; the pipeline synthesizes it -- see
plans/lean-pipeline/container-df-unification.md.) -/
def set {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [hkc : HasCode Df K] [hvc : HasCode Df V] [DecidableEq K]
    (uid : Object.UID) (k : K) (v : V) (world : Prover.World.World Ev Ob (Bag.Entry Df) Be)
    : Prover.World.World Ev Ob (Bag.Entry Df) Be :=
  let entry : Bag.Entry Df :=
    { kc := hkc.code, k := hkc.proof.symm ▸ k, vc := hvc.code, v := hvc.proof.symm ▸ v }
  let filtered := world.df_entries.filter (fun e => ! (e.1 == uidKey uid && Bag.Entry.keyMatches e.2 k))
  { world with df_entries := (uidKey uid, entry) :: filtered }

/-- `dynamic_field::add`. Same world action as `set`; the difference is
the spec side -- `add.aborts` models EFieldAlreadyExists (abort iff the
key is PRESENT), while `set` (the writeback primitive) is total. -/
def add {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : Object.UID) (k : K) (v : V) (world : Prover.World.World Ev Ob (Bag.Entry Df) Be)
    : Prover.World.World Ev Ob (Bag.Entry Df) Be :=
  set K V uid k v world

def add.aborts {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : Object.UID) (k : K) (_v : V) (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) : Bool :=
  -- EFieldAlreadyExists: `add` aborts when the key is already present.
  world.df_entries.any (fun e => e.1 == uidKey uid && Bag.Entry.keyMatches e.2 k)

/-- `dynamic_field::remove`. Return the value at `(uid, key)` plus the
world with that entry dropped. -/
def remove {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [hkc : HasCode Df K] [hvc : HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) Be)
    : V × Prover.World.World Ev Ob (Bag.Entry Df) Be :=
  let v := (borrow K V uid k world).1
  let filtered := world.df_entries.filter (fun e => ! (e.1 == uidKey uid && Bag.Entry.keyMatches e.2 k))
  (v, { world with df_entries := filtered })

/-- `dynamic_field::remove_if_exists` (World model). Drop the entry at
`(uid, key)` if present; never aborts. The `V` result mirrors
`remove`'s defaulting read and is only sound where the caller
DISCARDS it -- the route pass asserts that shape. -/
def store_remove_if_exists {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [hkc : HasCode Df K] [hvc : HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) Be)
    : V × Prover.World.World Ev Ob (Bag.Entry Df) Be :=
  let v := (borrow K V uid k world).1
  let filtered := world.df_entries.filter (fun e => ! (e.1 == uidKey uid && Bag.Entry.keyMatches e.2 k))
  (v, { world with df_entries := filtered })

/-- `dynamic_field::exists_with_type` / `exists_`. -/
def has {Ev Ob Be Df : Type} [Universe Df] (K : Type)
    [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) Be)
    : Bool × Prover.World.World Ev Ob (Bag.Entry Df) Be :=
  (world.df_entries.any (fun e => e.1 == uidKey uid && Bag.Entry.keyMatches e.2 k), world)

-- Aborts companions (false; missing-key / type-mismatch live in the harness).
def borrow.aborts {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) : Bool :=
  -- `dynamic_field::borrow`/`borrow_mut` abort (EFieldDoesNotExist) when the
  -- key is absent. Mirror `has`'s presence predicate; abort iff absent.
  ! world.df_entries.any (fun e => e.1 == uidKey uid && Bag.Entry.keyMatches e.2 k)
def set.aborts {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (_uid : Object.UID) (_k : K) (_v : V) (_world : Prover.World.World Ev Ob (Bag.Entry Df) Be) : Bool := false
def remove.aborts {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) : Bool :=
  -- `dynamic_field::remove` aborts (EFieldDoesNotExist) when the key is
  -- absent -- same presence predicate as borrow.aborts.
  ! world.df_entries.any (fun e => e.1 == uidKey uid && Bag.Entry.keyMatches e.2 k)

-- ---------------------------------------------------------------------------
-- Bag-VALUED dynamic fields: `dynamic_field::{add,borrow,borrow_mut,exists,
-- remove}<K, Bag>` (and `<K, ObjectBag>`). A `Bag` value can't be a code in
-- either universe (it IS a universe's container), so it can't ride in
-- `df_entries` as a `DfEntry`. Store the bag's own `size` + `storage` in the dedicated
-- `df_bag_entries` slot, keyed by `(uid, key)`; the key reuses `Bag.Entry`
-- for matching (value slot unused). Routed here by `dynamic_field_rewrite`
-- when the df VALUE type is exactly Bag/ObjectBag. The bag's contents
-- (`storage : List (Bag.Entry Bg)`) ARE universe-typed (over the `BagU`
-- bag universe), so they ride as the world's `BagEntry` param without
-- needing `HasCode _ Bag`.
-- ---------------------------------------------------------------------------

def store_bag_set {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K V : Type)
    [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (bag : Bag.Bag Bg)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg) :=
  let keyEntry : Bag.Entry Df :=
    { kc := hkc.code, k := hkc.proof.symm ▸ k, vc := hkc.code, v := hkc.proof.symm ▸ k }
  let filtered := world.df_bag_entries.filter
    (fun e => ! (e.1 == uidKey uid && Bag.Entry.keyMatches e.2.1 k))
  { world with df_bag_entries := (uidKey uid, keyEntry, bag.size, bag.storage) :: filtered }

/-- `dynamic_field::add<K, Bag>` (and `dynamic_object_field::add<K, ObjectBag>`).
Same World action as `store_bag_set`; the difference is the spec side --
`store_bag_add.aborts` models Move's TYPE-AGNOSTIC EFieldAlreadyExists (abort
iff ANY field occupies the key, in EITHER the bag store OR the plain
`df_entries` store), while `store_bag_set` (the bag writeback primitive) is
total. Mirrors the plain-df `add` = `set` split. -/
def store_bag_add {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K V : Type)
    [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (bag : Bag.Bag Bg)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg) :=
  store_bag_set K V uid k bag world

/-- The bag-`add` World action IS `store_bag_set` (only the abort side differs);
reduce it so every `store_bag_set` writeback lemma fires at add sites too. -/
@[simp] theorem store_bag_add_eq_store_bag_set {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] (K V : Type) [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (bag : Bag.Bag Bg)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    store_bag_add K V uid k bag world = store_bag_set K V uid k bag world := rfl

def store_bag_borrow {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K V : Type)
    [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    : Bag.Bag Bg × Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg) :=
  match world.df_bag_entries.findSome? (fun e =>
      if e.1 == uidKey uid && Bag.Entry.keyMatches e.2.1 k then some (e.2.2.1, e.2.2.2) else none) with
  | some (sz, st) => ({ (default : Bag.Bag Bg) with size := sz, storage := st }, world)
  | none          => (default, world)

def store_bag_has {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K : Type)
    [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    : Bool × Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg) :=
  (world.df_bag_entries.any (fun e => e.1 == uidKey uid && Bag.Entry.keyMatches e.2.1 k), world)

theorem store_bag_has_eq_false_of_validForNewId {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] (K : Type) [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (h : Prover.World.World.validForNewId (uidKey uid) world = true) :
    (store_bag_has K uid k world).1 = false := by
  apply Bool.eq_false_iff.mpr
  intro hhas
  have hcontains : Prover.World.World.contains_id world (uidKey uid) = true := by
    rw [Prover.World.World.contains_id, List.any_eq_true]
    rw [store_bag_has] at hhas
    simp only [Bool.and_eq_true, List.any_eq_true] at hhas
    rcases hhas with ⟨entry, hmem, hkey, _hmatch⟩
    rcases entry with ⟨eid, keyEntry, sz, st⟩
    have hmem_id : eid ∈ Prover.World.World.id_list world := by
      simp [Prover.World.World.id_list]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨keyEntry, sz, st, hmem⟩))))))))
    exact ⟨eid, hmem_id, hkey⟩
  simp [Prover.World.World.validForNewId, hcontains] at h

@[simp] theorem store_bag_has_bump_user_events {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] (K : Type) [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    (store_bag_has K uid k (Prover.World.World.bump_user_events world)).1 =
      (store_bag_has K uid k world).1 := rfl

@[simp] theorem store_bag_has_allocate_id {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] (K : Type) [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (id : Nat) :
    (store_bag_has K uid k (Prover.World.World.allocate_id world id)).1 =
      (store_bag_has K uid k world).1 := rfl

@[simp] theorem store_bag_borrow_allocate_id {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] (K V : Type) [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (id : Nat) :
    (store_bag_borrow K V uid k (Prover.World.World.allocate_id world id)).1 =
      (store_bag_borrow K V uid k world).1 := by
  unfold store_bag_borrow Prover.World.World.allocate_id
  generalize hfind :
    List.findSome?
      (fun e =>
        if e.1 == uidKey uid && Bag.Entry.keyMatches e.2.1 k
        then some (e.2.2.1, e.2.2.2)
        else none)
      world.df_bag_entries = found
  cases found with
  | none => simp
  | some p =>
      cases p
      simp

@[simp] theorem store_bag_has_set_owned {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] (K : Type) [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (owned : List (Address × Nat × Ob)) :
    (store_bag_has K uid k { world with owned := owned }).1 =
      (store_bag_has K uid k world).1 := rfl

@[simp] theorem store_bag_borrow_set_owned {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] (K V : Type) [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (owned : List (Address × Nat × Ob)) :
    (store_bag_borrow K V uid k { world with owned := owned }).1 =
      (store_bag_borrow K V uid k world).1 := by
  unfold store_bag_borrow
  generalize hfind :
    List.findSome?
      (fun e =>
        if e.1 == uidKey uid && Bag.Entry.keyMatches e.2.1 k
        then some (e.2.2.1, e.2.2.2)
        else none)
      world.df_bag_entries = found
  cases found with
  | none => simp
  | some p =>
      cases p
      simp

@[simp] theorem store_bag_has_object_new {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] (K : Type) [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (ctx : Tx_context.TxContext)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    (store_bag_has K uid k (Object.new ctx world).2.2).1 =
      (store_bag_has K uid k world).1 := by
  simp [Object.new]

@[simp] theorem store_bag_borrow_object_new {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] (K V : Type) [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (ctx : Tx_context.TxContext)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    (store_bag_borrow K V uid k (Object.new ctx world).2.2).1 =
      (store_bag_borrow K V uid k world).1 := by
  simp [Object.new]

@[simp] theorem store_bag_has_object_new_self {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] (K : Type) [hkc : HasCode Df K] [DecidableEq K]
    (k : K) (ctx : Tx_context.TxContext)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    (store_bag_has K (Object.new ctx world).1 k (Object.new ctx world).2.2).1 = false := by
  rw [store_bag_has_object_new]
  exact store_bag_has_eq_false_of_validForNewId K (Object.new ctx world).1 k world
    (Object.new_uid_validForNewId_eq_true ctx world)

def store_bag_remove {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K V : Type)
    [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    : Bag.Bag Bg × Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg) :=
  let bag := (store_bag_borrow K V uid k world).1
  let filtered := world.df_bag_entries.filter
    (fun e => ! (e.1 == uidKey uid && Bag.Entry.keyMatches e.2.1 k))
  (bag, { world with df_bag_entries := filtered })

def store_bag_set.aborts {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (_uid : Object.UID) (_k : K) (_bag : Bag.Bag Bg)
    (_world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) : Bool := false
/-- EFieldAlreadyExists for a bag-valued `dynamic_field::add`. Move's key
collision is TYPE-AGNOSTIC: `add<K, Bag>` aborts when ANY field occupies the
raw key `(uid, k)`, regardless of its value type. The split World model parks
bag-valued df in `df_bag_entries` and every other df value in `df_entries`, so
the check must consult BOTH stores -- `store_bag_has` (bag side) OR `has` (plain
`df_entries` side, the same predicate `dynamic_field::exists_(id, key)` renders
to). Without the `has` disjunct a same-key non-Bag field would be invisible and
the model would fail to abort where real Move does. -/
def store_bag_add.aborts {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K V : Type)
    [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (_bag : Bag.Bag Bg)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) : Bool :=
  (store_bag_has K uid k world).1 || (has K uid k world).1
def store_bag_borrow.aborts {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (_uid : Object.UID) (_k : K) (_world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) : Bool := false
def store_bag_has.aborts {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K : Type)
    [HasCode Df K] [DecidableEq K]
    (_uid : Object.UID) (_k : K) (_world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) : Bool := false
def store_bag_remove.aborts {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (_uid : Object.UID) (_k : K) (_world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) : Bool := false

-- ---------------------------------------------------------------------------
-- World-wellformedness for bag-valued dynamic fields (framework-owned).
--
-- `world_wf w` says every bag parked in `w.df_bag_entries` has unique packed
-- keys (`(storage.map Bag.packedKey).Nodup`). It depends ONLY on
-- `df_bag_entries`, so `world_wf_congr` collapses the preservation goal for
-- any op that leaves that slot untouched -- which is every world/df op
-- except the three df_bag mutators (`store_bag_set` inserts,
-- `store_bag_remove` / `clear_id` filter). Relocated + generalized from a
-- per-package prototype (`specs.WorldWFProto`), which pinned it to ember's
-- concrete `World`; the tactic scripts carry over unchanged.
-- ---------------------------------------------------------------------------

/-- If `List.findSome? f xs = some y` then some element of `xs` maps to
`some y` under `f`. -/
theorem findSome?_mem_of_eq_some {α β : Type} {f : α → Option β}
    {xs : List α} {y : β} (h : xs.findSome? f = some y) :
    ∃ x ∈ xs, f x = some y := by
  obtain ⟨l₁, a, l₂, hxs, hfa, _⟩ := List.findSome?_eq_some_iff.mp h
  exact ⟨a, by subst hxs; simp, hfa⟩

/-- Every bag stored in the world's `df_bag_entries` has unique packed keys. -/
def world_wf {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) : Prop :=
  ∀ e ∈ w.df_bag_entries, ((e.2.2.2).map Bag.packedKey).Nodup

/-- `world_wf` depends only on `df_bag_entries`: worlds that agree there are
`world_wf`-indistinguishable. Every trivial op's preservation is one
application of this. -/
theorem world_wf_congr {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    {w1 w2 : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)}
    (h : w1.df_bag_entries = w2.df_bag_entries) :
    world_wf w1 ↔ world_wf w2 := by
  unfold world_wf
  rw [h]

/-- The empty world is well-formed (`init.df_bag_entries = []`). -/
theorem world_wf_init {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] :
    world_wf (Prover.World.World.init :
      Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) := by
  unfold world_wf
  intro e he
  simp [Prover.World.World.init] at he

-- Trivial preservation: World-level ops that never touch `df_bag_entries`.
@[simp] theorem world_wf_emit_event {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) (e : Ev) :
    world_wf (Prover.World.World.emit_event w e) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_allocate_id {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) (id : Nat) :
    world_wf (Prover.World.World.allocate_id w id) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_transfer_to {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (id : Nat) (addr : Address) (obj : Ob) :
    world_wf (Prover.World.World.transfer_to w id addr obj) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_share {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (id : Nat) (obj : Ob) :
    world_wf (Prover.World.World.share w id obj) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_freeze {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (id : Nat) (obj : Ob) :
    world_wf (Prover.World.World.freeze w id obj) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_delete_object {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) (id : Nat) :
    world_wf (Prover.World.World.delete_object w id) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_receive_record {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (id : Nat) (parent : Address) :
    world_wf (Prover.World.World.receive_record w id parent) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_accum_add {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (addr : Address) (v : BoundedNat (2^256)) :
    world_wf (Prover.World.World.accum_add w addr v) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_accum_sub {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (addr : Address) (v : BoundedNat (2^256)) :
    world_wf (Prover.World.World.accum_sub w addr v) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_bump_user_events {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    world_wf (Prover.World.World.bump_user_events w) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_reset_user_events {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    world_wf (Prover.World.World.reset_user_events w) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_reset_created {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    world_wf (Prover.World.World.reset_created w) ↔ world_wf w :=
  world_wf_congr rfl

-- Trivial preservation at the ALLOCATING NATIVE heads (WorldFrameLemmas
-- migration): the invariant depends only on `df_bag_entries`, which no
-- allocator touches. Stated at the native's own head so a goal over a world
-- threaded through a constructor collapses without waiting for the
-- `new_world` transport chain.
@[simp] theorem world_wf_object_new {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (ctx : Tx_context.TxContext)
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    world_wf ((Object.new ctx w).2.2) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_object_new_ghost {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (ctx : Tx_context.TxContext)
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) (g : Object.UID) :
    world_wf ((Object.new__ghost ctx w g).2.2.1) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_table_new {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (K V : Type) [BEq K] [Inhabited V] (ctx : Tx_context.TxContext)
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    world_wf ((Table.new K V ctx w).2.2) ↔ world_wf w :=
  world_wf_congr rfl

@[simp] theorem world_wf_bag_new {U : Type} [Universe U] {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] (ctx : Tx_context.TxContext)
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    world_wf ((Bag.new (U := U) ctx w).2.2) ↔ world_wf w :=
  world_wf_congr rfl

-- Trivial preservation: df ops that touch only `df_entries` (not the bag slot).
@[simp] theorem world_wf_set {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (K V : Type) [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : Object.UID) (k : K) (v : V)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    world_wf (set K V uid k v world) ↔ world_wf world :=
  world_wf_congr rfl

@[simp] theorem world_wf_add {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (K V : Type) [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : Object.UID) (k : K) (v : V)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    world_wf (add K V uid k v world) ↔ world_wf world :=
  world_wf_congr rfl

@[simp] theorem world_wf_remove {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (K V : Type) [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    world_wf (remove K V uid k world).2 ↔ world_wf world :=
  world_wf_congr rfl

@[simp] theorem world_wf_store_remove_if_exists {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (K V : Type) [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    world_wf (store_remove_if_exists K V uid k world).2 ↔ world_wf world :=
  world_wf_congr rfl

@[simp] theorem world_wf_store_bag_borrow {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (K V : Type) [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    world_wf (store_bag_borrow K V uid k world).2 ↔ world_wf world :=
  world_wf_congr (by rw [store_bag_borrow]; split <;> rfl)

@[simp] theorem world_wf_set_owned {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (owned : List (Address × Nat × Ob)) :
    world_wf { world with owned := owned } ↔ world_wf world :=
  world_wf_congr rfl

@[simp] theorem world_wf_store_bag_has {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (K : Type) [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    world_wf (store_bag_has K uid k world).2 ↔ world_wf world :=
  world_wf_congr rfl

/-- Read side: the bag `store_bag_borrow` returns is key-unique whenever the
world is well-formed. The returned storage is either some stored entry's
list (key-unique by `world_wf`) or the default/empty bag. -/
theorem store_bag_borrow_keysUnique {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (K V : Type) [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K)
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (hwf : world_wf w) :
    (((store_bag_borrow K V uid k w).1.storage).map Bag.packedKey).Nodup := by
  have hstorage : (default : Bag.Bag Bg).storage = [] := rfl
  unfold store_bag_borrow
  cases h_find :
      List.findSome?
        (fun e =>
          if e.1 == uidKey uid &&
              Bag.Entry.keyMatches e.2.1 k then
            some (e.2.2.1, e.2.2.2)
          else
            none)
        w.df_bag_entries
  · simp [hstorage]
  · rename_i found
    obtain ⟨sz, st⟩ := found
    obtain ⟨e, hmem, hfe⟩ := findSome?_mem_of_eq_some h_find
    have hst : st = e.2.2.2 := by
      split at hfe
      · rw [Option.some.injEq, Prod.mk.injEq] at hfe
        exact hfe.2.symm
      · simp at hfe
    show ((st).map Bag.packedKey).Nodup
    rw [hst]
    exact hwf e hmem

/-- Write side: `store_bag_set` preserves `world_wf` when the inserted bag is
key-unique. The new head entry's storage is the inserted `bag.storage`
(`Bag.keysUnique`); the filtered tail is a sublist of the old
`df_bag_entries`, so each surviving entry keeps its witness. -/
theorem store_bag_set_world_wf {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (K V : Type) [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (bag : Bag.Bag Bg)
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (hwf : world_wf w)
    (hbag : Bag.keysUnique bag) :
    world_wf (store_bag_set K V uid k bag w) := by
  unfold world_wf
  intro e he
  simp only [store_bag_set, List.mem_cons, List.mem_filter] at he
  rcases he with rfl | ⟨hmem, _⟩
  · exact hbag
  · exact hwf e hmem

/-- Removal preserves `world_wf`: the surviving `df_bag_entries` are a
sublist (pure `filter`) of the original, so each keeps its per-bag
key-uniqueness. -/
theorem store_bag_remove_world_wf {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (K V : Type) [hkc : HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K)
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg))
    (hwf : world_wf w) :
    world_wf (store_bag_remove K V uid k w).2 := by
  unfold world_wf
  intro e he
  simp only [store_bag_remove, List.mem_filter] at he
  exact hwf e he.1

/-- `Prover.World.World.clear_id` preserves `world_wf`: it only `filter`s
`df_bag_entries`, so each surviving entry inherits its witness. -/
theorem world_wf_clear_id {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg]
    (w : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) (id : Nat)
    (hwf : world_wf w) :
    world_wf (Prover.World.World.clear_id w id) := by
  unfold world_wf
  intro e he
  simp only [Prover.World.World.clear_id, List.mem_filter] at he
  exact hwf e he.1

-- ---------------------------------------------------------------------------
-- Pass 2: world-frame completeness for the df writers. The plain-df writers
-- touch ONLY `df_entries` and the bag-store writers ONLY `df_bag_entries`;
-- each gets the frame for the OTHER df store plus the event/object fields
-- (`events`, `owned`, `shared`, `frozen`, `tx_user_events`). All rfl
-- `@[simp]` frames. `add` first collapses onto `set` (the world actions are
-- one definition -- mirrors the landed `store_bag_add_eq_store_bag_set`).
-- ---------------------------------------------------------------------------

/-- The plain-df `add` World action IS `set` (only the abort side differs);
reduce it so every `set` frame and writeback lemma fires at add sites too. -/
@[simp] theorem add_eq_set {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : Object.UID) (k : K) (v : V)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    add K V uid k v world = set K V uid k v world := rfl

section WriterFrames

variable {Ev Ob Be Df Bg : Type} [Universe Df] [Universe Bg]

@[simp] theorem set_df_bag_entries (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : Object.UID) (k : K) (v : V)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    (set K V uid k v world).df_bag_entries = world.df_bag_entries := rfl
@[simp] theorem set_events (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : Object.UID) (k : K) (v : V)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    (set K V uid k v world).events = world.events := rfl
@[simp] theorem set_owned (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : Object.UID) (k : K) (v : V)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    (set K V uid k v world).owned = world.owned := rfl
@[simp] theorem set_shared (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : Object.UID) (k : K) (v : V)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    (set K V uid k v world).shared = world.shared := rfl
@[simp] theorem set_frozen (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : Object.UID) (k : K) (v : V)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    (set K V uid k v world).frozen = world.frozen := rfl
@[simp] theorem set_tx_user_events (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : Object.UID) (k : K) (v : V)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    (set K V uid k v world).tx_user_events = world.tx_user_events := rfl

@[simp] theorem remove_snd_df_bag_entries (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    ((remove K V uid k world).2).df_bag_entries = world.df_bag_entries := rfl
@[simp] theorem remove_snd_events (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    ((remove K V uid k world).2).events = world.events := rfl
@[simp] theorem remove_snd_owned (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    ((remove K V uid k world).2).owned = world.owned := rfl
@[simp] theorem remove_snd_shared (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    ((remove K V uid k world).2).shared = world.shared := rfl
@[simp] theorem remove_snd_frozen (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    ((remove K V uid k world).2).frozen = world.frozen := rfl
@[simp] theorem remove_snd_tx_user_events (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) Be) :
    ((remove K V uid k world).2).tx_user_events = world.tx_user_events := rfl

@[simp] theorem store_bag_set_df_entries (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (bag : Bag.Bag Bg)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    (store_bag_set K V uid k bag world).df_entries = world.df_entries := rfl
@[simp] theorem store_bag_set_events (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (bag : Bag.Bag Bg)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    (store_bag_set K V uid k bag world).events = world.events := rfl
@[simp] theorem store_bag_set_owned (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (bag : Bag.Bag Bg)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    (store_bag_set K V uid k bag world).owned = world.owned := rfl
@[simp] theorem store_bag_set_shared (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (bag : Bag.Bag Bg)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    (store_bag_set K V uid k bag world).shared = world.shared := rfl
@[simp] theorem store_bag_set_frozen (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (bag : Bag.Bag Bg)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    (store_bag_set K V uid k bag world).frozen = world.frozen := rfl
@[simp] theorem store_bag_set_tx_user_events (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K) (bag : Bag.Bag Bg)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    (store_bag_set K V uid k bag world).tx_user_events = world.tx_user_events := rfl

@[simp] theorem store_bag_remove_snd_df_entries (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    ((store_bag_remove K V uid k world).2).df_entries = world.df_entries := rfl
@[simp] theorem store_bag_remove_snd_events (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    ((store_bag_remove K V uid k world).2).events = world.events := rfl
@[simp] theorem store_bag_remove_snd_owned (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    ((store_bag_remove K V uid k world).2).owned = world.owned := rfl
@[simp] theorem store_bag_remove_snd_shared (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    ((store_bag_remove K V uid k world).2).shared = world.shared := rfl
@[simp] theorem store_bag_remove_snd_frozen (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    ((store_bag_remove K V uid k world).2).frozen = world.frozen := rfl
@[simp] theorem store_bag_remove_snd_tx_user_events (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : Object.UID) (k : K)
    (world : Prover.World.World Ev Ob (Bag.Entry Df) (Bag.Entry Bg)) :
    ((store_bag_remove K V uid k world).2).tx_user_events = world.tx_user_events := rfl

end WriterFrames

end Dynamic_field

@[move_effect]
theorem dynamic_field_add_aborts_eq_has
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (v : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.add.aborts K V uid k v world =
      (_root_.Dynamic_field.has K uid k world).1 := by
  rfl

@[move_effect]
theorem dynamic_field_borrow_aborts_eq_not_has
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.borrow.aborts K V uid k world =
      !(_root_.Dynamic_field.has K uid k world).1 := by
  rfl

@[move_effect]
theorem dynamic_field_remove_aborts_eq_not_has
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.remove.aborts K V uid k world =
      !(_root_.Dynamic_field.has K uid k world).1 := by
  rfl

@[move_effect]
theorem dynamic_field_set_aborts_eq_false
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (v : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.set.aborts K V uid k v world = false := by
  rfl

@[move_effect]
theorem dynamic_field_store_bag_add_aborts_eq_has
    {Ev Ob Df Bg K : Type} [Universe Df] [Universe Bg] [HasCode Df K]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (bag : _root_.Bag.Bag Bg)
    (world :
      _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    _root_.Dynamic_field.store_bag_add.aborts
        K (_root_.Bag.Bag Bg) uid k bag world =
      ((_root_.Dynamic_field.store_bag_has K uid k world).1 ||
        (_root_.Dynamic_field.has K uid k world).1) := by
  rfl

@[move_effect]
theorem dynamic_field_store_bag_set_aborts_eq_false
    {Ev Ob Df Bg K : Type} [Universe Df] [Universe Bg] [HasCode Df K]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (bag : _root_.Bag.Bag Bg)
    (world :
      _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    _root_.Dynamic_field.store_bag_set.aborts
        K (_root_.Bag.Bag Bg) uid k bag world = false := by
  rfl

-- Total abort faces of the remaining `store_bag_*` ops, bridged like their
-- `set`/`add` siblings so no transitive caller acquires a spurious abort.

@[move_effect]
theorem dynamic_field_store_bag_borrow_aborts_eq_false
    {Ev Ob Df Bg K V : Type} [Universe Df] [Universe Bg] [HasCode Df K]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world :
      _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    _root_.Dynamic_field.store_bag_borrow.aborts K V uid k world = false := by
  rfl

@[move_effect]
theorem dynamic_field_store_bag_has_aborts_eq_false
    {Ev Ob Df Bg K : Type} [Universe Df] [Universe Bg] [HasCode Df K]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world :
      _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    _root_.Dynamic_field.store_bag_has.aborts K uid k world = false := by
  rfl

@[move_effect]
theorem dynamic_field_store_bag_remove_aborts_eq_false
    {Ev Ob Df Bg K V : Type} [Universe Df] [Universe Bg] [HasCode Df K]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world :
      _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    _root_.Dynamic_field.store_bag_remove.aborts K V uid k world = false := by
  rfl

/-- `store_remove_if_exists` and `remove` share one body (they differ only in
their abort faces), so every `remove` transport fires at
`remove_if_exists` sites after this rewrite. -/
@[simp]
theorem dynamic_field_store_remove_if_exists_eq_remove
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.store_remove_if_exists K V uid k world =
      _root_.Dynamic_field.remove K V uid k world := rfl

private theorem list_any_filter_other_fst
    {A : Type} (entries : List (Nat × A)) (updated queried : Nat)
    (drop query : Nat × A → Bool) (h_ne : queried ≠ updated) :
    (entries.filter fun e => !(e.1 == updated && drop e)).any
        (fun e => e.1 == queried && query e) =
      entries.any (fun e => e.1 == queried && query e) := by
  rw [List.any_filter]
  apply congrArg (fun p : Nat × A → Bool => entries.any p)
  funext e
  by_cases h_query : e.1 = queried
  · subst queried
    have h_updated : (e.1 == updated) = false := by
      exact Bool.eq_false_iff.mpr (fun h => h_ne (beq_iff_eq.mp h))
    simp only [h_updated, Bool.false_and, Bool.not_false, beq_self_eq_true,
      Bool.true_and]
  · have h_query_beq : (e.1 == queried) = false := by
      exact Bool.eq_false_iff.mpr (fun h => h_query (beq_iff_eq.mp h))
    simp only [h_query_beq, Bool.false_and, Bool.and_false]

theorem dynamic_field_has_set_uid_ne
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K]
    (updated queried : _root_.Object.UID) (updatedKey queryKey : K) (value : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h_ne :
      _root_.Dynamic_field.uidKey queried ≠ _root_.Dynamic_field.uidKey updated) :
    (_root_.Dynamic_field.has K queried queryKey
      (_root_.Dynamic_field.set K V updated updatedKey value world)).1 =
      (_root_.Dynamic_field.has K queried queryKey world).1 := by
  unfold _root_.Dynamic_field.has _root_.Dynamic_field.set
  simp only [List.any_cons]
  have h_head :
      (_root_.Dynamic_field.uidKey updated ==
        _root_.Dynamic_field.uidKey queried) = false := by
    exact Bool.eq_false_iff.mpr (fun h => h_ne (beq_iff_eq.mp h).symm)
  simp only [h_head, Bool.false_and, Bool.false_or]
  exact list_any_filter_other_fst world.df_entries
    (_root_.Dynamic_field.uidKey updated)
    (_root_.Dynamic_field.uidKey queried)
    (fun e => _root_.Bag.Entry.keyMatches e.2 updatedKey)
    (fun e => _root_.Bag.Entry.keyMatches e.2 queryKey)
    h_ne

theorem dynamic_field_has_add_uid_ne
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K]
    (updated queried : _root_.Object.UID) (updatedKey queryKey : K) (value : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h_ne :
      _root_.Dynamic_field.uidKey queried ≠ _root_.Dynamic_field.uidKey updated) :
    (_root_.Dynamic_field.has K queried queryKey
      (_root_.Dynamic_field.add K V updated updatedKey value world)).1 =
      (_root_.Dynamic_field.has K queried queryKey world).1 := by
  exact dynamic_field_has_set_uid_ne updated queried updatedKey queryKey value world h_ne

@[move_effect]
theorem DynamicFieldEffects.remove_fst_eq_borrow
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (key : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.remove K V uid key world).1 =
      (_root_.Dynamic_field.borrow K V uid key world).1 := by
  rfl

@[move_effect]
theorem dynamic_field_has_remove_same
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (key : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K uid key
      (_root_.Dynamic_field.remove K V uid key world).2).1 = false := by
  unfold _root_.Dynamic_field.has _root_.Dynamic_field.remove
  simp only [List.any_filter]
  apply List.any_eq_false.mpr
  intro entry _
  by_cases h_match :
      (entry.1 == _root_.Dynamic_field.uidKey uid &&
        _root_.Bag.Entry.keyMatches entry.2 key) = true
  · simp [h_match]
  · simp [h_match]

@[simp, move_effect]
theorem dynamic_field_has_set_same
    {Ev Ob Be Df K V : Type} [Universe Df] [hkc : HasCode Df K]
    [hvc : HasCode Df V] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (v : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K uid k
      (_root_.Dynamic_field.set K V uid k v world)).1 = true := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [_root_.Dynamic_field.has, _root_.Dynamic_field.set,
        _root_.Bag.Entry.keyMatches]

@[simp, move_effect]
theorem dynamic_field_borrow_set_same
    {Ev Ob Be Df K V : Type} [Universe Df] [hkc : HasCode Df K]
    [hvc : HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (k : K) (v : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.borrow K V uid k
      (_root_.Dynamic_field.set K V uid k v world)).1 = v := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [_root_.Dynamic_field.borrow, _root_.Dynamic_field.set,
        _root_.Bag.Entry.keyMatches]

@[simp]
theorem dynamic_field_has_bump_user_events
    {Ev Ob Be Df K : Type} [Universe Df] [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K uid k
      (_root_.Prover.World.World.bump_user_events world)).1 =
      (_root_.Dynamic_field.has K uid k world).1 := by
  simp [_root_.Dynamic_field.has, _root_.Prover.World.World.bump_user_events]

@[simp]
theorem dynamic_field_borrow_bump_user_events
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.borrow K V uid k
      (_root_.Prover.World.World.bump_user_events world)).1 =
      (_root_.Dynamic_field.borrow K V uid k world).1 := by
  simp [_root_.Dynamic_field.borrow, _root_.Prover.World.World.bump_user_events]

@[simp]
theorem dynamic_field_has_snd
    {Ev Ob Be Df K : Type} [Universe Df] [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K uid k world).2 = world := by
  simp [_root_.Dynamic_field.has]

-- df_entries-side mirror of `store_bag_has_object_new`: `object::new` records
-- the allocation in `allocated_ids` and leaves `df_entries` untouched, so the
-- plain df presence check is invariant under it.
@[simp]
theorem dynamic_field_has_object_new
    {Ev Ob Be Df K : Type} [Universe Df] [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K uid k (_root_.Object.new ctx world).2.2).1 =
      (_root_.Dynamic_field.has K uid k world).1 := by
  have hdf : ((_root_.Object.new ctx world).2.2).df_entries = world.df_entries := by
    unfold _root_.Object.new; rfl
  simp [_root_.Dynamic_field.has, hdf]

@[simp]
theorem dynamic_field_borrow_snd
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.borrow K V uid k world).2 = world := by
  simp [_root_.Dynamic_field.borrow]

@[simp]
theorem dynamic_field_has_set_bump_same
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (v : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K uid k
      (_root_.Dynamic_field.set K V uid k v world).bump_user_events).1 =
      true := by
  rw [dynamic_field_has_bump_user_events]
  exact dynamic_field_has_set_same uid k v world

@[simp]
theorem dynamic_field_borrow_after_has_set_bump_same
    {Ev Ob Be Df K V : Type} [Universe Df] [HasCode Df K] [HasCode Df V]
    [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (k : K) (v : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.borrow K V uid k
      (_root_.Dynamic_field.has K uid k
        (_root_.Dynamic_field.set K V uid k v world).bump_user_events).2).1 =
      v := by
  rw [dynamic_field_has_snd]
  rw [dynamic_field_borrow_bump_user_events]
  exact dynamic_field_borrow_set_same uid k v world

@[simp, move_effect]
theorem dynamic_field_store_bag_has_set_same
    {Ev Ob Df Bg K : Type} [Universe Df] [Universe Bg] [hkc : HasCode Df K]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (bag : _root_.Bag.Bag Bg)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_has K uid k
      (_root_.Dynamic_field.store_bag_set K (_root_.Bag.Bag Bg) uid k bag world)).1 =
      true := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    simp [_root_.Dynamic_field.store_bag_has, _root_.Dynamic_field.store_bag_set,
      _root_.Bag.Entry.keyMatches]

@[simp, move_effect]
theorem dynamic_field_store_bag_borrow_set_contains_with_type_same
    {Ev Ob Df Bg K BK BV : Type} [Universe Df] [Universe Bg]
    [hkc : HasCode Df K] [DecidableEq K] [hbkc : HasCode Bg BK]
    [hbvc : HasCode Bg BV] [DecidableEq BK]
    (uid : _root_.Object.UID) (k : K) (bag : _root_.Bag.Bag Bg)
    (bagKey : BK)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    _root_.Bag.contains_with_type BK BV
        (_root_.Dynamic_field.store_bag_borrow K (_root_.Bag.Bag Bg) uid k
          (_root_.Dynamic_field.store_bag_set K (_root_.Bag.Bag Bg) uid k bag world)).1
        bagKey =
      _root_.Bag.contains_with_type BK BV bag bagKey := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hbkc with
    | mk bkcode bkproof =>
      cases bkproof
      cases hbvc with
      | mk bvcode bvproof =>
        cases bvproof
        simp [_root_.Dynamic_field.store_bag_borrow, _root_.Dynamic_field.store_bag_set,
          _root_.Bag.contains_with_type, _root_.Bag.Entry.keyMatches]

@[simp, move_effect]
theorem dynamic_field_store_bag_borrow_set_contains_same
    {Ev Ob Df Bg K BK : Type} [Universe Df] [Universe Bg]
    [hkc : HasCode Df K] [DecidableEq K] [hbkc : HasCode Bg BK]
    [DecidableEq BK]
    (uid : _root_.Object.UID) (k : K) (bag : _root_.Bag.Bag Bg)
    (bagKey : BK)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    _root_.Bag.contains BK
        (_root_.Dynamic_field.store_bag_borrow K (_root_.Bag.Bag Bg) uid k
          (_root_.Dynamic_field.store_bag_set K (_root_.Bag.Bag Bg) uid k bag world)).1
        bagKey =
      _root_.Bag.contains BK bag bagKey := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hbkc with
    | mk bkcode bkproof =>
      cases bkproof
      simp [_root_.Dynamic_field.store_bag_borrow, _root_.Dynamic_field.store_bag_set,
        _root_.Bag.contains, _root_.Bag.Entry.keyMatches]

@[simp]
theorem dynamic_field_store_bag_borrow_set_length_same
    {Ev Ob Df Bg K : Type} [Universe Df] [Universe Bg]
    [hkc : HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (bag : _root_.Bag.Bag Bg)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    _root_.Bag.length
        (_root_.Dynamic_field.store_bag_borrow K (_root_.Bag.Bag Bg) uid k
          (_root_.Dynamic_field.store_bag_set K (_root_.Bag.Bag Bg) uid k bag world)).1 =
      _root_.Bag.length bag := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    simp [_root_.Dynamic_field.store_bag_borrow, _root_.Dynamic_field.store_bag_set,
      _root_.Bag.length, _root_.Bag.Entry.keyMatches]

theorem dynamic_field_store_bag_has_of_borrow_contains
    {Ev Ob Df Bg K BK : Type} [Universe Df] [Universe Bg]
    [hkc : HasCode Df K] [DecidableEq K] [hbkc : HasCode Bg BK]
    [DecidableEq BK]
    (uid : _root_.Object.UID) (k : K) (bagKey : BK)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg))
    (h_contains :
      _root_.Bag.contains BK
        (_root_.Dynamic_field.store_bag_borrow K (_root_.Bag.Bag Bg) uid k world).1
        bagKey = true) :
    (_root_.Dynamic_field.store_bag_has K uid k world).1 = true := by
  unfold _root_.Dynamic_field.store_bag_borrow at h_contains
  unfold _root_.Dynamic_field.store_bag_has
  let finder :
      (Nat × _root_.Bag.Entry Df × BoundedNat (2^64) ×
          List (_root_.Bag.Entry Bg)) →
        Option (BoundedNat (2^64) × List (_root_.Bag.Entry Bg)) :=
    fun e =>
      if e.1 == _root_.Dynamic_field.uidKey uid &&
          _root_.Bag.Entry.keyMatches e.2.1 k then
        some (e.2.2.1, e.2.2.2)
      else
        none
  change
    _root_.Bag.contains BK
      (match List.findSome? finder world.df_bag_entries with
      | some (sz, st) => ({ (default : _root_.Bag.Bag Bg) with
          size := sz, storage := st }, world)
      | none => (default, world)).1
      bagKey = true at h_contains
  change
    world.df_bag_entries.any
      (fun e => e.1 == _root_.Dynamic_field.uidKey uid &&
        _root_.Bag.Entry.keyMatches e.2.1 k) = true
  cases h_find : List.findSome? finder world.df_bag_entries with
  | none =>
      rw [h_find] at h_contains
      have h_default_storage :
          (default : _root_.Bag.Bag Bg).storage = [] := rfl
      simp [_root_.Bag.contains, h_default_storage] at h_contains
  | some found =>
      have h_isSome :
          (List.findSome? finder world.df_bag_entries).isSome := by
        simp [h_find]
      rcases (List.findSome?_isSome_iff.mp h_isSome) with
        ⟨entry, h_mem, h_entry_some⟩
      have h_key :
          (entry.1 == _root_.Dynamic_field.uidKey uid &&
            _root_.Bag.Entry.keyMatches entry.2.1 k) = true := by
        have h_entry_some' := h_entry_some
        simp [finder] at h_entry_some'
        simp [h_entry_some'.1, h_entry_some'.2]
      exact List.any_eq_true.mpr ⟨entry, h_mem, h_key⟩

@[simp, move_effect]
theorem dynamic_field_store_bag_borrow_set_borrow_same
    {Ev Ob Df Bg K BK BV : Type} [Universe Df] [Universe Bg]
    [hkc : HasCode Df K] [DecidableEq K] [hbkc : HasCode Bg BK]
    [hbvc : HasCode Bg BV] [DecidableEq BK] [Inhabited BV]
    (uid : _root_.Object.UID) (k : K) (bag : _root_.Bag.Bag Bg)
    (bagKey : BK)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    _root_.Bag.borrow BK BV
        (_root_.Dynamic_field.store_bag_borrow K (_root_.Bag.Bag Bg) uid k
          (_root_.Dynamic_field.store_bag_set K (_root_.Bag.Bag Bg) uid k bag world)).1
        bagKey =
      _root_.Bag.borrow BK BV bag bagKey := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hbkc with
    | mk bkcode bkproof =>
      cases bkproof
      cases hbvc with
      | mk bvcode bvproof =>
        cases bvproof
        simp [_root_.Dynamic_field.store_bag_borrow, _root_.Dynamic_field.store_bag_set,
          _root_.Bag.borrow, _root_.Bag.Entry.keyMatches]

@[simp]
theorem dynamic_field_store_bag_has_bump_user_events
    {Ev Ob Df Bg K : Type} [Universe Df] [Universe Bg] [HasCode Df K]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_has K uid k
      (_root_.Prover.World.World.bump_user_events world)).1 =
      (_root_.Dynamic_field.store_bag_has K uid k world).1 :=
  _root_.Dynamic_field.store_bag_has_bump_user_events K uid k world

@[simp]
theorem dynamic_field_store_bag_has_snd
    {Ev Ob Df Bg K : Type} [Universe Df] [Universe Bg] [HasCode Df K]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_has K uid k world).2 = world := by
  simp [_root_.Dynamic_field.store_bag_has]

@[simp]
theorem dynamic_field_store_bag_borrow_snd
    {Ev Ob Df Bg K V : Type} [Universe Df] [Universe Bg] [HasCode Df K]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_borrow K V uid k world).2 = world := by
  rw [_root_.Dynamic_field.store_bag_borrow]
  split <;> rfl

@[simp]
theorem dynamic_field_store_bag_borrow_bump_user_events
    {Ev Ob Df Bg K V : Type} [Universe Df] [Universe Bg] [HasCode Df K]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_borrow K V uid k
      (_root_.Prover.World.World.bump_user_events world)).1 =
      (_root_.Dynamic_field.store_bag_borrow K V uid k world).1 := by
  unfold _root_.Dynamic_field.store_bag_borrow _root_.Prover.World.World.bump_user_events
  cases h_find :
      List.findSome?
        (fun e =>
          if e.1 == _root_.Dynamic_field.uidKey uid &&
              _root_.Bag.Entry.keyMatches e.2.1 k then
            some (e.2.2.1, e.2.2.2)
          else
            none)
        world.df_bag_entries
  · simp [h_find]
  · rename_i found
    cases found
    simp [h_find]

@[simp]
theorem dynamic_field_store_bag_has_transfer_to
    {Ev Ob Df Bg K : Type} [Universe Df] [Universe Bg] [HasCode Df K]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg))
    (id : Nat) (addr : Address) (obj : Ob) :
    (_root_.Dynamic_field.store_bag_has K uid k
      (_root_.Prover.World.World.transfer_to world id addr obj)).1 =
      (_root_.Dynamic_field.store_bag_has K uid k world).1 := by
  simp [_root_.Dynamic_field.store_bag_has, _root_.Prover.World.World.transfer_to]

@[simp]
theorem dynamic_field_store_bag_borrow_transfer_to
    {Ev Ob Df Bg K V : Type} [Universe Df] [Universe Bg] [HasCode Df K]
    [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg))
    (id : Nat) (addr : Address) (obj : Ob) :
    (_root_.Dynamic_field.store_bag_borrow K V uid k
      (_root_.Prover.World.World.transfer_to world id addr obj)).1 =
      (_root_.Dynamic_field.store_bag_borrow K V uid k world).1 := by
  unfold _root_.Dynamic_field.store_bag_borrow _root_.Prover.World.World.transfer_to
  cases h_find :
      List.findSome?
        (fun e =>
          if e.1 == _root_.Dynamic_field.uidKey uid &&
              _root_.Bag.Entry.keyMatches e.2.1 k then
            some (e.2.2.1, e.2.2.2)
          else
            none)
        world.df_bag_entries
  · simp [h_find]
  · rename_i found
    cases found
    simp [h_find]

-- ---------------------------------------------------------------------------
-- UID-freshness corollary (M5 part c): `dynamic_field::add` does not abort at a
-- UID freshly produced by `object::new` in the world `new` returns. `add.aborts`
-- is EFieldAlreadyExists (key present); a fresh uid keys no df entry
-- (`Object.new_uid_no_df_entry`, ObjectNatives.lean), so the create-side face is
-- abort-free. Proven, not axiomatized -- the World model already encodes the
-- freshness (see the note on `Object.new_uid_no_df_entry`). The @[simp]
-- corollary discharges `versioned::create.aborts`,
-- `validator_wrapper::create_v1.aborts`, and the request-add-validator-candidate
-- create branch with no glue beyond the standard `Mutation.val_*` @[simp]s.
-- ---------------------------------------------------------------------------

/-- Monotonicity: a conjunctive `any` is false whenever its first conjunct's
`any` already is. -/
theorem any_and_eq_false_of_any_eq_false {α : Type} (l : List α) (p q : α → Bool)
    (h : l.any p = false) : l.any (fun e => p e && q e) = false := by
  apply Bool.eq_false_iff.mpr
  intro hany
  rw [List.any_eq_true] at hany
  rcases hany with ⟨x, hx, hpq⟩
  have hp : p x = true := by
    cases hc : p x with
    | true => rfl
    | false => rw [hc] at hpq; simp at hpq
  have hcontra : l.any p = true := List.any_eq_true.mpr ⟨x, hx, hp⟩
  rw [hcontra] at h
  simp at h

/-- df_entries-side mirror of `store_bag_has_eq_false_of_validForNewId`: a uid
that is `validForNewId` in `world` keys no entry in `world.df_entries`, so the
plain df presence check is false there (its parent ids are part of `id_list`).
Consumed by the create-side strengthened `store_bag_add.aborts` (the `has`
disjunct) when the bag is added on a fresh vault uid. -/
theorem dynamic_field_has_eq_false_of_validForNewId {Ev Ob Be Df : Type}
    [Universe Df] (K : Type) [hkc : HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h : _root_.Prover.World.World.validForNewId (_root_.Dynamic_field.uidKey uid) world = true) :
    (_root_.Dynamic_field.has K uid k world).1 = false := by
  have hany :=
    _root_.Object.df_entries_any_eq_false_of_validForNewId
      (_root_.Dynamic_field.uidKey uid) world h
  simpa [_root_.Dynamic_field.has] using
    any_and_eq_false_of_any_eq_false world.df_entries
      (fun e : Nat × _root_.Bag.Entry Df => e.1 == _root_.Dynamic_field.uidKey uid)
      (fun e : Nat × _root_.Bag.Entry Df => _root_.Bag.Entry.keyMatches e.2 k)
      hany

/-! ### Freshness at the ORIGINAL world (WorldFrameLemmas migration)

The world-frame batteries normalise a chained world back to the `world` a
constructor chain started from. What remains is a presence check for a uid
`object::new` minted FROM that world, against that same world -- and the
`_object_new` lemmas of this file are stated one hop later (at
`(Object.new ctx w).2.2`) and so do not match that normal form. -/

@[simp] theorem dynamic_field_store_bag_has_object_new_uid (K : Type) {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] [HasCode Df K] [DecidableEq K]
    (k : K) (ctx : _root_.Tx_context.TxContext)
    (w : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_has K (_root_.Object.new ctx w).1 k w).1 = false :=
  _root_.Dynamic_field.store_bag_has_eq_false_of_validForNewId K
    (_root_.Object.new ctx w).1 k w
    (_root_.Object.new_uid_validForNewId_eq_true ctx w)

@[simp] theorem dynamic_field_has_object_new_uid (K : Type) {Ev Ob Be Df : Type}
    [Universe Df] [HasCode Df K] [DecidableEq K]
    (k : K) (ctx : _root_.Tx_context.TxContext)
    (w : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K (_root_.Object.new ctx w).1 k w).1 = false :=
  dynamic_field_has_eq_false_of_validForNewId K (_root_.Object.new ctx w).1 k w
    (_root_.Object.new_uid_validForNewId_eq_true ctx w)

/-- `dynamic_field::add` cannot hit EFieldAlreadyExists on a uid minted
from the same world (its abort face IS the `df_entries` presence check). -/
@[simp] theorem dynamic_field_add_aborts_object_new_uid (K V : Type) {Ev Ob Be Df : Type}
    [Universe Df] [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (k : K) (v : V) (ctx : _root_.Tx_context.TxContext)
    (w : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.add.aborts K V (_root_.Object.new ctx w).1 k v w = false :=
  dynamic_field_has_object_new_uid K k ctx w

/-- Bag-valued `dynamic_field::add` on a uid minted from the same world.
Move's key collision is type-agnostic, so the abort face is
`store_bag_has || has`; a fresh uid keys neither store. -/
@[simp] theorem dynamic_field_store_bag_add_aborts_object_new_uid
    (K V : Type) {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] [HasCode Df K] [DecidableEq K]
    (k : K) (bag : _root_.Bag.Bag Bg) (ctx : _root_.Tx_context.TxContext)
    (w : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    _root_.Dynamic_field.store_bag_add.aborts K V (_root_.Object.new ctx w).1 k bag w
      = false := by
  rw [_root_.Dynamic_field.store_bag_add.aborts,
    dynamic_field_store_bag_has_object_new_uid K k ctx w,
    dynamic_field_has_object_new_uid K k ctx w]
  rfl

/-- Reading a bag-valued df at a uid minted from the same world yields
the default (empty) bag: nothing is stored there. Lets a create-side
`_correct` proof read back through the fresh-uid `add` without unfolding
the store. -/
theorem dynamic_field_store_bag_borrow_object_new_uid (K V : Type) {Ev Ob Df Bg : Type}
    [Universe Df] [Universe Bg] [HasCode Df K] [DecidableEq K]
    (k : K) (ctx : _root_.Tx_context.TxContext)
    (w : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_borrow K V (_root_.Object.new ctx w).1 k w).1
      = (default : _root_.Bag.Bag Bg) := by
  have hany : w.df_bag_entries.any
      (fun e => e.1 == _root_.Dynamic_field.uidKey (_root_.Object.new ctx w).1 &&
        _root_.Bag.Entry.keyMatches e.2.1 k) = false :=
    dynamic_field_store_bag_has_object_new_uid K k ctx w
  have hnone : w.df_bag_entries.findSome?
      (fun e =>
        if e.1 == _root_.Dynamic_field.uidKey (_root_.Object.new ctx w).1 &&
            _root_.Bag.Entry.keyMatches e.2.1 k
        then some (e.2.2.1, e.2.2.2) else none) = none := by
    apply List.findSome?_eq_none_iff.mpr
    intro e he
    have hfalse : (e.1 == _root_.Dynamic_field.uidKey (_root_.Object.new ctx w).1 &&
        _root_.Bag.Entry.keyMatches e.2.1 k) = false := by
      cases hc : (e.1 == _root_.Dynamic_field.uidKey (_root_.Object.new ctx w).1 &&
          _root_.Bag.Entry.keyMatches e.2.1 k) with
      | false => rfl
      | true =>
          exfalso
          have htrue : w.df_bag_entries.any
              (fun e => e.1 == _root_.Dynamic_field.uidKey (_root_.Object.new ctx w).1 &&
                _root_.Bag.Entry.keyMatches e.2.1 k) = true :=
            List.any_eq_true.mpr ⟨e, he, hc⟩
          rw [hany] at htrue
          exact Bool.noConfusion htrue
    simp [hfalse]
  simp only [_root_.Dynamic_field.store_bag_borrow, hnone]

@[simp] theorem dynamic_field_add_aborts_object_new_eq_false
    {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (k : K) (v : V) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.add.aborts K V (_root_.Object.new ctx world).1 k v
        (_root_.Object.new ctx world).2.2 = false := by
  unfold _root_.Dynamic_field.add.aborts _root_.Dynamic_field.uidKey
  exact any_and_eq_false_of_any_eq_false
    ((_root_.Object.new ctx world).2.2).df_entries
    (fun e : Nat × _root_.Bag.Entry Df => e.1 == _root_.Object.uidKey (_root_.Object.new ctx world).1)
    (fun e : Nat × _root_.Bag.Entry Df => _root_.Bag.Entry.keyMatches e.2 k)
    (_root_.Object.new_uid_no_df_entry ctx world)

-- ---------------------------------------------------------------------------
-- The allocation-frame bridge.
--
-- `dynamic_field_add_aborts_object_new_eq_false` above is stated at exactly
-- ONE world: `(Object.new ctx world).2.2`. A Move constructor that mints a uid
-- and then keeps allocating (`table::new`, `bag::new`, a nested constructor,
-- ...) adds the field at a LATER world, and no allocator touches `df_entries`,
-- so the freshness argument still goes through -- but the lemma above no
-- longer matches. Generalise it over any world that merely AGREES with the
-- minting world on `df_entries`.
--
-- `@[simp]` with the agreement as a side condition is deliberate: the
-- allocation-frame pack (`World.allocate_id_df_entries`,
-- `Object.new_world_df_entries`, and the four container
-- `new_world_df_entries`) discharges exactly that side condition by `simp`,
-- so an arbitrarily deep allocation chain between the mint and the `add`
-- resolves automatically instead of needing a hand-rolled peeling lemma per
-- chain shape. Nothing new is trusted: freshness still comes from
-- `Object.new_uid_validForNewId_eq_true` plus `World.id_list` counting
-- `df_entries` parents.
-- ---------------------------------------------------------------------------

@[simp] theorem dynamic_field_add_aborts_object_new_of_df_entries_eq
    {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (k : K) (v : V) (ctx : _root_.Tx_context.TxContext)
    (world w : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h : w.df_entries = world.df_entries) :
    _root_.Dynamic_field.add.aborts K V (_root_.Object.new ctx world).1 k v w = false := by
  unfold _root_.Dynamic_field.add.aborts _root_.Dynamic_field.uidKey
  rw [h]
  exact any_and_eq_false_of_any_eq_false
    world.df_entries
    (fun e : Nat × _root_.Bag.Entry Df => e.1 == _root_.Object.uidKey (_root_.Object.new ctx world).1)
    (fun e : Nat × _root_.Bag.Entry Df => _root_.Bag.Entry.keyMatches e.2 k)
    (_root_.Object.df_entries_any_eq_false_of_validForNewId
      (_root_.Object.uidKey (_root_.Object.new ctx world).1) world
      (_root_.Object.new_uid_validForNewId_eq_true ctx world))

/-- `dynamic_field::exists_` reads `df_entries` and nothing else, so two
worlds that agree on it answer every presence question identically.
Deliberately NOT `@[simp]`: both sides have the same head, and the target
world is not determined by the left-hand side, so it can only be cited.
It is the general form of the per-allocation-shape peeling lemmas clients
were writing by hand (`..._after_allocate`, `..._after_two_allocates`):
combine with the allocation-frame pack to discharge the agreement. -/
theorem dynamic_field_has_fst_eq_of_df_entries_eq
    {Ev Ob Be Df : Type} [Universe Df] (K : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (w1 w2 : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h : w1.df_entries = w2.df_entries) :
    (_root_.Dynamic_field.has K uid k w1).1 = (_root_.Dynamic_field.has K uid k w2).1 := by
  simp [_root_.Dynamic_field.has, h]

/-- `dynamic_field::borrow` resolves its value by searching `df_entries` and
returns the world unchanged, so its VALUE component is likewise a function of
`df_entries` alone. Same citation-only discipline as
`dynamic_field_has_fst_eq_of_df_entries_eq`. Needed wherever a client
predicate READS a dynamic field (rather than only testing presence) across an
allocation hop. -/
theorem dynamic_field_borrow_fst_eq_of_df_entries_eq
    {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (k : K)
    (w1 w2 : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h : w1.df_entries = w2.df_entries) :
    (_root_.Dynamic_field.borrow K V uid k w1).1 =
      (_root_.Dynamic_field.borrow K V uid k w2).1 := by
  simp [_root_.Dynamic_field.borrow, h]

/-- `dynamic_field::add`'s abort face IS the `df_entries` presence check, so
it too depends on nothing else. Same citation-only discipline as
`dynamic_field_has_fst_eq_of_df_entries_eq`; use it for the non-fresh uid
case, where the freshness bridge above does not apply. -/
theorem dynamic_field_add_aborts_eq_of_df_entries_eq
    {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (v : V)
    (w1 w2 : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h : w1.df_entries = w2.df_entries) :
    _root_.Dynamic_field.add.aborts K V uid k v w1 =
      _root_.Dynamic_field.add.aborts K V uid k v w2 := by
  simp [_root_.Dynamic_field.add.aborts, h]

-- ---------------------------------------------------------------------------
-- The `allocate_id` trio: the simp-usable specialisation of the three
-- congruences above.
--
-- The congruences are deliberately citation-only -- both sides share a head
-- and the target world is not determined by the LHS -- so they cannot peel an
-- allocation on their own. `World.allocate_id` only conses onto
-- `allocated_ids`, so at THAT world the target IS determined, and the same
-- three facts become ordinary frame rewrites toward the smaller term: they
-- peel an allocation off wherever it sits directly under a `has` /
-- `add.aborts` / `borrow`, at any depth, with no allocation COUNT in the
-- statement.
--
-- This is what retires the hand-rolled `*_after_allocate` /
-- `*_after_two_allocates` ladders: those rungs were indexed by a count that
-- world threading changes, and a count-free frame subsumes every one of them.
-- The `store_bag_*` side of the df API already shipped its two rungs
-- (`store_bag_has_allocate_id`, `store_bag_borrow_allocate_id`); these are the
-- missing plain-df siblings.
-- ---------------------------------------------------------------------------

@[simp] theorem dynamic_field_has_fst_allocate_id
    {Ev Ob Be Df : Type} [Universe Df] (K : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) (id : Nat) :
    (_root_.Dynamic_field.has K uid k
        (_root_.Prover.World.World.allocate_id world id)).1 =
      (_root_.Dynamic_field.has K uid k world).1 := rfl

@[simp] theorem dynamic_field_add_aborts_allocate_id
    {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (v : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) (id : Nat) :
    _root_.Dynamic_field.add.aborts K V uid k v
        (_root_.Prover.World.World.allocate_id world id) =
      _root_.Dynamic_field.add.aborts K V uid k v world := rfl

@[simp] theorem dynamic_field_borrow_fst_allocate_id
    {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (k : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) (id : Nat) :
    (_root_.Dynamic_field.borrow K V uid k
        (_root_.Prover.World.World.allocate_id world id)).1 =
      (_root_.Dynamic_field.borrow K V uid k world).1 := rfl

-- ---------------------------------------------------------------------------
-- Constructor rungs: the same trio (`has` / `add.aborts` / `borrow`), plus
-- the two `store_bag_*` observers, stated directly at each container
-- constructor's world. The cetus readiness arc hand-rolled the `table::new`
-- instances of exactly these (`dynamic_field_borrow_fst_table_new`, ...);
-- shipping all four constructors framework-side retires that class of
-- client-local rung for good. All rfl-class frame rewrites toward the base
-- world, so `@[simp]` per the pack discipline.
-- ---------------------------------------------------------------------------

@[simp] theorem dynamic_field_has_fst_table_new
    {Ev Ob Be Df TK TV : Type} [Universe Df] (K : Type)
    [HasCode Df K] [DecidableEq K] [BEq TK] [Inhabited TV]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K uid k
        (_root_.Table.new TK TV ctx world).2.2).1 =
      (_root_.Dynamic_field.has K uid k world).1 := rfl

@[simp] theorem dynamic_field_add_aborts_table_new
    {Ev Ob Be Df TK TV : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [BEq TK] [Inhabited TV]
    (uid : _root_.Object.UID) (k : K) (v : V) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.add.aborts K V uid k v
        (_root_.Table.new TK TV ctx world).2.2 =
      _root_.Dynamic_field.add.aborts K V uid k v world := rfl

@[simp] theorem dynamic_field_borrow_fst_table_new
    {Ev Ob Be Df TK TV : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    [BEq TK] [Inhabited TV]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.borrow K V uid k
        (_root_.Table.new TK TV ctx world).2.2).1 =
      (_root_.Dynamic_field.borrow K V uid k world).1 := rfl

@[simp] theorem dynamic_field_has_fst_object_table_new
    {Ev Ob Be Df TK TV : Type} [Universe Df] (K : Type)
    [HasCode Df K] [DecidableEq K] [BEq TK] [Inhabited TV]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K uid k
        (_root_.Object_table.new TK TV ctx world).2.2).1 =
      (_root_.Dynamic_field.has K uid k world).1 := rfl

@[simp] theorem dynamic_field_add_aborts_object_table_new
    {Ev Ob Be Df TK TV : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [BEq TK] [Inhabited TV]
    (uid : _root_.Object.UID) (k : K) (v : V) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.add.aborts K V uid k v
        (_root_.Object_table.new TK TV ctx world).2.2 =
      _root_.Dynamic_field.add.aborts K V uid k v world := rfl

@[simp] theorem dynamic_field_borrow_fst_object_table_new
    {Ev Ob Be Df TK TV : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    [BEq TK] [Inhabited TV]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.borrow K V uid k
        (_root_.Object_table.new TK TV ctx world).2.2).1 =
      (_root_.Dynamic_field.borrow K V uid k world).1 := rfl

@[simp] theorem dynamic_field_has_fst_bag_new
    {Ev Ob Be Df UB : Type} [Universe Df] [Universe UB] (K : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K uid k
        (_root_.Bag.new (U := UB) ctx world).2.2).1 =
      (_root_.Dynamic_field.has K uid k world).1 := rfl

@[simp] theorem dynamic_field_add_aborts_bag_new
    {Ev Ob Be Df UB : Type} [Universe Df] [Universe UB] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (v : V) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.add.aborts K V uid k v
        (_root_.Bag.new (U := UB) ctx world).2.2 =
      _root_.Dynamic_field.add.aborts K V uid k v world := rfl

@[simp] theorem dynamic_field_borrow_fst_bag_new
    {Ev Ob Be Df UB : Type} [Universe Df] [Universe UB] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.borrow K V uid k
        (_root_.Bag.new (U := UB) ctx world).2.2).1 =
      (_root_.Dynamic_field.borrow K V uid k world).1 := rfl

@[simp] theorem dynamic_field_has_fst_object_bag_new
    {Ev Ob Be Df UB : Type} [Universe Df] [Universe UB] (K : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K uid k
        (_root_.Object_bag.new (U := UB) ctx world).2.2).1 =
      (_root_.Dynamic_field.has K uid k world).1 := rfl

@[simp] theorem dynamic_field_add_aborts_object_bag_new
    {Ev Ob Be Df UB : Type} [Universe Df] [Universe UB] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (v : V) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.add.aborts K V uid k v
        (_root_.Object_bag.new (U := UB) ctx world).2.2 =
      _root_.Dynamic_field.add.aborts K V uid k v world := rfl

@[simp] theorem dynamic_field_borrow_fst_object_bag_new
    {Ev Ob Be Df UB : Type} [Universe Df] [Universe UB] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.borrow K V uid k
        (_root_.Object_bag.new (U := UB) ctx world).2.2).1 =
      (_root_.Dynamic_field.borrow K V uid k world).1 := rfl

-- The `store_bag_*` observers at each container constructor's world.

@[simp] theorem dynamic_field_store_bag_has_table_new
    {Ev Ob Df Bg TK TV : Type} [Universe Df] [Universe Bg] (K : Type)
    [HasCode Df K] [DecidableEq K] [BEq TK] [Inhabited TV]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_has K uid k
        (_root_.Table.new TK TV ctx world).2.2).1 =
      (_root_.Dynamic_field.store_bag_has K uid k world).1 := rfl

@[simp] theorem dynamic_field_store_bag_borrow_table_new
    {Ev Ob Df Bg TK TV : Type} [Universe Df] [Universe Bg] (K V : Type)
    [HasCode Df K] [DecidableEq K] [BEq TK] [Inhabited TV]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_borrow K V uid k
        (_root_.Table.new TK TV ctx world).2.2).1 =
      (_root_.Dynamic_field.store_bag_borrow K V uid k world).1 := by
  simp [_root_.Table.new]

@[simp] theorem dynamic_field_store_bag_has_object_table_new
    {Ev Ob Df Bg TK TV : Type} [Universe Df] [Universe Bg] (K : Type)
    [HasCode Df K] [DecidableEq K] [BEq TK] [Inhabited TV]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_has K uid k
        (_root_.Object_table.new TK TV ctx world).2.2).1 =
      (_root_.Dynamic_field.store_bag_has K uid k world).1 := rfl

@[simp] theorem dynamic_field_store_bag_borrow_object_table_new
    {Ev Ob Df Bg TK TV : Type} [Universe Df] [Universe Bg] (K V : Type)
    [HasCode Df K] [DecidableEq K] [BEq TK] [Inhabited TV]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_borrow K V uid k
        (_root_.Object_table.new TK TV ctx world).2.2).1 =
      (_root_.Dynamic_field.store_bag_borrow K V uid k world).1 := by
  simp [_root_.Object_table.new]

@[simp] theorem dynamic_field_store_bag_has_bag_new
    {Ev Ob Df Bg UB : Type} [Universe Df] [Universe Bg] [Universe UB] (K : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_has K uid k
        (_root_.Bag.new (U := UB) ctx world).2.2).1 =
      (_root_.Dynamic_field.store_bag_has K uid k world).1 := rfl

@[simp] theorem dynamic_field_store_bag_borrow_bag_new
    {Ev Ob Df Bg UB : Type} [Universe Df] [Universe Bg] [Universe UB] (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_borrow K V uid k
        (_root_.Bag.new (U := UB) ctx world).2.2).1 =
      (_root_.Dynamic_field.store_bag_borrow K V uid k world).1 := by
  simp [_root_.Bag.new]

@[simp] theorem dynamic_field_store_bag_has_object_bag_new
    {Ev Ob Df Bg UB : Type} [Universe Df] [Universe Bg] [Universe UB] (K : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_has K uid k
        (_root_.Object_bag.new (U := UB) ctx world).2.2).1 =
      (_root_.Dynamic_field.store_bag_has K uid k world).1 := rfl

@[simp] theorem dynamic_field_store_bag_borrow_object_bag_new
    {Ev Ob Df Bg UB : Type} [Universe Df] [Universe Bg] [Universe UB] (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_borrow K V uid k
        (_root_.Object_bag.new (U := UB) ctx world).2.2).1 =
      (_root_.Dynamic_field.store_bag_borrow K V uid k world).1 := by
  simp [_root_.Object_bag.new]

-- ---------------------------------------------------------------------------
-- THE `object::new` RUNG -- the last hop of every allocation chain.
--
-- The constructor rungs above are one hop short on their own, and the reason
-- is a lemma in this same pack. `TableNatives.new_world` (and its three
-- siblings) is an rfl `@[simp]` frame that rewrites a container
-- constructor's world to `object::new`'s:
--
--     (Table.new K V ctx world).2.2 = (Object.new ctx world).2.2
--
-- simp normalises the world argument BEFORE it tries a rung keyed on
-- `(Table.new ...).2.2`, so on any chain deeper than one frame -- and on
-- every chain observed through a `Dynamic_field.set` -- the peel arrives at
-- `(Object.new ctx world).2.2` and stops: the framework shipped the
-- `allocate_id` trio and one trio per CONSTRUCTOR, and nothing at
-- `object::new` itself. `Object.new_world_eq_allocate_id` cannot fill the
-- gap; it is deliberately citation-only because its RHS names the minted uid
-- and is not a smaller term. (The ghost-threaded form is already covered:
-- `Object.new__ghost_world_eq_allocate_id` IS `@[simp]`, its RHS mentioning
-- only the ghost variable.)
--
-- `object::new`'s one world action is a single `World.allocate_id`, which
-- `has` / `add.aborts` / `borrow` / the two `store_bag_*` observers all see
-- straight through -- so the same trio holds here by `rfl`, and being
-- strictly toward the smaller world it is an `@[simp]` frame by the pack
-- discipline. These eight rungs subsume the six that cetus's
-- `Factory_Proofs` carried privately (`cetus_dynamic_field_*_object_new`,
-- commit `d4d3a4c`), including the under-`Dynamic_field.set` forms that
-- ablation proved load-bearing there: a `set` ABOVE the allocation chain
-- (allocate, then add a field) leaves the constructor frames buried under it,
-- where the bare trio cannot reach them.
-- ---------------------------------------------------------------------------

@[simp] theorem dynamic_field_has_fst_object_new
    {Ev Ob Be Df : Type} [Universe Df] (K : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K uid k
        (_root_.Object.new ctx world).2.2).1 =
      (_root_.Dynamic_field.has K uid k world).1 := rfl

@[simp] theorem dynamic_field_add_aborts_object_new
    {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (v : V) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.add.aborts K V uid k v
        (_root_.Object.new ctx world).2.2 =
      _root_.Dynamic_field.add.aborts K V uid k v world := rfl

@[simp] theorem dynamic_field_borrow_fst_object_new
    {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.borrow K V uid k
        (_root_.Object.new ctx world).2.2).1 =
      (_root_.Dynamic_field.borrow K V uid k world).1 := rfl

@[simp] theorem dynamic_field_has_fst_set_object_new
    {Ev Ob Be Df : Type} [Universe Df] (K V : Type)
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (uid uid2 : _root_.Object.UID) (k k2 : K) (v : V)
    (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.has K uid k
        (_root_.Dynamic_field.set K V uid2 k2 v
          (_root_.Object.new ctx world).2.2)).1 =
      (_root_.Dynamic_field.has K uid k
        (_root_.Dynamic_field.set K V uid2 k2 v world)).1 := rfl

@[simp] theorem dynamic_field_add_aborts_set_object_new
    {Ev Ob Be Df : Type} [Universe Df] (K V V2 : Type)
    [HasCode Df K] [HasCode Df V] [HasCode Df V2] [DecidableEq K]
    (uid uid2 : _root_.Object.UID) (k k2 : K) (v : V) (v2 : V2)
    (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.add.aborts K V2 uid k v2
        (_root_.Dynamic_field.set K V uid2 k2 v
          (_root_.Object.new ctx world).2.2) =
      _root_.Dynamic_field.add.aborts K V2 uid k v2
        (_root_.Dynamic_field.set K V uid2 k2 v world) := rfl

@[simp] theorem dynamic_field_borrow_fst_set_object_new
    {Ev Ob Be Df : Type} [Universe Df] (K V V2 : Type)
    [HasCode Df K] [HasCode Df V] [HasCode Df V2] [DecidableEq K] [Inhabited V2]
    (uid uid2 : _root_.Object.UID) (k k2 : K) (v : V)
    (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.borrow K V2 uid k
        (_root_.Dynamic_field.set K V uid2 k2 v
          (_root_.Object.new ctx world).2.2)).1 =
      (_root_.Dynamic_field.borrow K V2 uid k
        (_root_.Dynamic_field.set K V uid2 k2 v world)).1 := rfl

@[simp] theorem dynamic_field_store_bag_has_object_new
    {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_has K uid k
        (_root_.Object.new ctx world).2.2).1 =
      (_root_.Dynamic_field.store_bag_has K uid k world).1 := rfl

@[simp] theorem dynamic_field_store_bag_borrow_object_new
    {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    (_root_.Dynamic_field.store_bag_borrow K V uid k
        (_root_.Object.new ctx world).2.2).1 =
      (_root_.Dynamic_field.store_bag_borrow K V uid k world).1 := by
  simp [_root_.Object.new]

-- ---------------------------------------------------------------------------
-- `df_bag_entries` congruences: the bag-store mirrors of the three
-- citation-only `df_entries` congruences below. Same discipline (both sides
-- share a head; the target world is not determined by the LHS), so
-- citation-only.
-- ---------------------------------------------------------------------------

theorem dynamic_field_store_bag_has_fst_eq_of_df_bag_entries_eq
    {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (w1 w2 : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg))
    (h : w1.df_bag_entries = w2.df_bag_entries) :
    (_root_.Dynamic_field.store_bag_has K uid k w1).1 =
      (_root_.Dynamic_field.store_bag_has K uid k w2).1 := by
  simp [_root_.Dynamic_field.store_bag_has, h]

theorem dynamic_field_store_bag_borrow_fst_eq_of_df_bag_entries_eq
    {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (uid : _root_.Object.UID) (k : K)
    (w1 w2 : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg))
    (h : w1.df_bag_entries = w2.df_bag_entries) :
    (_root_.Dynamic_field.store_bag_borrow K V uid k w1).1 =
      (_root_.Dynamic_field.store_bag_borrow K V uid k w2).1 := by
  unfold _root_.Dynamic_field.store_bag_borrow
  rw [h]
  generalize List.findSome? _ w2.df_bag_entries = found
  cases found with
  | none => rfl
  | some p =>
      cases p
      rfl

-- UID-freshness corollary for the bag-valued `dynamic_field::add<K, Bag>`
-- create face (create_multi_collateral_vault adds the supported-assets bag on a
-- FRESH vault uid). The strengthened `store_bag_add.aborts` is the disjunction
-- `store_bag_has || has`; a fresh uid keys NEITHER store, so both faces are
-- false. Bag side: `store_bag_has_object_new_self`. Plain df_entries side:
-- `Object.new_uid_no_df_entry` + the conjunctive-`any` monotonicity above.
@[simp] theorem dynamic_field_store_bag_add_aborts_object_new_eq_false
    {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (k : K) (v : _root_.Bag.Bag Bg) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg)) :
    _root_.Dynamic_field.store_bag_add.aborts K V (_root_.Object.new ctx world).1 k v
        (_root_.Object.new ctx world).2.2 = false := by
  have hbag :
      (_root_.Dynamic_field.store_bag_has K (_root_.Object.new ctx world).1 k
        (_root_.Object.new ctx world).2.2).1 = false :=
    _root_.Dynamic_field.store_bag_has_object_new_self K k ctx world
  have hdf :
      (_root_.Dynamic_field.has K (_root_.Object.new ctx world).1 k
        (_root_.Object.new ctx world).2.2).1 = false := by
    show ((_root_.Object.new ctx world).2.2).df_entries.any
        (fun e => e.1 == _root_.Dynamic_field.uidKey (_root_.Object.new ctx world).1 &&
          _root_.Bag.Entry.keyMatches e.2 k) = false
    unfold _root_.Dynamic_field.uidKey
    exact any_and_eq_false_of_any_eq_false
      ((_root_.Object.new ctx world).2.2).df_entries
      (fun e : Nat × _root_.Bag.Entry Df => e.1 == _root_.Object.uidKey (_root_.Object.new ctx world).1)
      (fun e : Nat × _root_.Bag.Entry Df => _root_.Bag.Entry.keyMatches e.2 k)
      (_root_.Object.new_uid_no_df_entry ctx world)
  unfold _root_.Dynamic_field.store_bag_add.aborts
  rw [hbag, hdf]
  rfl

/-- Allocation-frame bridge for the bag-valued create face, mirroring
`dynamic_field_add_aborts_object_new_of_df_entries_eq`: the add may happen at
ANY world that agrees with the minting world on BOTH df stores (the bag-add
abort face reads both). `@[simp]` with the agreements as side conditions --
the `df_entries` pack plus the new `df_bag_entries` twins discharge exactly
those, so a mint-then-allocate-then-bag-add chain resolves automatically. -/
@[simp] theorem dynamic_field_store_bag_add_aborts_object_new_of_entries_eq
    {Ev Ob Df Bg : Type} [Universe Df] [Universe Bg] (K V : Type)
    [HasCode Df K] [DecidableEq K]
    (k : K) (v : _root_.Bag.Bag Bg) (ctx : _root_.Tx_context.TxContext)
    (world w : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) (_root_.Bag.Entry Bg))
    (h_df : w.df_entries = world.df_entries)
    (h_bag : w.df_bag_entries = world.df_bag_entries) :
    _root_.Dynamic_field.store_bag_add.aborts K V (_root_.Object.new ctx world).1 k v
        w = false := by
  have h_valid := _root_.Object.new_uid_validForNewId_eq_true ctx world
  have h_bag_face :
      (_root_.Dynamic_field.store_bag_has K (_root_.Object.new ctx world).1 k w).1 =
        false := by
    rw [dynamic_field_store_bag_has_fst_eq_of_df_bag_entries_eq K
      (_root_.Object.new ctx world).1 k w world h_bag]
    exact _root_.Dynamic_field.store_bag_has_eq_false_of_validForNewId K
      (_root_.Object.new ctx world).1 k world h_valid
  have h_df_face :
      (_root_.Dynamic_field.has K (_root_.Object.new ctx world).1 k w).1 =
        false := by
    rw [dynamic_field_has_fst_eq_of_df_entries_eq K
      (_root_.Object.new ctx world).1 k w world h_df]
    exact dynamic_field_has_eq_false_of_validForNewId K
      (_root_.Object.new ctx world).1 k world h_valid
  unfold _root_.Dynamic_field.store_bag_add.aborts
  rw [h_bag_face, h_df_face]
  rfl

/-! ## Shared df frame lemmas

Key-disjointness and world-bookkeeping frames for the plain (non-bag) df API.
The `*_key_ne` pair is the df analogue of `TableEffects.{contains,borrow}_set_ne`
and was the single largest duplicated proof in the client corpora (81 / 60
lines per copy). Namespaced per the standing rule in
`plans/lean-pipeline/shared-proof-infra.md`. -/

namespace DynamicFieldEffects

/-- A write at a DIFFERENT key leaves the presence check unchanged (any uid). -/
theorem has_set_key_ne {Ev Ob Be Df K V : Type} [Universe Df]
    [hkc : HasCode Df K] [hvc : HasCode Df V] [DecidableEq K]
    (readUid writeUid : _root_.Object.UID) (readKey writeKey : K) (value : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h_ne : readKey ≠ writeKey) :
    (_root_.Dynamic_field.has K readUid readKey
      (_root_.Dynamic_field.set K V writeUid writeKey value world)).1 =
      (_root_.Dynamic_field.has K readUid readKey world).1 := by
  unfold _root_.Dynamic_field.has _root_.Dynamic_field.set
  simp only [List.any_cons]
  have h_head :
      (_root_.Dynamic_field.uidKey writeUid ==
          _root_.Dynamic_field.uidKey readUid &&
        _root_.Bag.Entry.keyMatches
          { kc := hkc.code, k := hkc.proof.symm ▸ writeKey,
            vc := hvc.code, v := hvc.proof.symm ▸ value }
          readKey) = false := by
    apply Bool.eq_false_iff.mpr
    intro h_head_true
    rcases Bool.and_eq_true_iff.mp h_head_true with ⟨_, h_read⟩
    have h_write := BagFacts.keyMatches_pack (U := Df) writeKey value
    have h_read_false := BagFacts.keyMatches_eq_false_of_ne
      { kc := hkc.code, k := hkc.proof.symm ▸ writeKey,
        vc := hvc.code, v := hvc.proof.symm ▸ value }
      writeKey readKey (Ne.symm h_ne) h_write
    simp [h_read_false] at h_read
  rw [h_head, Bool.false_or]
  apply ListFacts.any_filter_not_of_disjoint
  intro entry h_remove
  rcases Bool.and_eq_true_iff.mp h_remove with ⟨_, h_write⟩
  have h_read_false := BagFacts.keyMatches_eq_false_of_ne
    entry.2 writeKey readKey (Ne.symm h_ne) h_write
  simp [h_read_false]

/-- A write at a DIFFERENT key leaves the read unchanged (any uid, and the
written value type need not match the read value type). -/
theorem borrow_set_key_ne {Ev Ob Be Df K ReadV WriteV : Type} [Universe Df]
    [hkc : HasCode Df K] [hrvc : HasCode Df ReadV] [hwvc : HasCode Df WriteV]
    [DecidableEq K] [Inhabited ReadV]
    (readUid writeUid : _root_.Object.UID) (readKey writeKey : K)
    (value : WriteV)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h_ne : readKey ≠ writeKey) :
    (_root_.Dynamic_field.borrow K ReadV readUid readKey
      (_root_.Dynamic_field.set K WriteV writeUid writeKey value world)).1 =
      (_root_.Dynamic_field.borrow K ReadV readUid readKey world).1 := by
  unfold _root_.Dynamic_field.borrow _root_.Dynamic_field.set
  simp only
  have h_write := BagFacts.keyMatches_pack (U := Df) writeKey value
  have h_read_false := BagFacts.keyMatches_eq_false_of_ne
    ({ kc := hkc.code, k := hkc.proof.symm ▸ writeKey,
       vc := hwvc.code, v := hwvc.proof.symm ▸ value } : _root_.Bag.Entry Df)
    writeKey readKey (Ne.symm h_ne) h_write
  have h_head :
      (if (_root_.Dynamic_field.uidKey writeUid ==
            _root_.Dynamic_field.uidKey readUid &&
          _root_.Bag.Entry.keyMatches
            ({ kc := hkc.code, k := hkc.proof.symm ▸ writeKey,
               vc := hwvc.code, v := hwvc.proof.symm ▸ value }
              : _root_.Bag.Entry Df) readKey) = true then
        if hv : hwvc.code = hrvc.code then
          some (hrvc.proof ▸ hv ▸ hwvc.proof.symm ▸ value)
        else none
      else none) = none := by
    simp [h_read_false]
  change
    (List.findSome?
      (fun e =>
        if (e.1 == _root_.Dynamic_field.uidKey readUid &&
            _root_.Bag.Entry.keyMatches e.2 readKey) = true then
          if hv : e.2.vc = hrvc.code then
            some (hrvc.proof ▸ hv ▸ e.2.v)
          else none
        else none)
      ((_root_.Dynamic_field.uidKey writeUid,
        ({ kc := hkc.code, k := hkc.proof.symm ▸ writeKey,
           vc := hwvc.code, v := hwvc.proof.symm ▸ value }
            : _root_.Bag.Entry Df)) ::
        world.df_entries.filter (fun e =>
          !(e.1 == _root_.Dynamic_field.uidKey writeUid &&
            _root_.Bag.Entry.keyMatches e.2 writeKey)))).getD default = _
  rw [List.findSome?_cons, h_head]
  apply congrArg (fun result : Option ReadV => result.getD default)
  apply ListFacts.findSome?_filter_not_of_removed_none
  intro entry h_remove
  rcases Bool.and_eq_true_iff.mp h_remove with ⟨_, h_write⟩
  have h_read_false := BagFacts.keyMatches_eq_false_of_ne
    entry.2 writeKey readKey (Ne.symm h_ne) h_write
  simp [h_read_false]

/-- df read side of `dynamic_field_has_object_new`: `object::new` only records
an allocation, so it leaves `df_entries` (and hence every read) alone. -/
theorem borrow_object_new {Ev Ob Be Df K V : Type} [Universe Df]
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (key : K) (ctx : _root_.Tx_context.TxContext)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.borrow K V uid key
      (_root_.Object.new ctx world).2.2).1 =
      (_root_.Dynamic_field.borrow K V uid key world).1 := by
  have h_df : ((_root_.Object.new ctx world).2.2).df_entries =
      world.df_entries := by
    unfold _root_.Object.new; rfl
  simp [_root_.Dynamic_field.borrow, h_df]

/-- df counterparts of `dynamic_field_store_bag_{has,borrow}_transfer_to`. -/
theorem has_transfer_to {Ev Ob Be Df K : Type} [Universe Df] [HasCode Df K]
    [DecidableEq K] (uid : _root_.Object.UID) (key : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (id : Nat) (recipient : Address) (obj : Ob) :
    (_root_.Dynamic_field.has K uid key
      (_root_.Prover.World.World.transfer_to world id recipient obj)).1 =
      (_root_.Dynamic_field.has K uid key world).1 := by
  simp [_root_.Dynamic_field.has, _root_.Prover.World.World.transfer_to]

theorem borrow_transfer_to {Ev Ob Be Df K V : Type} [Universe Df]
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (key : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (id : Nat) (recipient : Address) (obj : Ob) :
    (_root_.Dynamic_field.borrow K V uid key
      (_root_.Prover.World.World.transfer_to world id recipient obj)).1 =
      (_root_.Dynamic_field.borrow K V uid key world).1 := by
  simp [_root_.Dynamic_field.borrow, _root_.Prover.World.World.transfer_to]

/-- `add`-shaped restatements of `dynamic_field_borrow_set_same` /
`dynamic_field_has_set_same`; `add` and `set` share a world action but clients
write the call as `add`. -/
theorem borrow_add_same {Ev Ob Be Df K V : Type} [Universe Df]
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (key : K) (value : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    (_root_.Dynamic_field.borrow K V uid key
      (_root_.Dynamic_field.add K V uid key value world)).1 = value :=
  dynamic_field_borrow_set_same uid key value world

theorem borrow_aborts_add_same_eq_false {Ev Ob Be Df K V : Type} [Universe Df]
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (uid : _root_.Object.UID) (key : K) (value : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be) :
    _root_.Dynamic_field.borrow.aborts K V uid key
      (_root_.Dynamic_field.add K V uid key value world) = false := by
  rw [dynamic_field_borrow_aborts_eq_not_has,
    show (_root_.Dynamic_field.add K V uid key value world) =
      (_root_.Dynamic_field.set K V uid key value world) from rfl,
    dynamic_field_has_set_same]
  rfl

/-- `add`-shaped aliases of the `set` key-disjointness pair (`add` and `set`
share a world action; clients write the call as `add`). -/
theorem has_add_key_ne {Ev Ob Be Df K V : Type} [Universe Df]
    [HasCode Df K] [HasCode Df V] [DecidableEq K]
    (readUid writeUid : _root_.Object.UID) (readKey writeKey : K) (value : V)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h_ne : readKey ≠ writeKey) :
    (_root_.Dynamic_field.has K readUid readKey
      (_root_.Dynamic_field.add K V writeUid writeKey value world)).1 =
      (_root_.Dynamic_field.has K readUid readKey world).1 :=
  has_set_key_ne readUid writeUid readKey writeKey value world h_ne

theorem borrow_add_key_ne {Ev Ob Be Df K ReadV WriteV : Type} [Universe Df]
    [HasCode Df K] [HasCode Df ReadV] [HasCode Df WriteV]
    [DecidableEq K] [Inhabited ReadV]
    (readUid writeUid : _root_.Object.UID) (readKey writeKey : K)
    (value : WriteV)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h_ne : readKey ≠ writeKey) :
    (_root_.Dynamic_field.borrow K ReadV readUid readKey
      (_root_.Dynamic_field.add K WriteV writeUid writeKey value world)).1 =
      (_root_.Dynamic_field.borrow K ReadV readUid readKey world).1 :=
  borrow_set_key_ne readUid writeUid readKey writeKey value world h_ne

/-- A write at a DIFFERENT parent uid leaves the read unchanged (any keys;
the uid-side sibling of `borrow_set_key_ne`, completing the pair the
presence side already has in `dynamic_field_has_set_uid_ne`). -/
theorem borrow_set_uid_ne {Ev Ob Be Df K ReadV WriteV : Type} [Universe Df]
    [hkc : HasCode Df K] [hrvc : HasCode Df ReadV] [hwvc : HasCode Df WriteV]
    [DecidableEq K] [Inhabited ReadV]
    (readUid writeUid : _root_.Object.UID) (readKey writeKey : K)
    (value : WriteV)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h_ne :
      _root_.Dynamic_field.uidKey readUid ≠ _root_.Dynamic_field.uidKey writeUid) :
    (_root_.Dynamic_field.borrow K ReadV readUid readKey
      (_root_.Dynamic_field.set K WriteV writeUid writeKey value world)).1 =
      (_root_.Dynamic_field.borrow K ReadV readUid readKey world).1 := by
  unfold _root_.Dynamic_field.borrow _root_.Dynamic_field.set
  simp only
  have h_uid_false :
      (_root_.Dynamic_field.uidKey writeUid ==
        _root_.Dynamic_field.uidKey readUid) = false := by
    apply Bool.eq_false_iff.mpr
    intro h_true
    exact h_ne (beq_iff_eq.mp h_true).symm
  have h_head :
      (if (_root_.Dynamic_field.uidKey writeUid ==
            _root_.Dynamic_field.uidKey readUid &&
          _root_.Bag.Entry.keyMatches
            ({ kc := hkc.code, k := hkc.proof.symm ▸ writeKey,
               vc := hwvc.code, v := hwvc.proof.symm ▸ value }
              : _root_.Bag.Entry Df) readKey) = true then
        if hv : hwvc.code = hrvc.code then
          some (hrvc.proof ▸ hv ▸ hwvc.proof.symm ▸ value)
        else none
      else none) = none := by
    simp [h_uid_false]
  change
    (List.findSome?
      (fun e =>
        if (e.1 == _root_.Dynamic_field.uidKey readUid &&
            _root_.Bag.Entry.keyMatches e.2 readKey) = true then
          if hv : e.2.vc = hrvc.code then
            some (hrvc.proof ▸ hv ▸ e.2.v)
          else none
        else none)
      ((_root_.Dynamic_field.uidKey writeUid,
        ({ kc := hkc.code, k := hkc.proof.symm ▸ writeKey,
           vc := hwvc.code, v := hwvc.proof.symm ▸ value }
            : _root_.Bag.Entry Df)) ::
        world.df_entries.filter (fun e =>
          !(e.1 == _root_.Dynamic_field.uidKey writeUid &&
            _root_.Bag.Entry.keyMatches e.2 writeKey)))).getD default = _
  rw [List.findSome?_cons, h_head]
  apply congrArg (fun result : Option ReadV => result.getD default)
  apply ListFacts.findSome?_filter_not_of_removed_none
  intro entry h_remove
  rcases Bool.and_eq_true_iff.mp h_remove with ⟨h_uid, _⟩
  have h_entry_uid_false :
      (entry.1 == _root_.Dynamic_field.uidKey readUid) = false := by
    apply Bool.eq_false_iff.mpr
    intro h_true
    exact h_ne ((beq_iff_eq.mp h_true).symm.trans (beq_iff_eq.mp h_uid))
  simp [h_entry_uid_false]

theorem borrow_add_uid_ne {Ev Ob Be Df K ReadV WriteV : Type} [Universe Df]
    [HasCode Df K] [HasCode Df ReadV] [HasCode Df WriteV]
    [DecidableEq K] [Inhabited ReadV]
    (readUid writeUid : _root_.Object.UID) (readKey writeKey : K)
    (value : WriteV)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h_ne :
      _root_.Dynamic_field.uidKey readUid ≠ _root_.Dynamic_field.uidKey writeUid) :
    (_root_.Dynamic_field.borrow K ReadV readUid readKey
      (_root_.Dynamic_field.add K WriteV writeUid writeKey value world)).1 =
      (_root_.Dynamic_field.borrow K ReadV readUid readKey world).1 :=
  borrow_set_uid_ne readUid writeUid readKey writeKey value world h_ne

/-- `remove`-side key/uid disjointness: dropping the entry at one `(uid, key)`
leaves presence and reads at any OTHER key (or any other uid) unchanged.
Completes the writer column the `set`/`add` pair already covers. -/
theorem has_remove_key_ne {Ev Ob Be Df K V : Type} [Universe Df]
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (readUid removeUid : _root_.Object.UID) (readKey removeKey : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h_ne : readKey ≠ removeKey) :
    (_root_.Dynamic_field.has K readUid readKey
      (_root_.Dynamic_field.remove K V removeUid removeKey world).2).1 =
      (_root_.Dynamic_field.has K readUid readKey world).1 := by
  unfold _root_.Dynamic_field.has _root_.Dynamic_field.remove
  simp only
  apply ListFacts.any_filter_not_of_disjoint
  intro entry h_remove
  rcases Bool.and_eq_true_iff.mp h_remove with ⟨_, h_write⟩
  have h_read_false := BagFacts.keyMatches_eq_false_of_ne
    entry.2 removeKey readKey (Ne.symm h_ne) h_write
  simp [h_read_false]

theorem has_remove_uid_ne {Ev Ob Be Df K V : Type} [Universe Df]
    [HasCode Df K] [HasCode Df V] [DecidableEq K] [Inhabited V]
    (readUid removeUid : _root_.Object.UID) (readKey removeKey : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h_ne :
      _root_.Dynamic_field.uidKey readUid ≠ _root_.Dynamic_field.uidKey removeUid) :
    (_root_.Dynamic_field.has K readUid readKey
      (_root_.Dynamic_field.remove K V removeUid removeKey world).2).1 =
      (_root_.Dynamic_field.has K readUid readKey world).1 := by
  unfold _root_.Dynamic_field.has _root_.Dynamic_field.remove
  simp only
  apply ListFacts.any_filter_not_of_disjoint
  intro entry h_remove
  rcases Bool.and_eq_true_iff.mp h_remove with ⟨h_uid, _⟩
  have h_entry_uid_false :
      (entry.1 == _root_.Dynamic_field.uidKey readUid) = false := by
    apply Bool.eq_false_iff.mpr
    intro h_true
    exact h_ne ((beq_iff_eq.mp h_true).symm.trans (beq_iff_eq.mp h_uid))
  simp [h_entry_uid_false]

theorem borrow_remove_key_ne {Ev Ob Be Df K ReadV RemoveV : Type} [Universe Df]
    [HasCode Df K] [hrvc : HasCode Df ReadV] [HasCode Df RemoveV]
    [DecidableEq K] [Inhabited ReadV] [Inhabited RemoveV]
    (readUid removeUid : _root_.Object.UID) (readKey removeKey : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h_ne : readKey ≠ removeKey) :
    (_root_.Dynamic_field.borrow K ReadV readUid readKey
      (_root_.Dynamic_field.remove K RemoveV removeUid removeKey world).2).1 =
      (_root_.Dynamic_field.borrow K ReadV readUid readKey world).1 := by
  unfold _root_.Dynamic_field.borrow _root_.Dynamic_field.remove
  simp only
  apply congrArg (fun result : Option ReadV => result.getD default)
  apply ListFacts.findSome?_filter_not_of_removed_none
  intro entry h_remove
  rcases Bool.and_eq_true_iff.mp h_remove with ⟨_, h_write⟩
  have h_read_false := BagFacts.keyMatches_eq_false_of_ne
    entry.2 removeKey readKey (Ne.symm h_ne) h_write
  simp [h_read_false]

theorem borrow_remove_uid_ne {Ev Ob Be Df K ReadV RemoveV : Type} [Universe Df]
    [HasCode Df K] [hrvc : HasCode Df ReadV] [HasCode Df RemoveV]
    [DecidableEq K] [Inhabited ReadV] [Inhabited RemoveV]
    (readUid removeUid : _root_.Object.UID) (readKey removeKey : K)
    (world : _root_.Prover.World.World Ev Ob (_root_.Bag.Entry Df) Be)
    (h_ne :
      _root_.Dynamic_field.uidKey readUid ≠ _root_.Dynamic_field.uidKey removeUid) :
    (_root_.Dynamic_field.borrow K ReadV readUid readKey
      (_root_.Dynamic_field.remove K RemoveV removeUid removeKey world).2).1 =
      (_root_.Dynamic_field.borrow K ReadV readUid readKey world).1 := by
  unfold _root_.Dynamic_field.borrow _root_.Dynamic_field.remove
  simp only
  apply congrArg (fun result : Option ReadV => result.getD default)
  apply ListFacts.findSome?_filter_not_of_removed_none
  intro entry h_remove
  rcases Bool.and_eq_true_iff.mp h_remove with ⟨h_uid, _⟩
  have h_entry_uid_false :
      (entry.1 == _root_.Dynamic_field.uidKey readUid) = false := by
    apply Bool.eq_false_iff.mpr
    intro h_true
    exact h_ne ((beq_iff_eq.mp h_true).symm.trans (beq_iff_eq.mp h_uid))
  simp [h_entry_uid_false]

end DynamicFieldEffects
