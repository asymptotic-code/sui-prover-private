-- Native implementations for sui::object_bag.
--
-- Move source: `public struct ObjectBag has key, store { id: UID,
-- size: u64 }`. Same heterogeneous-storage model as `sui::bag` --
-- see `BagNatives.lean` for the full design rationale (typed
-- `storage` IN the struct, no axioms; `Entry`/`keyMatches` are
-- reused from there). ObjectBag is excluded from TyCode / BagU and
-- routed through the skeleton split identically to Bag on the
-- renderer side.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.Universe
import Sui.ObjectNatives
import Sui.Tx_contextNatives
import Sui.BagNatives

namespace Object_bag

/-- Same shape as `Bag.Bag`; entries reuse `Bag.Entry`. -/
structure ObjectBag (U : Type) [Universe U] where
  id      : Object.UID
  size    : BoundedNat (2^64)
  storage : List (Bag.Entry U)
deriving Inhabited, DecidableEq

/-- ObjectBag is a Sui `key`-ability object (Move: `struct ObjectBag
    has key, store { id: UID, size: u64 }`); see the matching
    instance on `Bag.Bag` for why the prelude provides it. -/
instance {U : Type} [Universe U] : Object.HasObjectId (ObjectBag U) where
  uid b := b.id

def new {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    ObjectBag U × Tx_context.TxContext × Prover.World.World Ev Ob Df Be :=
  let created := Object.new ctx world
  (⟨created.1, (0 : BoundedNat (2^64)), []⟩, created.2.1, created.2.2)

/-- Allocation-frame pack (6/6): `object_bag::new` delegates its UID
    allocation to `object::new`, so dynamic-field storage survives the
    hop. Same statement and same one-line proof as
    `Bag.new_world_df_entries`. -/
@[simp] theorem new_world_df_entries {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    ((new (U := U) ctx world).2.2).df_entries = world.df_entries := rfl

/-- Bag-store twin of `new_world_df_entries` (see
    `Bag.new_world_df_bag_entries`). -/
@[simp] theorem new_world_df_bag_entries {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    ((new (U := U) ctx world).2.2).df_bag_entries = world.df_bag_entries := rfl

/-- Pass 2: see `Table.new_world` / `Table.new_ctx`. -/
@[simp] theorem new_world {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (new (U := U) ctx world).2.2 = (Object.new ctx world).2.2 := rfl

@[simp] theorem new_ctx {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (new (U := U) ctx world).2.1 = (Object.new ctx world).2.1 := rfl

def new.aborts {U Ev Ob Df Be : Type} [Universe U]
    (_ctx : Tx_context.TxContext) (_world : Prover.World.World Ev Ob Df Be) : Bool := false

def add {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [DecidableEq K]
    (self : ObjectBag U) (k : K) (v : V) : ObjectBag U :=
  let entry : Bag.Entry U :=
    { kc := hkc.code, k  := hkc.proof.symm ▸ k
    , vc := hvc.code, v  := hvc.proof.symm ▸ v }
  let filtered := self.storage.filter (fun e => ! Bag.Entry.keyMatches e k)
  { self with size := self.size + 1, storage := entry :: filtered }

def add.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [DecidableEq K]
    (self : ObjectBag U) (k : K) (_v : V) : Bool :=
  -- `object_bag::add` aborts when the key is present or the size increment overflows.
  self.storage.any (fun e => Bag.Entry.keyMatches e k) ||
    BoundedNat.add_aborts
      ⟨self.storage.length % (2^64), Nat.mod_lt _ (by decide)⟩
      (1 : BoundedNat (2^64))

/-- `Object_bag.set` — writeback companion of `borrow_mut`, same
contract as `Bag.set`: overwrite at `k` preserving size when the key
exists, behave like `add` (size + 1) when absent. The renderer emits
this at ObjectBag writeback sites. -/
def set {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [DecidableEq K]
    (self : ObjectBag U) (k : K) (v : V) : ObjectBag U :=
  let entry : Bag.Entry U :=
    { kc := hkc.code, k  := hkc.proof.symm ▸ k
    , vc := hvc.code, v  := hvc.proof.symm ▸ v }
  let had_key := self.storage.any (fun e => Bag.Entry.keyMatches e k)
  let filtered := self.storage.filter (fun e => ! Bag.Entry.keyMatches e k)
  let new_size := if had_key then self.size else self.size + 1
  { self with size := new_size, storage := entry :: filtered }

def remove {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [DecidableEq K] [Inhabited V]
    (self : ObjectBag U) (k : K) : V × ObjectBag U :=
  let found? : Option V :=
    self.storage.findSome? (fun e =>
      if Bag.Entry.keyMatches e k then
        if hv : e.vc = hvc.code then
          some (hvc.proof ▸ hv ▸ e.v)
        else none
      else none)
  let v := found?.getD default
  let filtered := self.storage.filter (fun e => ! Bag.Entry.keyMatches e k)
  (v, { self with size := self.size - 1, storage := filtered })

def remove.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [hvc : HasCode U V] [DecidableEq K] [Inhabited V]
    (self : ObjectBag U) (k : K) : Bool :=
  -- `object_bag::remove` aborts when the key is absent or has a different value type.
  ! self.storage.any (fun e => Bag.Entry.keyMatches e k && (e.vc = hvc.code))

def borrow {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [DecidableEq K] [Inhabited V]
    (self : ObjectBag U) (k : K) : V :=
  let found? : Option V :=
    self.storage.findSome? (fun e =>
      if Bag.Entry.keyMatches e k then
        if hv : e.vc = hvc.code then
          some (hvc.proof ▸ hv ▸ e.v)
        else none
      else none)
  found?.getD default

def borrow.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [hvc : HasCode U V] [DecidableEq K] [Inhabited V]
    (self : ObjectBag U) (k : K) : Bool :=
  -- `object_bag::borrow` aborts when the key is absent or has a different value type.
  ! self.storage.any (fun e => Bag.Entry.keyMatches e k && (e.vc = hvc.code))

def contains {U : Type} [Universe U] (K : Type)
    [HasCode U K] [DecidableEq K]
    (self : ObjectBag U) (k : K) : Bool :=
  self.storage.any (fun e => Bag.Entry.keyMatches e k)

def contains.aborts {U : Type} [Universe U] (K : Type)
    [HasCode U K] [DecidableEq K]
    (_self : ObjectBag U) (_k : K) : Bool := false

def contains_with_type {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [DecidableEq K]
    (self : ObjectBag U) (k : K) : Bool :=
  self.storage.any (fun e =>
    Bag.Entry.keyMatches e k && (e.vc = hvc.code))

def contains_with_type.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [DecidableEq K]
    (_self : ObjectBag U) (_k : K) : Bool := false

-- length / is_empty DERIVED from storage, matching Bag.
def length {U : Type} [Universe U] (self : ObjectBag U) : BoundedNat (2^64) :=
  ⟨self.storage.length % (2^64), Nat.mod_lt _ (by decide)⟩
def length.aborts {U : Type} [Universe U] (_self : ObjectBag U) : Bool := false

def is_empty {U : Type} [Universe U] (self : ObjectBag U) : Bool :=
  self.storage.isEmpty
def is_empty.aborts {U : Type} [Universe U] (_self : ObjectBag U) : Bool := false

def destroy_empty {U : Type} [Universe U] (_self : ObjectBag U) : Unit := ()
-- Aborts (non-empty) read from `storage`, matching `is_empty`/`length`
-- (single source of truth; `size` is maintained but unread and not tied
-- to `storage.length` by any invariant). See BagNatives.destroy_empty.aborts.
def destroy_empty.aborts {U : Type} [Universe U] (self : ObjectBag U) : Bool :=
  !self.storage.isEmpty

end Object_bag

-- ---------------------------------------------------------------------------
-- Observer x writer matrix for ObjectBag, mirroring `BagNatives.lean`
-- (entries reuse `Bag.Entry`, so the `BagFacts` leaves apply directly).
-- Attribute discipline as in the Bag file: `@[simp]` on rfl-class /
-- unconditional one-directional frames; conditional `_ne` transports are
-- citation-only.
-- ---------------------------------------------------------------------------

namespace Object_bag

-- Abort-face bridges + total faces.

@[simp] theorem object_bag_new_aborts_eq_false
    {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    new.aborts (U := U) ctx world = false := rfl

@[simp] theorem object_bag_borrow_aborts_eq_not_contains_with_type
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : ObjectBag U) (k : K) :
    borrow.aborts K V bag k = !contains_with_type K V bag k := rfl

@[simp] theorem object_bag_remove_aborts_eq_not_contains_with_type
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : ObjectBag U) (k : K) :
    remove.aborts K V bag k = !contains_with_type K V bag k := rfl

@[simp] theorem object_bag_add_aborts_eq_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : ObjectBag U) (k : K) (v : V) :
    add.aborts K V bag k v =
      (contains K bag k ||
        BoundedNat.add_aborts (length bag) (1 : BoundedNat (2^64))) := rfl

@[simp] theorem object_bag_contains_aborts_eq_false
    {U K : Type} [Universe U] [HasCode U K] [DecidableEq K]
    (bag : ObjectBag U) (k : K) :
    contains.aborts K bag k = false := rfl

@[simp] theorem object_bag_contains_with_type_aborts_eq_false
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : ObjectBag U) (k : K) :
    contains_with_type.aborts K V bag k = false := rfl

@[simp] theorem object_bag_length_aborts_eq_false {U : Type} [Universe U]
    (bag : ObjectBag U) :
    length.aborts bag = false := rfl

@[simp] theorem object_bag_is_empty_aborts_eq_false {U : Type} [Universe U]
    (bag : ObjectBag U) :
    is_empty.aborts bag = false := rfl

@[simp] theorem object_bag_destroy_empty_aborts_eq_not_is_empty
    {U : Type} [Universe U] (bag : ObjectBag U) :
    destroy_empty.aborts bag = !is_empty bag := rfl

-- Constructor faces.

@[simp] theorem object_bag_contains_new
    {U K Ev Ob Df Be : Type} [Universe U] [HasCode U K] [DecidableEq K]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (k : K) :
    contains K (new (U := U) ctx world).1 k = false := by
  simp [new, contains]

@[simp] theorem object_bag_contains_with_type_new
    {U K V Ev Ob Df Be : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] (ctx : Tx_context.TxContext)
    (world : Prover.World.World Ev Ob Df Be) (k : K) :
    contains_with_type K V (new (U := U) ctx world).1 k = false := by
  simp [new, contains_with_type]

@[simp] theorem object_bag_borrow_new
    {U K V Ev Ob Df Be : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (k : K) :
    borrow K V (new (U := U) ctx world).1 k = default := rfl

@[simp] theorem object_bag_length_new_eq_zero
    {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    length (new (U := U) ctx world).1 = (0 : BoundedNat (2^64)) := rfl

@[simp] theorem object_bag_is_empty_new
    {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    is_empty (new (U := U) ctx world).1 = true := rfl

@[simp] theorem object_bag_destroy_empty_aborts_new
    {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    destroy_empty.aborts (new (U := U) ctx world).1 = false := rfl

@[simp] theorem object_bag_add_aborts_new
    {U K V Ev Ob Df Be : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be)
    (k : K) (v : V) :
    add.aborts K V (new (U := U) ctx world).1 k v = false := rfl

@[simp] theorem object_bag_borrow_aborts_new
    {U K V Ev Ob Df Be : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (k : K) :
    borrow.aborts K V (new (U := U) ctx world).1 k = true := rfl

@[simp] theorem object_bag_remove_aborts_new
    {U K V Ev Ob Df Be : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (k : K) :
    remove.aborts K V (new (U := U) ctx world).1 k = true := rfl

-- Same-key transports.

@[simp] theorem object_bag_contains_add_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : ObjectBag U) (k : K) (v : V) :
    contains K (add K V bag k v) k = true := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [contains, add, Bag.Entry.keyMatches]

@[simp] theorem object_bag_contains_with_type_add_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : ObjectBag U) (k : K) (v : V) :
    contains_with_type K V (add K V bag k v) k = true := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [contains_with_type, add, Bag.Entry.keyMatches]

@[simp] theorem object_bag_borrow_add_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V] (bag : ObjectBag U) (k : K) (v : V) :
    borrow K V (add K V bag k v) k = v := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [borrow, add, Bag.Entry.keyMatches]

@[simp] theorem object_bag_contains_set_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : ObjectBag U) (k : K) (v : V) :
    contains K (set K V bag k v) k = true := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [contains, set, Bag.Entry.keyMatches]

@[simp] theorem object_bag_contains_with_type_set_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : ObjectBag U) (k : K) (v : V) :
    contains_with_type K V (set K V bag k v) k = true := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [contains_with_type, set, Bag.Entry.keyMatches]

@[simp] theorem object_bag_borrow_set_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V] (bag : ObjectBag U) (k : K) (v : V) :
    borrow K V (set K V bag k v) k = v := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [borrow, set, Bag.Entry.keyMatches]

@[simp] theorem object_bag_contains_with_type_remove_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : ObjectBag U) (k : K) :
    contains_with_type K V (remove K V bag k).2 k = false := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [contains_with_type, remove, Bag.Entry.keyMatches]
      intro _ _ h_no_key h_key h_lift_eq _h_type
      exact (h_no_key h_key) h_lift_eq

@[simp] theorem object_bag_contains_remove_same
    {U K V : Type} [Universe U] [HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : ObjectBag U) (k : K) :
    contains K (remove K V bag k).2 k = false := by
  unfold contains remove
  apply Bool.eq_false_iff.mpr
  intro h_any
  rcases List.any_eq_true.mp h_any with ⟨entry, h_mem, h_match⟩
  have h_kept := (List.mem_filter.mp h_mem).2
  rw [h_match] at h_kept
  simp at h_kept

/-- The absent-key read (see `bag_borrow_eq_default_of_not_contains`). -/
theorem object_bag_borrow_eq_default_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : ObjectBag U) (k : K)
    (h_not_contains : contains K bag k = false) :
    borrow K V bag k = default := by
  unfold borrow
  unfold contains at h_not_contains
  have h_none :
      List.findSome? (fun e =>
        if Bag.Entry.keyMatches e k then
          if hv : e.vc = hvc.code then some (hvc.proof ▸ hv ▸ e.v) else none
        else none) bag.storage = none := by
    rw [List.findSome?_eq_none_iff]
    intro e h_mem
    have h_false : Bag.Entry.keyMatches e k = false := by
      cases h_match : Bag.Entry.keyMatches e k
      · rfl
      · exfalso
        have h_any : bag.storage.any
            (fun e => Bag.Entry.keyMatches e k) = true :=
          List.any_eq_true.mpr ⟨e, h_mem, h_match⟩
        rw [h_any] at h_not_contains
        simp at h_not_contains
    simp [h_false]
  simp only [h_none, Option.getD_none]

@[simp] theorem object_bag_borrow_remove_same
    {U K V : Type} [Universe U] [HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : ObjectBag U) (k : K) :
    borrow K V (remove K V bag k).2 k = default :=
  object_bag_borrow_eq_default_of_not_contains _ k
    (object_bag_contains_remove_same bag k)

@[simp] theorem object_bag_remove_fst_eq_borrow
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : ObjectBag U) (k : K) :
    (remove K V bag k).1 = borrow K V bag k := rfl

/-- On an absent key, `set` behaves exactly like `add`
    (see `bag_set_eq_add_of_not_contains`). -/
theorem object_bag_set_eq_add_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : ObjectBag U) (k : K) (v : V)
    (h_not_contains : contains K bag k = false) :
    set K V bag k v = add K V bag k v := by
  unfold set add
  unfold contains at h_not_contains
  rw [h_not_contains]
  rfl

-- Distinct-key transports (citation-only; conditional).

theorem object_bag_contains_add_ne
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : ObjectBag U) (added key : K) (value : V)
    (h_ne : key ≠ added) :
    contains K (add K V bag added value) key = contains K bag key := by
  unfold contains add
  simp only [List.any_cons]
  have h_pack := BagFacts.keyMatches_pack (U := U) added value
  have h_head := BagFacts.keyMatches_eq_false_of_ne
    { kc := hkc.code, k := hkc.proof.symm ▸ added,
      vc := hvc.code, v := hvc.proof.symm ▸ value }
    added key (Ne.symm h_ne) h_pack
  rw [h_head, Bool.false_or]
  apply ListFacts.any_filter_not_of_disjoint
  intro entry h_match
  exact BagFacts.keyMatches_eq_false_of_ne entry added key (Ne.symm h_ne) h_match

theorem object_bag_contains_set_ne
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : ObjectBag U) (updated key : K) (value : V)
    (h_ne : key ≠ updated) :
    contains K (set K V bag updated value) key = contains K bag key := by
  unfold contains set
  simp only [List.any_cons]
  have h_pack := BagFacts.keyMatches_pack (U := U) updated value
  have h_head := BagFacts.keyMatches_eq_false_of_ne
    { kc := hkc.code, k := hkc.proof.symm ▸ updated,
      vc := hvc.code, v := hvc.proof.symm ▸ value }
    updated key (Ne.symm h_ne) h_pack
  rw [h_head, Bool.false_or]
  apply ListFacts.any_filter_not_of_disjoint
  intro entry h_match
  exact BagFacts.keyMatches_eq_false_of_ne entry updated key (Ne.symm h_ne) h_match

theorem object_bag_contains_remove_ne
    {U K V : Type} [Universe U] [HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : ObjectBag U) (removed key : K)
    (h_ne : key ≠ removed) :
    contains K (remove K V bag removed).2 key = contains K bag key := by
  unfold contains remove
  simp only []
  apply ListFacts.any_filter_not_of_disjoint
  intro entry h_match
  exact BagFacts.keyMatches_eq_false_of_ne entry removed key (Ne.symm h_ne) h_match

theorem object_bag_contains_with_type_add_ne
    {U K V W : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [hwc : HasCode U W] [DecidableEq K]
    (bag : ObjectBag U) (added key : K) (value : V)
    (h_ne : key ≠ added) :
    contains_with_type K W (add K V bag added value) key =
      contains_with_type K W bag key := by
  unfold contains_with_type add
  simp only [List.any_cons]
  have h_pack := BagFacts.keyMatches_pack (U := U) added value
  have h_head := BagFacts.keyMatches_eq_false_of_ne
    { kc := hkc.code, k := hkc.proof.symm ▸ added,
      vc := hvc.code, v := hvc.proof.symm ▸ value }
    added key (Ne.symm h_ne) h_pack
  rw [h_head]
  simp only [Bool.false_and, Bool.false_or]
  apply ListFacts.any_filter_not_of_disjoint
  intro entry h_match
  have h_false :=
    BagFacts.keyMatches_eq_false_of_ne entry added key (Ne.symm h_ne) h_match
  simp [h_false]

theorem object_bag_contains_with_type_set_ne
    {U K V W : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [hwc : HasCode U W] [DecidableEq K]
    (bag : ObjectBag U) (updated key : K) (value : V)
    (h_ne : key ≠ updated) :
    contains_with_type K W (set K V bag updated value) key =
      contains_with_type K W bag key := by
  unfold contains_with_type set
  simp only [List.any_cons]
  have h_pack := BagFacts.keyMatches_pack (U := U) updated value
  have h_head := BagFacts.keyMatches_eq_false_of_ne
    { kc := hkc.code, k := hkc.proof.symm ▸ updated,
      vc := hvc.code, v := hvc.proof.symm ▸ value }
    updated key (Ne.symm h_ne) h_pack
  rw [h_head]
  simp only [Bool.false_and, Bool.false_or]
  apply ListFacts.any_filter_not_of_disjoint
  intro entry h_match
  have h_false :=
    BagFacts.keyMatches_eq_false_of_ne entry updated key (Ne.symm h_ne) h_match
  simp [h_false]

theorem object_bag_contains_with_type_remove_ne
    {U K V W : Type} [Universe U] [HasCode U K] [hvc : HasCode U V]
    [hwc : HasCode U W] [DecidableEq K] [Inhabited V]
    (bag : ObjectBag U) (removed key : K)
    (h_ne : key ≠ removed) :
    contains_with_type K W (remove K V bag removed).2 key =
      contains_with_type K W bag key := by
  unfold contains_with_type remove
  simp only []
  apply ListFacts.any_filter_not_of_disjoint
  intro entry h_match
  have h_false :=
    BagFacts.keyMatches_eq_false_of_ne entry removed key (Ne.symm h_ne) h_match
  simp [h_false]

theorem object_bag_borrow_add_ne
    {U K RV WV : Type} [Universe U] [hkc : HasCode U K] [hrvc : HasCode U RV]
    [hwvc : HasCode U WV] [DecidableEq K] [Inhabited RV]
    (bag : ObjectBag U) (added key : K) (value : WV)
    (h_ne : key ≠ added) :
    borrow K RV (add K WV bag added value) key = borrow K RV bag key := by
  unfold borrow add
  simp only [List.findSome?_cons]
  have h_pack := BagFacts.keyMatches_pack (U := U) added value
  have h_head := BagFacts.keyMatches_eq_false_of_ne
    { kc := hkc.code, k := hkc.proof.symm ▸ added,
      vc := hwvc.code, v := hwvc.proof.symm ▸ value }
    added key (Ne.symm h_ne) h_pack
  simp only [h_head, Bool.false_eq_true, if_false]
  apply congrArg (fun found? : Option RV => found?.getD default)
  apply ListFacts.findSome?_filter_not_of_removed_none
  intro entry h_match
  have h_false :=
    BagFacts.keyMatches_eq_false_of_ne entry added key (Ne.symm h_ne) h_match
  simp [h_false]

theorem object_bag_borrow_set_ne
    {U K RV WV : Type} [Universe U] [hkc : HasCode U K] [hrvc : HasCode U RV]
    [hwvc : HasCode U WV] [DecidableEq K] [Inhabited RV]
    (bag : ObjectBag U) (updated key : K) (value : WV)
    (h_ne : key ≠ updated) :
    borrow K RV (set K WV bag updated value) key = borrow K RV bag key := by
  unfold borrow set
  simp only [List.findSome?_cons]
  have h_pack := BagFacts.keyMatches_pack (U := U) updated value
  have h_head := BagFacts.keyMatches_eq_false_of_ne
    { kc := hkc.code, k := hkc.proof.symm ▸ updated,
      vc := hwvc.code, v := hwvc.proof.symm ▸ value }
    updated key (Ne.symm h_ne) h_pack
  simp only [h_head, Bool.false_eq_true, if_false]
  apply congrArg (fun found? : Option RV => found?.getD default)
  apply ListFacts.findSome?_filter_not_of_removed_none
  intro entry h_match
  have h_false :=
    BagFacts.keyMatches_eq_false_of_ne entry updated key (Ne.symm h_ne) h_match
  simp [h_false]

theorem object_bag_borrow_remove_ne
    {U K RV WV : Type} [Universe U] [HasCode U K] [hrvc : HasCode U RV]
    [hwvc : HasCode U WV] [DecidableEq K] [Inhabited RV] [Inhabited WV]
    (bag : ObjectBag U) (removed key : K)
    (h_ne : key ≠ removed) :
    borrow K RV (remove K WV bag removed).2 key = borrow K RV bag key := by
  unfold borrow remove
  simp only []
  apply congrArg (fun found? : Option RV => found?.getD default)
  apply ListFacts.findSome?_filter_not_of_removed_none
  intro entry h_match
  have h_false :=
    BagFacts.keyMatches_eq_false_of_ne entry removed key (Ne.symm h_ne) h_match
  simp [h_false]

end Object_bag

-- ---------------------------------------------------------------------------
-- Pass 2: the size x remove row (see the BagNatives twin: ghost `size`
-- decrements unconditionally, so only storage-derived observers are framed;
-- duplicate keys make "length - 1" false, so eq-on-absent / le / lt).
-- ---------------------------------------------------------------------------

namespace Object_bag

-- (strict-decrease core consolidated into `ListFacts.length_filter_lt_of_any`
-- in `Prelude/Helpers.lean` by the lemma-wave landing.)

private theorem object_bag_remove_storage_eq_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : ObjectBag U) (k : K)
    (h_not_contains : contains K bag k = false) :
    (remove K V bag k).2.storage = bag.storage := by
  unfold contains at h_not_contains
  unfold remove
  show bag.storage.filter (fun e => !Bag.Entry.keyMatches e k) = bag.storage
  apply List.filter_eq_self.mpr
  intro e h_mem
  have h_false : Bag.Entry.keyMatches e k = false := by
    cases h_match : Bag.Entry.keyMatches e k
    · rfl
    · exfalso
      have h_any : bag.storage.any
          (fun e => Bag.Entry.keyMatches e k) = true :=
        List.any_eq_true.mpr ⟨e, h_mem, h_match⟩
      rw [h_any] at h_not_contains
      simp at h_not_contains
  simp [h_false]

theorem object_bag_length_remove_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : ObjectBag U) (k : K)
    (h_not_contains : contains K bag k = false) :
    length (remove K V bag k).2 = length bag := by
  apply BoundedNat.ext
  show ((remove K V bag k).2.storage).length % (2^64) =
    bag.storage.length % (2^64)
  rw [object_bag_remove_storage_eq_of_not_contains bag k h_not_contains]

theorem object_bag_is_empty_remove_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : ObjectBag U) (k : K)
    (h_not_contains : contains K bag k = false) :
    is_empty (remove K V bag k).2 = is_empty bag := by
  unfold is_empty
  rw [object_bag_remove_storage_eq_of_not_contains bag k h_not_contains]

theorem object_bag_length_remove_le
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : ObjectBag U) (k : K) :
    (length (remove K V bag k).2).val ≤ (length bag).val := by
  have h_bound := MoveVector.list_length_bounded (Bag.Entry U) bag.storage
  have h_le := List.length_filter_le
    (fun e : Bag.Entry U => !Bag.Entry.keyMatches e k) bag.storage
  unfold length remove
  show (bag.storage.filter _).length % (2^64) ≤ bag.storage.length % (2^64)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h_bound]
  exact h_le

theorem object_bag_length_remove_lt_of_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : ObjectBag U) (k : K)
    (h_contains : contains K bag k = true) :
    (length (remove K V bag k).2).val < (length bag).val := by
  have h_bound := MoveVector.list_length_bounded (Bag.Entry U) bag.storage
  unfold contains at h_contains
  have h_lt := ListFacts.length_filter_lt_of_any bag.storage
    (fun e => Bag.Entry.keyMatches e k) h_contains
  unfold length remove
  show (bag.storage.filter _).length % (2^64) < bag.storage.length % (2^64)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h_bound]
  exact h_lt

end Object_bag

-- Pass 2: matrix-audit fills (emptiness x writers, length x add/set guarded).
-- ObjectBag has no borrow_mut in the model, so no writeback faces here.

namespace Object_bag

@[simp] theorem object_bag_is_empty_add
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : ObjectBag U) (k : K) (v : V) :
    is_empty (add K V bag k v) = false := rfl

@[simp] theorem object_bag_is_empty_set
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : ObjectBag U) (k : K) (v : V) :
    is_empty (set K V bag k v) = false := rfl

theorem object_bag_length_add_val_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : ObjectBag U) (k : K) (v : V)
    (h_not_contains : contains K bag k = false) :
    (length (add K V bag k v)).val = (length bag).val + 1 := by
  unfold contains at h_not_contains
  have h_filter : bag.storage.filter
      (fun e => !Bag.Entry.keyMatches e k) = bag.storage := by
    apply List.filter_eq_self.mpr
    intro e h_mem
    have h_false : Bag.Entry.keyMatches e k = false := by
      cases h_match : Bag.Entry.keyMatches e k
      · rfl
      · exfalso
        have h_any : bag.storage.any
            (fun e => Bag.Entry.keyMatches e k) = true :=
          List.any_eq_true.mpr ⟨e, h_mem, h_match⟩
        rw [h_any] at h_not_contains
        simp at h_not_contains
    simp [h_false]
  have h_bound := MoveVector.list_length_bounded_pred (Bag.Entry U) bag.storage
  unfold length add
  show (_ :: bag.storage.filter _).length % (2^64) =
    bag.storage.length % (2^64) + 1
  rw [List.length_cons, h_filter]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem object_bag_length_set_val_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : ObjectBag U) (k : K) (v : V)
    (h_not_contains : contains K bag k = false) :
    (length (set K V bag k v)).val = (length bag).val + 1 := by
  rw [object_bag_set_eq_add_of_not_contains bag k v h_not_contains]
  exact object_bag_length_add_val_of_not_contains bag k v h_not_contains

end Object_bag

-- Pass 2: cross-container mirrors of the Bag facts the ObjectBag side lacked
-- (typed-presence weakening, occupancy bound, length bound, and the
-- keysUnique battery over the shared `Bag.packedKey`).

namespace Object_bag

theorem object_bag_contains_of_contains_with_type_eq_true
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : ObjectBag U) (k : K) :
    contains_with_type K V bag k = true → contains K bag k = true := by
  unfold contains_with_type contains
  simp only [List.any_eq_true, Bool.and_eq_true]
  rintro ⟨entry, h_mem, h_key, _h_type⟩
  exact ⟨entry, h_mem, h_key⟩

theorem object_bag_length_gt_zero_of_contains_with_type_eq_true
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : ObjectBag U) (k : K)
    (h_contains : contains_with_type K V bag k = true) :
    BoundedNat.gt (length bag) (0 : BoundedNat (2^64)) = true := by
  unfold contains_with_type at h_contains
  rcases (List.any_eq_true.mp h_contains) with ⟨entry, h_mem, _h_entry⟩
  have h_storage_ne : bag.storage ≠ [] := by
    intro h_nil
    simp [h_nil] at h_mem
  have h_len_pos : 0 < bag.storage.length :=
    List.length_pos_iff.mpr h_storage_ne
  have h_len_bound : bag.storage.length < 2^64 :=
    _root_.MoveVector.list_length_bounded (Bag.Entry U) bag.storage
  unfold length BoundedNat.gt
  have h_zero : (0 : BoundedNat (2^64)).val = 0 := by
    rfl
  simp [Nat.mod_eq_of_lt h_len_bound, h_zero, h_len_pos]

theorem object_bag_length_lt_u64_max_pred
    {U : Type} [Universe U] (bag : ObjectBag U)
    (m : BoundedNat (2^64)) (hm : m.val = 18446744073709551615) :
    BoundedNat.lt (length bag) m = true := by
  unfold length BoundedNat.lt
  have h := MoveVector.list_length_bounded_pred (Bag.Entry U) bag.storage
  apply nat_blt_eq_true
  rw [hm]
  show bag.storage.length % (2^64) < 18446744073709551615
  have hmod : bag.storage.length % (2^64) = bag.storage.length :=
    Nat.mod_eq_of_lt (by omega)
  omega

/-- An ObjectBag has unique keys iff its storage entries have distinct
    `Bag.packedKey`s (the entry type is shared with `Bag`). -/
def keysUnique {U : Type} [Universe U] (bag : ObjectBag U) : Prop :=
  (bag.storage.map Bag.packedKey).Nodup

theorem keysUnique_default {U : Type} [Universe U] :
    (((default : ObjectBag U).storage.map Bag.packedKey).Nodup) := by
  have hstorage : (default : ObjectBag U).storage = [] := rfl
  simp [hstorage]

theorem keysUnique_new {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (((new (U := U) ctx world).1.storage.map Bag.packedKey).Nodup) := by
  simp [new]

theorem keysUnique_add
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : ObjectBag U) (key : K) (value : V)
    (hunique : (bag.storage.map Bag.packedKey).Nodup)
    (habsent : contains K bag key = false) :
    ((add K V bag key value).storage.map Bag.packedKey).Nodup := by
  simp only [add, List.map_cons, List.nodup_cons]
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨entry, hentry, heq⟩
    have hfiltered := List.mem_filter.mp hentry
    have hmatch : Bag.Entry.keyMatches entry key = true := by
      rw [Bag.keyMatches_iff_packed_eq]
      simpa [Bag.packedKey, Bag.packed, add] using heq
    have hcontains : contains K bag key = true := by
      unfold contains
      rw [List.any_eq_true]
      exact ⟨entry, hfiltered.1, hmatch⟩
    rw [habsent] at hcontains
    simp at hcontains
  · exact (List.filter_sublist.map Bag.packedKey).nodup hunique

theorem keysUnique_set
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : ObjectBag U) (key : K) (value : V)
    (hunique : (bag.storage.map Bag.packedKey).Nodup) :
    ((set K V bag key value).storage.map Bag.packedKey).Nodup := by
  simp only [set, List.map_cons, List.nodup_cons]
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨entry, hentry, heq⟩
    have hfiltered := (List.mem_filter.mp hentry).2
    have hmatch : Bag.Entry.keyMatches entry key = true := by
      rw [Bag.keyMatches_iff_packed_eq]
      simpa [Bag.packedKey, Bag.packed, set] using heq
    simp [hmatch] at hfiltered
  · exact (List.filter_sublist.map Bag.packedKey).nodup hunique

end Object_bag

-- Pass 2 audit stragglers: object identity preserved by every writer.

namespace Object_bag

@[simp] theorem object_bag_id_add
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : ObjectBag U) (k : K) (v : V) :
    (add K V bag k v).id = bag.id := rfl

@[simp] theorem object_bag_id_set
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : ObjectBag U) (k : K) (v : V) :
    (set K V bag k v).id = bag.id := rfl

@[simp] theorem object_bag_id_remove
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : ObjectBag U) (k : K) :
    ((remove K V bag k).2).id = bag.id := rfl

end Object_bag
