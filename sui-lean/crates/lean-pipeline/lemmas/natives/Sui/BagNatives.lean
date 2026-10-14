-- Native implementations for sui::bag.
--
-- Move source: `public struct Bag has key, store { id: UID,
-- size: u64 }`. Heterogeneous storage -- one Bag holds entries of
-- arbitrary `(K, V)` pairs.
--
-- ## Toy-faithful design (entries IN the bag struct, no axioms)
--
-- `Bag (U : Type) [Universe U]` with `storage : List (Entry U)`.
-- `Entry U` has `k : Universe.interp kc` and `v : Universe.interp vc`
-- (dependent on the per-entry codes). Every `bag::add k v |>.borrow k`
-- law is provable by `rfl` given the renderer-emitted HasCode
-- instances (`HasCode TyCode T := ⟨ctor, rfl⟩`).
--
-- The historical `Vault_Types -> TyCodeInterp -> Vault_Types` file
-- cycle that blocked this design is broken by splitting user
-- `_Types.lean` into:
--   * `<Mod>_Types_Skeleton.lean` -- Bag-FREE structs only,
--     imported by `Generated/TyCodeInterp.lean`.
--   * `<Mod>_Types.lean` -- Bag-CONTAINING structs, imports
--     `TyCodeInterp` for the `[Universe TyCode]` instance.
-- The renderer emits both files automatically for modules that
-- contain any Bag-containing struct.
--
-- Bag itself is also filtered out of TyCode -- including it would
-- force `TyCodeInterp.lean` to reference `Bag.Bag TyCode` in its
-- interp body before the Universe instance is declared (forward
-- ref). Move programs that store Bag values via dyn_field need a
-- separate renderer path; the modeling-via-TyCode path doesn't
-- support them.
--
-- See `plans/lean-pipeline/dynamic-typing-via-repr-design.md` and
-- `plans/lean-pipeline/dynamic-typing-toy.lean`.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.ProgramState
import Prelude.Universe
import MoveStdlib.MoveVectorNatives
import Sui.ObjectNatives
import Sui.Tx_contextNatives

namespace Bag

/-- One heterogeneous key/value pair. -/
structure Entry (U : Type) [Universe U] where
  kc : U
  k  : Universe.interp kc
  vc : U
  v  : Universe.interp vc

instance {U : Type} [Universe U] : DecidableEq (Entry U) := by
  intro e1 e2
  cases e1 with
  | mk kc1 k1 vc1 v1 =>
    cases e2 with
    | mk kc2 k2 vc2 v2 =>
      match Universe.decEq kc1 kc2 with
      | isFalse hkc =>
        exact isFalse (by intro h; cases h; exact hkc rfl)
      | isTrue hkc =>
        subst kc2
        match Universe.decEqInterp kc1 k1 k2 with
        | isFalse hk =>
          exact isFalse (by intro h; cases h; exact hk rfl)
        | isTrue hk =>
          subst k2
          match Universe.decEq vc1 vc2 with
          | isFalse hvc =>
            exact isFalse (by intro h; cases h; exact hvc rfl)
          | isTrue hvc =>
            subst vc2
            match Universe.decEqInterp vc1 v1 v2 with
            | isFalse hv =>
              exact isFalse (by intro h; cases h; exact hv rfl)
            | isTrue hv =>
              subst v2
              exact isTrue rfl

/-- `Bag (U : Type) [Universe U]` -- typed storage IN the struct. -/
structure Bag (U : Type) [Universe U] where
  id      : Object.UID
  size    : BoundedNat (2^64)
  storage : List (Entry U)
deriving Inhabited, DecidableEq

/-- A `Bag` is a Sui `key`-ability object (Move: `struct Bag has key, store
    { id: UID, size: u64 }`), so it carries an object identity. Required
    when a Bag value is shared / transferred directly (e.g. a test helper
    calling `public_share_object` on a Bag field). The renderer only emits
    `HasObjectId` for user `key` structs, not framework native objects, so
    the instance is provided here. -/
instance {U : Type} [Universe U] : Object.HasObjectId (Bag U) where
  uid b := b.id

def new {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    Bag U × Tx_context.TxContext × Prover.World.World Ev Ob Df Be :=
  let created := Object.new ctx world
  (⟨created.1, (0 : BoundedNat (2^64)), []⟩, created.2.1, created.2.2)

/-- Allocation-frame pack (4/6): `bag::new` delegates its UID allocation
    to `object::new`, so dynamic-field storage survives the hop. Same
    statement and same one-line proof as `Table.new_world_df_entries`. -/
@[simp] theorem new_world_df_entries {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    ((new (U := U) ctx world).2.2).df_entries = world.df_entries := rfl

/-- Bag-store twin of `new_world_df_entries` (see
    `Table.new_world_df_bag_entries`). -/
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

/-- Raw struct-field faces of the fresh bag (WorldFrameLemmas migration:
    formerly `WorldFrame.bag_new_id`/`_size`/`_storage`). `new_storage` is
    the fact the `bag_*_new` observer family is really about, stated so it
    survives a caller that has already projected the bag out of the tuple
    (which is where those lemmas stop firing). -/
@[simp] theorem new_id {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (new (U := U) ctx world).1.id = (Object.new ctx world).1 := rfl

@[simp] theorem new_size {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (new (U := U) ctx world).1.size = (0 : BoundedNat (2^64)) := rfl

@[simp] theorem new_storage {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (new (U := U) ctx world).1.storage = ([] : List (Entry U)) := rfl

def new.aborts {U Ev Ob Df Be : Type} [Universe U]
    (_ctx : Tx_context.TxContext) (_world : Prover.World.World Ev Ob Df Be) : Bool := false

def uid_token {U : Type} [Universe U] (bag : Bag U) : List (BoundedNat (2^8)) :=
  Object.uid_token bag.id

def Entry.keyMatches {U : Type} [Universe U] {K : Type}
    [hkc : HasCode U K] [DecidableEq K] (e : Entry U) (k : K) : Bool :=
  if h : e.kc = hkc.code then
    let lifted : K := hkc.proof ▸ h ▸ e.k
    lifted == k
  else
    false

def add {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [DecidableEq K]
    (self : Bag U) (k : K) (v : V) : Bag U :=
  let entry : Entry U :=
    { kc := hkc.code, k  := hkc.proof.symm ▸ k
    , vc := hvc.code, v  := hvc.proof.symm ▸ v }
  let filtered := self.storage.filter (fun e => ! Entry.keyMatches e k)
  { self with size := self.size + 1, storage := entry :: filtered }

def add.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [DecidableEq K]
    (self : Bag U) (k : K) (_v : V) : Bool :=
  -- `bag::add` aborts when the key is present or the size increment overflows.
  self.storage.any (fun e => Entry.keyMatches e k) ||
    BoundedNat.add_aborts
      ⟨self.storage.length % (2^64), Nat.mod_lt _ (by decide)⟩
      (1 : BoundedNat (2^64))

/-- `Bag.set` — overwrites the value at key `k`, preserving size when
the key already exists (semantically the writeback companion of
`borrow_mut`). If the key is absent, behaves like `add` (size + 1).
The renderer emits `Bag.set` at writeback sites for
`let sa = bag::borrow_mut(bag, k); <mutate sa>` patterns so the
mutation propagates back into the bag's storage. -/
def set {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [DecidableEq K]
    (self : Bag U) (k : K) (v : V) : Bag U :=
  let entry : Entry U :=
    { kc := hkc.code, k  := hkc.proof.symm ▸ k
    , vc := hvc.code, v  := hvc.proof.symm ▸ v }
  let had_key := self.storage.any (fun e => Entry.keyMatches e k)
  let filtered := self.storage.filter (fun e => ! Entry.keyMatches e k)
  let new_size := if had_key then self.size else self.size + 1
  { self with size := new_size, storage := entry :: filtered }

def remove {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [DecidableEq K] [Inhabited V]
    (self : Bag U) (k : K) : V × Bag U :=
  let found? : Option V :=
    self.storage.findSome? (fun e =>
      if Entry.keyMatches e k then
        if hv : e.vc = hvc.code then
          some (hvc.proof ▸ hv ▸ e.v)
        else none
      else none)
  let v := found?.getD default
  let filtered := self.storage.filter (fun e => ! Entry.keyMatches e k)
  (v, { self with size := self.size - 1, storage := filtered })

def remove.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [hvc : HasCode U V] [DecidableEq K] [Inhabited V]
    (self : Bag U) (k : K) : Bool :=
  -- `bag::remove` aborts when the key is absent or has a different value type.
  ! self.storage.any (fun e => Entry.keyMatches e k && (e.vc = hvc.code))

def borrow {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [DecidableEq K] [Inhabited V]
    (self : Bag U) (k : K) : V :=
  let found? : Option V :=
    self.storage.findSome? (fun e =>
      if Entry.keyMatches e k then
        if hv : e.vc = hvc.code then
          some (hvc.proof ▸ hv ▸ e.v)
        else none
      else none)
  found?.getD default

def borrow.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [hvc : HasCode U V] [DecidableEq K] [Inhabited V]
    (self : Bag U) (k : K) : Bool :=
  -- `bag::borrow` aborts when the key is absent or has a different value type.
  ! self.storage.any (fun e => Entry.keyMatches e k && (e.vc = hvc.code))

/-- `bag::borrow_mut` — read-modify-write access to a bag value. The Mutable's
reconstruct writes the new value back via `set` (same key, same bag), so the
caller's `Mutable.apply` writeback lands in `Bag.storage`. Without this def the
Move-source lowering fell through to the `borrow_child_object_mut` default stub
and every bag read-modify-write was silently dropped (staking_pool
FungibleStakedSuiData supply/principal updates). -/
def borrow_mut {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [DecidableEq K] [Inhabited V]
    (self : Bag U) (k : K) : (Mutable V (Bag U)) × Bag U :=
  (Mutable.mk (borrow K V self k) (fun v => set K V self k v), self)

def borrow_mut.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [DecidableEq K] [Inhabited V]
    (_self : Bag U) (_k : K) : Bool := false

def contains {U : Type} [Universe U] (K : Type)

    [HasCode U K] [DecidableEq K]
    (self : Bag U) (k : K) : Bool :=
  self.storage.any (fun e => Entry.keyMatches e k)

def contains.aborts {U : Type} [Universe U] (K : Type)
    [HasCode U K] [DecidableEq K]
    (_self : Bag U) (_k : K) : Bool := false

def contains_with_type {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [DecidableEq K]
    (self : Bag U) (k : K) : Bool :=
  self.storage.any (fun e =>
    Entry.keyMatches e k && (e.vc = hvc.code))

def contains_with_type.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [DecidableEq K]
    (_self : Bag U) (_k : K) : Bool := false

-- length / is_empty DERIVED from storage (one source of truth; the
-- tracked `size` stays maintained but unread) -- see
-- container-df-unification.md "size/contains".
def length {U : Type} [Universe U] (self : Bag U) : BoundedNat (2^64) :=
  ⟨self.storage.length % (2^64), Nat.mod_lt _ (by decide)⟩
def length.aborts {U : Type} [Universe U] (_self : Bag U) : Bool := false

def is_empty {U : Type} [Universe U] (self : Bag U) : Bool :=
  self.storage.isEmpty
def is_empty.aborts {U : Type} [Universe U] (_self : Bag U) : Bool := false

def destroy_empty {U : Type} [Universe U] (_self : Bag U) : Unit := ()
-- Aborts (EBagNotEmpty) when the bag is non-empty. Real Move tests
-- `size == 0`; we read `storage` instead of the tracked `size` so this
-- agrees with `is_empty`/`length` (the single source of truth -- `size`
-- is maintained but unread, and is NOT tied to `storage.length` by any
-- structure invariant, so reading it here would make the spec unprovable).
def destroy_empty.aborts {U : Type} [Universe U] (self : Bag U) : Bool :=
  !self.storage.isEmpty

theorem bag_contains_of_contains_with_type_eq_true
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : Bag U) (k : K) :
    contains_with_type K V bag k = true →
      contains K bag k = true := by
  unfold contains_with_type contains
  simp only [List.any_eq_true, Bool.and_eq_true]
  rintro ⟨entry, h_mem, h_key, _h_type⟩
  exact ⟨entry, h_mem, h_key⟩

theorem bag_length_gt_zero_of_contains_with_type_eq_true
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : Bag U) (k : K)
    (h_contains : contains_with_type K V bag k = true) :
    BoundedNat.gt (length bag) (0 : BoundedNat (2^64)) = true := by
  unfold contains_with_type at h_contains
  rcases (List.any_eq_true.mp h_contains) with ⟨entry, h_mem, _h_entry⟩
  have h_storage_ne : bag.storage ≠ [] := by
    intro h_nil
    simp [h_nil] at h_mem
  have h_len_pos : 0 < bag.storage.length :=
    List.length_pos_iff.mpr h_storage_ne
  have h_len_bound :
      bag.storage.length < 2^64 :=
    _root_.MoveVector.list_length_bounded (Entry U) bag.storage
  unfold length BoundedNat.gt
  have h_zero : (0 : BoundedNat (2^64)).val = 0 := by
    rfl
  simp [Nat.mod_eq_of_lt h_len_bound, h_zero, h_len_pos]

@[simp]
theorem bag_borrow_aborts_eq_not_contains_with_type
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : Bag U) (k : K) :
    borrow.aborts K V bag k =
      !contains_with_type K V bag k := by
  unfold borrow.aborts contains_with_type
  rfl

@[simp]
theorem bag_remove_aborts_eq_not_contains_with_type
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : Bag U) (k : K) :
    remove.aborts K V bag k =
      !contains_with_type K V bag k := by
  unfold remove.aborts contains_with_type
  rfl

@[simp]
theorem bag_new_contains_with_type_eq_false
    {U K V Ev Ob Df Be : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] (ctx : Tx_context.TxContext)
    (world : Prover.World.World Ev Ob Df Be) (k : K) :
    contains_with_type K V (new (U := U) ctx world).1 k = false := by
  simp [new, contains_with_type]

@[simp]
theorem bag_new_contains_eq_false
    {U K Ev Ob Df Be : Type} [Universe U] [HasCode U K] [DecidableEq K]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (k : K) :
    contains K (new (U := U) ctx world).1 k = false := by
  simp [new, contains]

@[simp]
theorem bag_default_contains_with_type_eq_false
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (k : K) :
    contains_with_type K V (default : Bag U) k = false := by
  have h_storage : (default : Bag U).storage = [] := rfl
  simp [contains_with_type, h_storage]

@[simp]
theorem bag_default_contains_eq_false
    {U K : Type} [Universe U] [HasCode U K] [DecidableEq K]
    (k : K) :
    contains K (default : Bag U) k = false := by
  have h_storage : (default : Bag U).storage = [] := rfl
  simp [contains, h_storage]

@[simp]
theorem bag_default_length_eq_zero {U : Type} [Universe U] :
    length (default : Bag U) = (0 : BoundedNat (2^64)) := by
  have h_storage : (default : Bag U).storage = [] := rfl
  have h_zero : (0 : BoundedNat (2^64)).val = 0 := by
    rfl
  apply BoundedNat.ext
  simp [length, h_storage, h_zero]

@[simp]
theorem bag_contains_with_type_set_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : Bag U) (k : K) (v : V) :
    contains_with_type K V (set K V bag k v) k = true := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [contains_with_type, set, Entry.keyMatches]

@[simp]
theorem bag_contains_set_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : Bag U) (k : K) (v : V) :
    contains K (set K V bag k v) k = true := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [contains, set, Entry.keyMatches]

@[simp]
theorem bag_borrow_set_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V] (bag : Bag U) (k : K) (v : V) :
    borrow K V (set K V bag k v) k = v := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [borrow, set, Entry.keyMatches]

@[simp]
theorem bag_add_aborts_eq_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] (bag : Bag U) (k : K) (v : V) :
    add.aborts K V bag k v =
      (contains K bag k ||
        BoundedNat.add_aborts (length bag) (1 : BoundedNat (2^64))) := by
  rfl

@[simp]
theorem bag_contains_with_type_add_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : Bag U) (k : K) (v : V) :
    contains_with_type K V (add K V bag k v) k = true := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [contains_with_type, add, Entry.keyMatches]

@[simp]
theorem bag_contains_with_type_remove_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : Bag U) (k : K) :
    contains_with_type K V (remove K V bag k).2 k = false := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [contains_with_type, remove, Entry.keyMatches]
      intro _ _ h_no_key h_key h_lift_eq _h_type
      exact (h_no_key h_key) h_lift_eq

@[simp]
theorem bag_contains_add_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : Bag U) (k : K) (v : V) :
    contains K (add K V bag k v) k = true := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [contains, add, Entry.keyMatches]

@[simp]
theorem bag_borrow_add_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V] (bag : Bag U) (k : K) (v : V) :
    borrow K V (add K V bag k v) k = v := by
  cases hkc with
  | mk kcode kproof =>
    cases kproof
    cases hvc with
    | mk vcode vproof =>
      cases vproof
      simp [borrow, add, Entry.keyMatches]

-- ---------------------------------------------------------------------------
-- Packed-key uniqueness machinery (framework-owned).
--
-- Relocated from a per-package `specs.Invs` prototype so any package can
-- reason about bag key-uniqueness. `packedKey` is the type-erased key
-- identity of an entry (its code + interpreted value as a dependent pair);
-- two entries collide as keys iff their `packedKey`s coincide. `keysUnique`
-- is the bag invariant `(storage.map packedKey).Nodup`, preserved by `add`
-- (on an absent key) and `set`. Fully generic over `[Universe U]`.
-- ---------------------------------------------------------------------------

/-- Type-erased key identity of an entry: its key code paired with the
interpreted key value, as a dependent pair. -/
def packedKey {U : Type} [Universe U] (entry : Entry U) :
    Sigma (fun code : U => Universe.interp code) :=
  ⟨entry.kc, entry.k⟩

/-- Type-erased key identity of a typed key `key : K`, via its `HasCode`. -/
def packed {U K : Type} [Universe U] [hkc : HasCode U K] (key : K) :
    Sigma (fun code : U => Universe.interp code) :=
  ⟨hkc.code, hkc.proof.symm ▸ key⟩

/-- A bag has unique keys iff its storage entries have distinct `packedKey`s. -/
def keysUnique {U : Type} [Universe U] (bag : Bag U) : Prop :=
  (bag.storage.map packedKey).Nodup

/-! ### The empty-storage bag literal (WorldFrameLemmas migration)

`bag::new`'s bag is `⟨uid, 0, []⟩`, and the `bag_*_new` observer lemmas are
stated over `(Bag.new ctx w).1`. A proof that has already materialised the
literal (any `simp` list carrying `Bag.new`, or a `Bag` read back out of
`df_bag_entries` where the stored `storage` is `[]`) no longer matches them,
and the observer is stuck mid-goal -- the "bag-literal casualty". Frame the
observers on the STORAGE instead: `[]` decides every membership question, so
these hold for any uid and any (unread) `size` field. -/

@[simp] theorem contains_storage_nil {U : Type} [Universe U]
    (K : Type) [HasCode U K] [DecidableEq K]
    (uid : Object.UID) (sz : BoundedNat (2^64)) (k : K) :
    contains K (⟨uid, sz, []⟩ : Bag U) k = false := rfl

@[simp] theorem contains_with_type_storage_nil {U : Type} [Universe U]
    (K V : Type) [HasCode U K] [HasCode U V] [DecidableEq K]
    (uid : Object.UID) (sz : BoundedNat (2^64)) (k : K) :
    contains_with_type K V (⟨uid, sz, []⟩ : Bag U) k = false := rfl

@[simp] theorem is_empty_storage_nil {U : Type} [Universe U]
    (uid : Object.UID) (sz : BoundedNat (2^64)) :
    is_empty (⟨uid, sz, []⟩ : Bag U) = true := rfl

@[simp] theorem keysUnique_storage_nil {U : Type} [Universe U]
    (uid : Object.UID) (sz : BoundedNat (2^64)) :
    keysUnique (⟨uid, sz, []⟩ : Bag U) := by
  simp [keysUnique]

/-- `bag::add` / `bag::set` at the STORAGE level (WorldFrameLemmas
migration). Both write `entry :: <old storage minus the key>`, and every
`Bag` observer (`contains`, `length`, `keysUnique`) is defined over
`storage` -- so a goal that projects storage out of a write can keep walking
down to the bag it was written into. Without this the chain stops at
`(Bag.add .. bag ..).storage` and a `bag`-level frame (e.g. the df
round-trip `store_bag_borrow (store_bag_set ..)`, whose result agrees with
the written bag on `size`/`storage` but NOT on `id`) can never fire. Not an
unfold of the observers: `contains`/`length` patterns still match
`add`/`set` first.

CITATION-ONLY (battery decision at the wave landing): as ambient `@[simp]`
these eagerly decompose every bag write into its storage cons/filter form,
splitting goals (e.g. `keysUnique` preservation after a `set`) that the
bag-level lemmas close whole -- measured on ember's Deposit proof. The
WorldFrameLemmas island only ever exposed them to files that hand-imported
it; proofs that project storage cite them explicitly. -/
theorem add_storage {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [DecidableEq K]
    (self : Bag U) (k : K) (v : V) :
    (add K V self k v).storage
      = ({ kc := hkc.code, k := hkc.proof.symm ▸ k,
           vc := hvc.code, v := hvc.proof.symm ▸ v } : Entry U)
        :: self.storage.filter (fun e => ! Entry.keyMatches e k) := rfl

theorem set_storage {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [DecidableEq K]
    (self : Bag U) (k : K) (v : V) :
    (set K V self k v).storage
      = ({ kc := hkc.code, k := hkc.proof.symm ▸ k,
           vc := hvc.code, v := hvc.proof.symm ▸ v } : Entry U)
        :: self.storage.filter (fun e => ! Entry.keyMatches e k) := rfl

theorem keyMatches_iff_packed_eq
    {U K : Type} [Universe U] [hkc : HasCode U K] [DecidableEq K]
    (entry : Entry U) (key : K) :
    Entry.keyMatches entry key = true ↔
      packedKey entry = packed key := by
  cases entry with
  | mk entryCode entryKey valueCode value =>
    cases hkc with
    | mk code proof =>
      cases proof
      by_cases h : entryCode = code
      · subst entryCode
        simp [packedKey, packed, Entry.keyMatches]
      · simp [packedKey, packed, Entry.keyMatches, h]

theorem keysUnique_default {U : Type} [Universe U] :
    (((default : Bag U).storage.map packedKey).Nodup) := by
  have hstorage : (default : Bag U).storage = [] := rfl
  simp [hstorage]

theorem keysUnique_new {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (((new (U := U) ctx world).1.storage.map packedKey).Nodup) := by
  simp [new]

theorem keysUnique_add
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : Bag U) (key : K) (value : V)
    (hunique : (bag.storage.map packedKey).Nodup)
    (habsent : contains K bag key = false) :
    ((add K V bag key value).storage.map packedKey).Nodup := by
  simp only [add, List.map_cons, List.nodup_cons]
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨entry, hentry, heq⟩
    have hfiltered := List.mem_filter.mp hentry
    have hmatch : Entry.keyMatches entry key = true := by
      rw [keyMatches_iff_packed_eq]
      simpa [packedKey, packed, add] using heq
    have hcontains : contains K bag key = true := by
      unfold contains
      rw [List.any_eq_true]
      exact ⟨entry, hfiltered.1, hmatch⟩
    rw [habsent] at hcontains
    simp at hcontains
  · exact (List.filter_sublist.map packedKey).nodup hunique

theorem keysUnique_add_new
    {U K V Ev Ob Df Be : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] (ctx : Tx_context.TxContext)
    (world : Prover.World.World Ev Ob Df Be) (key : K) (value : V) :
    ((add K V (new (U := U) ctx world).1 key value).storage.map
      packedKey).Nodup := by
  apply keysUnique_add
  · exact keysUnique_new ctx world
  · exact bag_new_contains_eq_false ctx world key

theorem keysUnique_set
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : Bag U) (key : K) (value : V)
    (hunique : (bag.storage.map packedKey).Nodup) :
    ((set K V bag key value).storage.map packedKey).Nodup := by
  simp only [set, List.map_cons, List.nodup_cons]
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨entry, hentry, heq⟩
    have hfiltered := (List.mem_filter.mp hentry).2
    have hmatch : Entry.keyMatches entry key = true := by
      rw [keyMatches_iff_packed_eq]
      simpa [packedKey, packed, set] using heq
    simp [hmatch] at hfiltered
  · exact (List.filter_sublist.map packedKey).nodup hunique

theorem eq_of_mem_of_mem_of_map_nodup
    {A B : Type} (f : A → B) {xs : List A} {a b : A}
    (hunique : (xs.map f).Nodup)
    (ha : a ∈ xs) (hb : b ∈ xs) (heq : f a = f b) :
    a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      simp only [List.map_cons, List.nodup_cons] at hunique
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · rfl
        · exfalso
          apply hunique.1
          exact List.mem_map.mpr ⟨b, hb, heq.symm⟩
      · rcases hb with rfl | hb
        · exfalso
          apply hunique.1
          exact List.mem_map.mpr ⟨a, ha, heq⟩
        · exact ih hunique.2 ha hb

theorem contains_with_type_set_preserved_of_keysUnique
    {U K V W : Type} [Universe U]
    [hkc : HasCode U K] [hvc : HasCode U V] [hwc : HasCode U W]
    [DecidableEq K]
    (bag : Bag U) (oldKey newKey : K) (newValue : W)
    (hunique : (bag.storage.map packedKey).Nodup)
    (hold : contains_with_type K V bag oldKey = true)
    (hnew : contains_with_type K W bag newKey = true) :
    contains_with_type K V
      (set K W bag newKey newValue) oldKey = true := by
  unfold contains_with_type at hold hnew ⊢
  simp only [List.any_eq_true, Bool.and_eq_true] at hold hnew ⊢
  rcases hold with ⟨oldEntry, holdMem, holdKey, holdType⟩
  rcases hnew with ⟨newEntry, hnewMem, hnewKey, hnewType⟩
  have holdPacked : packedKey oldEntry = packed oldKey :=
    (keyMatches_iff_packed_eq oldEntry oldKey).mp holdKey
  have hnewPacked : packedKey newEntry = packed newKey :=
    (keyMatches_iff_packed_eq newEntry newKey).mp hnewKey
  let replacement : Entry U :=
    { kc := hkc.code, k := hkc.proof.symm ▸ newKey
    , vc := hwc.code, v := hwc.proof.symm ▸ newValue }
  by_cases hkeys : packed (U := U) oldKey = packed (U := U) newKey
  · have hentries : oldEntry = newEntry := by
      apply eq_of_mem_of_mem_of_map_nodup packedKey hunique holdMem hnewMem
      exact holdPacked.trans (hkeys.trans hnewPacked.symm)
    subst newEntry
    have holdTypeProp : oldEntry.vc = hvc.code := of_decide_eq_true holdType
    have hnewTypeProp : oldEntry.vc = hwc.code := of_decide_eq_true hnewType
    have hcodes : hwc.code = hvc.code := hnewTypeProp.symm.trans holdTypeProp
    refine ⟨replacement, ?_, ?_, ?_⟩
    · simp [replacement, set]
    · rw [keyMatches_iff_packed_eq]
      simpa [replacement, packedKey, packed] using hkeys.symm
    · exact decide_eq_true (by simpa [replacement] using hcodes)
  · have hnotMatch : Entry.keyMatches oldEntry newKey = false := by
      cases hm : Entry.keyMatches oldEntry newKey
      · rfl
      · exfalso
        apply hkeys
        exact holdPacked.symm.trans
          ((keyMatches_iff_packed_eq oldEntry newKey).mp hm)
    refine ⟨oldEntry, ?_, holdKey, holdType⟩
    simp [set, holdMem, hnotMatch]

end Bag

theorem bag_contains_of_contains_with_type_eq_true
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) :
    _root_.Bag.contains_with_type K V bag k = true →
      _root_.Bag.contains K bag k = true :=
  _root_.Bag.bag_contains_of_contains_with_type_eq_true bag k

theorem bag_length_gt_zero_of_contains_with_type_eq_true
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K)
    (h_contains : _root_.Bag.contains_with_type K V bag k = true) :
    BoundedNat.gt (_root_.Bag.length bag) (0 : BoundedNat (2^64)) = true :=
  _root_.Bag.bag_length_gt_zero_of_contains_with_type_eq_true bag k h_contains

@[simp]
theorem bag_borrow_aborts_eq_not_contains_with_type
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : _root_.Bag.Bag U) (k : K) :
    _root_.Bag.borrow.aborts K V bag k =
      !_root_.Bag.contains_with_type K V bag k :=
  _root_.Bag.bag_borrow_aborts_eq_not_contains_with_type bag k

@[simp]
theorem bag_remove_aborts_eq_not_contains_with_type
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : _root_.Bag.Bag U) (k : K) :
    _root_.Bag.remove.aborts K V bag k =
      !_root_.Bag.contains_with_type K V bag k :=
  _root_.Bag.bag_remove_aborts_eq_not_contains_with_type bag k

@[simp]
theorem bag_new_contains_with_type_eq_false
    {U K V Ev Ob Df Be : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] (ctx : Tx_context.TxContext)
    (world : Prover.World.World Ev Ob Df Be) (k : K) :
    _root_.Bag.contains_with_type K V (_root_.Bag.new (U := U) ctx world).1 k = false :=
  _root_.Bag.bag_new_contains_with_type_eq_false ctx world k

@[simp]
theorem bag_new_contains_eq_false
    {U K Ev Ob Df Be : Type} [Universe U] [HasCode U K] [DecidableEq K]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (k : K) :
    _root_.Bag.contains K (_root_.Bag.new (U := U) ctx world).1 k = false :=
  _root_.Bag.bag_new_contains_eq_false ctx world k

@[simp]
theorem bag_default_contains_with_type_eq_false
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (k : K) :
    _root_.Bag.contains_with_type K V (default : _root_.Bag.Bag U) k = false :=
  _root_.Bag.bag_default_contains_with_type_eq_false k

@[simp]
theorem bag_default_contains_eq_false
    {U K : Type} [Universe U] [HasCode U K] [DecidableEq K]
    (k : K) :
    _root_.Bag.contains K (default : _root_.Bag.Bag U) k = false :=
  _root_.Bag.bag_default_contains_eq_false k

@[simp]
theorem bag_default_length_eq_zero {U : Type} [Universe U] :
    _root_.Bag.length (default : _root_.Bag.Bag U) = (0 : BoundedNat (2^64)) :=
  _root_.Bag.bag_default_length_eq_zero

@[simp]
theorem bag_contains_with_type_set_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) (v : V) :
    _root_.Bag.contains_with_type K V (_root_.Bag.set K V bag k v) k = true :=
  _root_.Bag.bag_contains_with_type_set_same bag k v

@[simp]
theorem bag_contains_set_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) (v : V) :
    _root_.Bag.contains K (_root_.Bag.set K V bag k v) k = true :=
  _root_.Bag.bag_contains_set_same bag k v

@[simp]
theorem bag_borrow_set_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V] (bag : _root_.Bag.Bag U) (k : K) (v : V) :
    _root_.Bag.borrow K V (_root_.Bag.set K V bag k v) k = v :=
  _root_.Bag.bag_borrow_set_same bag k v

@[simp]
theorem bag_add_aborts_eq_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] (bag : _root_.Bag.Bag U) (k : K) (v : V) :
    _root_.Bag.add.aborts K V bag k v =
      (_root_.Bag.contains K bag k ||
        BoundedNat.add_aborts (_root_.Bag.length bag) (1 : BoundedNat (2^64))) :=
  _root_.Bag.bag_add_aborts_eq_contains bag k v

@[simp]
theorem bag_contains_with_type_add_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) (v : V) :
    _root_.Bag.contains_with_type K V (_root_.Bag.add K V bag k v) k = true :=
  _root_.Bag.bag_contains_with_type_add_same bag k v

@[simp]
theorem bag_contains_with_type_remove_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : _root_.Bag.Bag U) (k : K) :
    _root_.Bag.contains_with_type K V (_root_.Bag.remove K V bag k).2 k = false :=
  _root_.Bag.bag_contains_with_type_remove_same bag k

@[simp]
theorem bag_contains_add_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) (v : V) :
    _root_.Bag.contains K (_root_.Bag.add K V bag k v) k = true :=
  _root_.Bag.bag_contains_add_same bag k v

@[simp]
theorem bag_borrow_add_same
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V] (bag : _root_.Bag.Bag U) (k : K) (v : V) :
    _root_.Bag.borrow K V (_root_.Bag.add K V bag k v) k = v :=
  _root_.Bag.bag_borrow_add_same bag k v

/-! ## Shared `Bag.Entry.keyMatches` facts

`Bag.Entry` is also the df-entry payload, so these two are the leaves under
every "the write at another key did not disturb my read" dynamic-field proof.
Namespaced per the standing rule in
`plans/lean-pipeline/shared-proof-infra.md`. -/

namespace BagFacts

/-- A freshly packed entry matches the key it was packed with. -/
theorem keyMatches_pack {U K V : Type} [Universe U] [hkc : HasCode U K]
    [hvc : HasCode U V] [DecidableEq K] (key : K) (value : V) :
    _root_.Bag.Entry.keyMatches
      { kc := hkc.code, k := hkc.proof.symm ▸ key,
        vc := hvc.code, v := hvc.proof.symm ▸ value } key = true := by
  cases hkc with
  | mk code proof =>
      cases proof
      simp [_root_.Bag.Entry.keyMatches]

/-- An entry matches at most one key of a given type. -/
theorem keyMatches_eq_false_of_ne {U K : Type} [Universe U] [hkc : HasCode U K]
    [DecidableEq K] (entry : _root_.Bag.Entry U) (left right : K)
    (h_ne : left ≠ right)
    (h_left : _root_.Bag.Entry.keyMatches entry left = true) :
    _root_.Bag.Entry.keyMatches entry right = false := by
  cases hkc with
  | mk code proof =>
      unfold _root_.Bag.Entry.keyMatches at h_left ⊢
      by_cases h_code : entry.kc = code
      · simp only [h_code, ↓reduceDIte] at h_left ⊢
        apply Bool.eq_false_iff.mpr
        intro h_right
        exact h_ne ((LawfulBEq.eq_of_beq h_left).symm.trans
          (LawfulBEq.eq_of_beq h_right))
      · simp [h_code] at h_left

end BagFacts

-- ---------------------------------------------------------------------------
-- Matrix completion: constructor faces, total abort-face bridges, and the
-- distinct-key transports (the `_ne` column) for `add` / `set` / `remove`.
-- The `_ne` lemmas are conditional, so they stay citation-only per the
-- standing attribute discipline; the constructor faces and `= false`
-- bridges are rfl-class frames and carry `@[simp]` like their neighbours.
-- ---------------------------------------------------------------------------

@[simp]
theorem bag_new_aborts_eq_false
    {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    _root_.Bag.new.aborts (U := U) ctx world = false := rfl

@[simp]
theorem bag_contains_aborts_eq_false
    {U K : Type} [Universe U] [HasCode U K] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) :
    _root_.Bag.contains.aborts K bag k = false := rfl

@[simp]
theorem bag_contains_with_type_aborts_eq_false
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) :
    _root_.Bag.contains_with_type.aborts K V bag k = false := rfl

@[simp]
theorem bag_borrow_mut_aborts_eq_false
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : _root_.Bag.Bag U) (k : K) :
    _root_.Bag.borrow_mut.aborts K V bag k = false := rfl

@[simp]
theorem bag_length_aborts_eq_false {U : Type} [Universe U]
    (bag : _root_.Bag.Bag U) :
    _root_.Bag.length.aborts bag = false := rfl

@[simp]
theorem bag_is_empty_aborts_eq_false {U : Type} [Universe U]
    (bag : _root_.Bag.Bag U) :
    _root_.Bag.is_empty.aborts bag = false := rfl

/-- Abort-face bridge for `destroy_empty` (both sides read `storage`). -/
@[simp]
theorem bag_destroy_empty_aborts_eq_not_is_empty {U : Type} [Universe U]
    (bag : _root_.Bag.Bag U) :
    _root_.Bag.destroy_empty.aborts bag = !_root_.Bag.is_empty bag := rfl

@[simp]
theorem bag_borrow_new
    {U K V Ev Ob Df Be : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (k : K) :
    _root_.Bag.borrow K V (_root_.Bag.new (U := U) ctx world).1 k = default := rfl

@[simp]
theorem bag_length_new_eq_zero
    {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    _root_.Bag.length (_root_.Bag.new (U := U) ctx world).1 =
      (0 : BoundedNat (2^64)) := rfl

@[simp]
theorem bag_is_empty_new
    {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    _root_.Bag.is_empty (_root_.Bag.new (U := U) ctx world).1 = true := rfl

@[simp]
theorem bag_destroy_empty_aborts_new
    {U Ev Ob Df Be : Type} [Universe U]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    _root_.Bag.destroy_empty.aborts (_root_.Bag.new (U := U) ctx world).1 =
      false := rfl

/-- The create face: `bag::new` then `bag::add` never aborts -- the fresh bag
    contains no key and the size increment `0 + 1` cannot overflow. -/
@[simp]
theorem bag_add_aborts_new
    {U K V Ev Ob Df Be : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be)
    (k : K) (v : V) :
    _root_.Bag.add.aborts K V (_root_.Bag.new (U := U) ctx world).1 k v =
      false := rfl

@[simp]
theorem bag_borrow_aborts_new
    {U K V Ev Ob Df Be : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (k : K) :
    _root_.Bag.borrow.aborts K V (_root_.Bag.new (U := U) ctx world).1 k =
      true := rfl

@[simp]
theorem bag_remove_aborts_new
    {U K V Ev Ob Df Be : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (k : K) :
    _root_.Bag.remove.aborts K V (_root_.Bag.new (U := U) ctx world).1 k =
      true := rfl

/-- `remove`'s value component IS the `borrow` read (same `findSome?`). -/
@[simp]
theorem bag_remove_fst_eq_borrow
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : _root_.Bag.Bag U) (k : K) :
    (_root_.Bag.remove K V bag k).1 = _root_.Bag.borrow K V bag k := rfl

/-- On an absent key, `set` behaves exactly like `add` (same storage action;
    the size branch collapses). Lets every `set` lemma transfer to `add`
    sites and vice versa under the add-side non-abort face. -/
theorem bag_set_eq_add_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) (v : V)
    (h_not_contains : _root_.Bag.contains K bag k = false) :
    _root_.Bag.set K V bag k v = _root_.Bag.add K V bag k v := by
  unfold _root_.Bag.set _root_.Bag.add
  unfold _root_.Bag.contains at h_not_contains
  rw [h_not_contains]
  rfl

/-- `remove` deletes every entry at the key: same-key presence goes false
    (plain `contains`; the `contains_with_type` form already existed). -/
@[simp]
theorem bag_contains_remove_same
    {U K V : Type} [Universe U] [HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : _root_.Bag.Bag U) (k : K) :
    _root_.Bag.contains K (_root_.Bag.remove K V bag k).2 k = false := by
  unfold _root_.Bag.contains _root_.Bag.remove
  apply Bool.eq_false_iff.mpr
  intro h_any
  rcases List.any_eq_true.mp h_any with ⟨entry, h_mem, h_match⟩
  have h_kept := (List.mem_filter.mp h_mem).2
  rw [h_match] at h_kept
  simp at h_kept

/-- The absent-key read: `borrow` falls back to the model default whenever
    the key is not present. The general fact behind every same-key-after-
    delete corollary. -/
theorem bag_borrow_eq_default_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : _root_.Bag.Bag U) (k : K)
    (h_not_contains : _root_.Bag.contains K bag k = false) :
    _root_.Bag.borrow K V bag k = default := by
  unfold _root_.Bag.borrow
  unfold _root_.Bag.contains at h_not_contains
  have h_none :
      List.findSome? (fun e =>
        if _root_.Bag.Entry.keyMatches e k then
          if hv : e.vc = hvc.code then some (hvc.proof ▸ hv ▸ e.v) else none
        else none) bag.storage = none := by
    rw [List.findSome?_eq_none_iff]
    intro e h_mem
    have h_false : _root_.Bag.Entry.keyMatches e k = false := by
      cases h_match : _root_.Bag.Entry.keyMatches e k
      · rfl
      · exfalso
        have h_any : bag.storage.any
            (fun e => _root_.Bag.Entry.keyMatches e k) = true :=
          List.any_eq_true.mpr ⟨e, h_mem, h_match⟩
        rw [h_any] at h_not_contains
        simp at h_not_contains
    simp [h_false]
  simp only [h_none, Option.getD_none]

/-- Same-key read after `remove` falls back to the model default. -/
@[simp]
theorem bag_borrow_remove_same
    {U K V : Type} [Universe U] [HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : _root_.Bag.Bag U) (k : K) :
    _root_.Bag.borrow K V (_root_.Bag.remove K V bag k).2 k = default :=
  bag_borrow_eq_default_of_not_contains _ k (bag_contains_remove_same bag k)

/-- Distinct-key transports: a write at `added`/`updated`/`removed` leaves
    every observer at a DIFFERENT key of the same key type unchanged. -/
theorem bag_contains_add_ne
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : _root_.Bag.Bag U) (added key : K) (value : V)
    (h_ne : key ≠ added) :
    _root_.Bag.contains K (_root_.Bag.add K V bag added value) key =
      _root_.Bag.contains K bag key := by
  unfold _root_.Bag.contains _root_.Bag.add
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

theorem bag_contains_set_ne
    {U K V : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [DecidableEq K]
    (bag : _root_.Bag.Bag U) (updated key : K) (value : V)
    (h_ne : key ≠ updated) :
    _root_.Bag.contains K (_root_.Bag.set K V bag updated value) key =
      _root_.Bag.contains K bag key := by
  unfold _root_.Bag.contains _root_.Bag.set
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

theorem bag_contains_remove_ne
    {U K V : Type} [Universe U] [HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : _root_.Bag.Bag U) (removed key : K)
    (h_ne : key ≠ removed) :
    _root_.Bag.contains K (_root_.Bag.remove K V bag removed).2 key =
      _root_.Bag.contains K bag key := by
  unfold _root_.Bag.contains _root_.Bag.remove
  simp only []
  apply ListFacts.any_filter_not_of_disjoint
  intro entry h_match
  exact BagFacts.keyMatches_eq_false_of_ne entry removed key (Ne.symm h_ne) h_match

theorem bag_contains_with_type_add_ne
    {U K V W : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [hwc : HasCode U W] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (added key : K) (value : V)
    (h_ne : key ≠ added) :
    _root_.Bag.contains_with_type K W (_root_.Bag.add K V bag added value) key =
      _root_.Bag.contains_with_type K W bag key := by
  unfold _root_.Bag.contains_with_type _root_.Bag.add
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

theorem bag_contains_with_type_set_ne
    {U K V W : Type} [Universe U] [hkc : HasCode U K] [hvc : HasCode U V]
    [hwc : HasCode U W] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (updated key : K) (value : V)
    (h_ne : key ≠ updated) :
    _root_.Bag.contains_with_type K W (_root_.Bag.set K V bag updated value) key =
      _root_.Bag.contains_with_type K W bag key := by
  unfold _root_.Bag.contains_with_type _root_.Bag.set
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

theorem bag_contains_with_type_remove_ne
    {U K V W : Type} [Universe U] [HasCode U K] [hvc : HasCode U V]
    [hwc : HasCode U W] [DecidableEq K] [Inhabited V]
    (bag : _root_.Bag.Bag U) (removed key : K)
    (h_ne : key ≠ removed) :
    _root_.Bag.contains_with_type K W (_root_.Bag.remove K V bag removed).2 key =
      _root_.Bag.contains_with_type K W bag key := by
  unfold _root_.Bag.contains_with_type _root_.Bag.remove
  simp only []
  apply ListFacts.any_filter_not_of_disjoint
  intro entry h_match
  have h_false :=
    BagFacts.keyMatches_eq_false_of_ne entry removed key (Ne.symm h_ne) h_match
  simp [h_false]

/-- Distinct-key read transports. The read value type (`RV`) and the written
    value type (`WV`) are independent, mirroring
    `DynamicFieldEffects.borrow_set_key_ne`. -/
theorem bag_borrow_add_ne
    {U K RV WV : Type} [Universe U] [hkc : HasCode U K] [hrvc : HasCode U RV]
    [hwvc : HasCode U WV] [DecidableEq K] [Inhabited RV]
    (bag : _root_.Bag.Bag U) (added key : K) (value : WV)
    (h_ne : key ≠ added) :
    _root_.Bag.borrow K RV (_root_.Bag.add K WV bag added value) key =
      _root_.Bag.borrow K RV bag key := by
  unfold _root_.Bag.borrow _root_.Bag.add
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

theorem bag_borrow_set_ne
    {U K RV WV : Type} [Universe U] [hkc : HasCode U K] [hrvc : HasCode U RV]
    [hwvc : HasCode U WV] [DecidableEq K] [Inhabited RV]
    (bag : _root_.Bag.Bag U) (updated key : K) (value : WV)
    (h_ne : key ≠ updated) :
    _root_.Bag.borrow K RV (_root_.Bag.set K WV bag updated value) key =
      _root_.Bag.borrow K RV bag key := by
  unfold _root_.Bag.borrow _root_.Bag.set
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

theorem bag_borrow_remove_ne
    {U K RV WV : Type} [Universe U] [HasCode U K] [hrvc : HasCode U RV]
    [hwvc : HasCode U WV] [DecidableEq K] [Inhabited RV] [Inhabited WV]
    (bag : _root_.Bag.Bag U) (removed key : K)
    (h_ne : key ≠ removed) :
    _root_.Bag.borrow K RV (_root_.Bag.remove K WV bag removed).2 key =
      _root_.Bag.borrow K RV bag key := by
  unfold _root_.Bag.borrow _root_.Bag.remove
  simp only []
  apply congrArg (fun found? : Option RV => found?.getD default)
  apply ListFacts.findSome?_filter_not_of_removed_none
  intro entry h_match
  have h_false :=
    BagFacts.keyMatches_eq_false_of_ne entry removed key (Ne.symm h_ne) h_match
  simp [h_false]

-- ---------------------------------------------------------------------------
-- Pass 2: the size x remove row. NOTE: unlike `Table.remove`, `Bag.remove`
-- decrements the ghost `size` field UNCONDITIONALLY (no branch), so the
-- struct-level "remove of an absent key is a no-op" is FALSE here; the honest
-- form is observer-level (storage-derived observers only). With duplicate
-- keys expressible in an arbitrary `Bag`, "length - 1" is also false; the
-- characterization is eq-on-absent / le / strict-lt-on-present.
-- ---------------------------------------------------------------------------

-- (strict-decrease core consolidated into `ListFacts.length_filter_lt_of_any`
-- in `Prelude/Helpers.lean` by the lemma-wave landing.)

private theorem bag_remove_storage_eq_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [hvc : HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : _root_.Bag.Bag U) (k : K)
    (h_not_contains : _root_.Bag.contains K bag k = false) :
    (_root_.Bag.remove K V bag k).2.storage = bag.storage := by
  unfold _root_.Bag.contains at h_not_contains
  unfold _root_.Bag.remove
  show bag.storage.filter (fun e => !_root_.Bag.Entry.keyMatches e k) = bag.storage
  apply List.filter_eq_self.mpr
  intro e h_mem
  have h_false : _root_.Bag.Entry.keyMatches e k = false := by
    cases h_match : _root_.Bag.Entry.keyMatches e k
    · rfl
    · exfalso
      have h_any : bag.storage.any
          (fun e => _root_.Bag.Entry.keyMatches e k) = true :=
        List.any_eq_true.mpr ⟨e, h_mem, h_match⟩
      rw [h_any] at h_not_contains
      simp at h_not_contains
  simp [h_false]

theorem bag_length_remove_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : _root_.Bag.Bag U) (k : K)
    (h_not_contains : _root_.Bag.contains K bag k = false) :
    _root_.Bag.length (_root_.Bag.remove K V bag k).2 =
      _root_.Bag.length bag := by
  apply BoundedNat.ext
  show ((_root_.Bag.remove K V bag k).2.storage).length % (2^64) =
    bag.storage.length % (2^64)
  rw [bag_remove_storage_eq_of_not_contains bag k h_not_contains]

theorem bag_is_empty_remove_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : _root_.Bag.Bag U) (k : K)
    (h_not_contains : _root_.Bag.contains K bag k = false) :
    _root_.Bag.is_empty (_root_.Bag.remove K V bag k).2 =
      _root_.Bag.is_empty bag := by
  unfold _root_.Bag.is_empty
  rw [bag_remove_storage_eq_of_not_contains bag k h_not_contains]

theorem bag_length_remove_le
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : _root_.Bag.Bag U) (k : K) :
    (_root_.Bag.length (_root_.Bag.remove K V bag k).2).val ≤
      (_root_.Bag.length bag).val := by
  have h_bound := MoveVector.list_length_bounded (_root_.Bag.Entry U) bag.storage
  have h_le := List.length_filter_le
    (fun e : _root_.Bag.Entry U => !_root_.Bag.Entry.keyMatches e k) bag.storage
  unfold _root_.Bag.length _root_.Bag.remove
  show (bag.storage.filter _).length % (2^64) ≤ bag.storage.length % (2^64)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h_bound]
  exact h_le

theorem bag_length_remove_lt_of_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V]
    [DecidableEq K] [Inhabited V]
    (bag : _root_.Bag.Bag U) (k : K)
    (h_contains : _root_.Bag.contains K bag k = true) :
    (_root_.Bag.length (_root_.Bag.remove K V bag k).2).val <
      (_root_.Bag.length bag).val := by
  have h_bound := MoveVector.list_length_bounded (_root_.Bag.Entry U) bag.storage
  unfold _root_.Bag.contains at h_contains
  have h_lt := ListFacts.length_filter_lt_of_any bag.storage
    (fun e => _root_.Bag.Entry.keyMatches e k) h_contains
  unfold _root_.Bag.length _root_.Bag.remove
  show (bag.storage.filter _).length % (2^64) < bag.storage.length % (2^64)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h_bound]
  exact h_lt

-- ---------------------------------------------------------------------------
-- Pass 2: matrix-audit fills -- emptiness x writers, length x add/set
-- (absent-key guarded), and the borrow_mut writeback faces.
-- ---------------------------------------------------------------------------

/-- `add` and `set` both cons the packed entry, so the result is never
    empty. -/
@[simp] theorem bag_is_empty_add
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) (v : V) :
    _root_.Bag.is_empty (_root_.Bag.add K V bag k v) = false := rfl

@[simp] theorem bag_is_empty_set
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) (v : V) :
    _root_.Bag.is_empty (_root_.Bag.set K V bag k v) = false := rfl

/-- On an absent key `add` grows the derived length by exactly one (present
    keys are unreachable: `add` aborts there). At a PRESENT key the storage
    action drops every prior match first, so the clean equality needs the
    `keysUnique` invariant -- deferred to that battery. -/
theorem bag_length_add_val_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) (v : V)
    (h_not_contains : _root_.Bag.contains K bag k = false) :
    (_root_.Bag.length (_root_.Bag.add K V bag k v)).val =
      (_root_.Bag.length bag).val + 1 := by
  unfold _root_.Bag.contains at h_not_contains
  have h_filter : bag.storage.filter
      (fun e => !_root_.Bag.Entry.keyMatches e k) = bag.storage := by
    apply List.filter_eq_self.mpr
    intro e h_mem
    have h_false : _root_.Bag.Entry.keyMatches e k = false := by
      cases h_match : _root_.Bag.Entry.keyMatches e k
      · rfl
      · exfalso
        have h_any : bag.storage.any
            (fun e => _root_.Bag.Entry.keyMatches e k) = true :=
          List.any_eq_true.mpr ⟨e, h_mem, h_match⟩
        rw [h_any] at h_not_contains
        simp at h_not_contains
    simp [h_false]
  have h_bound := MoveVector.list_length_bounded_pred (_root_.Bag.Entry U) bag.storage
  unfold _root_.Bag.length _root_.Bag.add
  show (_ :: bag.storage.filter _).length % (2^64) =
    bag.storage.length % (2^64) + 1
  rw [List.length_cons, h_filter]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem bag_length_set_val_of_not_contains
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) (v : V)
    (h_not_contains : _root_.Bag.contains K bag k = false) :
    (_root_.Bag.length (_root_.Bag.set K V bag k v)).val =
      (_root_.Bag.length bag).val + 1 := by
  rw [bag_set_eq_add_of_not_contains bag k v h_not_contains]
  exact bag_length_add_val_of_not_contains bag k v h_not_contains

-- `borrow_mut` writeback faces: the Mutable's value IS the `borrow` read and
-- its reconstruct IS the `set` writeback; the bag itself rides unchanged.

@[simp] theorem bag_borrow_mut_snd
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : _root_.Bag.Bag U) (k : K) :
    (_root_.Bag.borrow_mut K V bag k).2 = bag := rfl

@[simp] theorem bag_borrow_mut_fst_val
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : _root_.Bag.Bag U) (k : K) :
    (_root_.Bag.borrow_mut K V bag k).1.val = _root_.Bag.borrow K V bag k := rfl

@[simp] theorem bag_borrow_mut_fst_reconstruct
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : _root_.Bag.Bag U) (k : K) (v : V) :
    (_root_.Bag.borrow_mut K V bag k).1.reconstruct v =
      _root_.Bag.set K V bag k v := rfl

/-- Cross-container mirror of `Table.length_lt_u64_max_pred` (see there). -/
theorem bag_length_lt_u64_max_pred
    {U : Type} [Universe U] (bag : _root_.Bag.Bag U)
    (m : BoundedNat (2^64)) (hm : m.val = 18446744073709551615) :
    BoundedNat.lt (_root_.Bag.length bag) m = true := by
  unfold _root_.Bag.length BoundedNat.lt
  have h := MoveVector.list_length_bounded_pred (_root_.Bag.Entry U) bag.storage
  apply nat_blt_eq_true
  rw [hm]
  show bag.storage.length % (2^64) < 18446744073709551615
  have hmod : bag.storage.length % (2^64) = bag.storage.length :=
    Nat.mod_eq_of_lt (by omega)
  omega

-- Pass 2 audit stragglers: the writers never touch the object identity
-- (`HasObjectId` reads `.id`), so the uid-token observers see through them.

@[simp] theorem bag_id_add
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) (v : V) :
    (_root_.Bag.add K V bag k v).id = bag.id := rfl

@[simp] theorem bag_id_set
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    (bag : _root_.Bag.Bag U) (k : K) (v : V) :
    (_root_.Bag.set K V bag k v).id = bag.id := rfl

@[simp] theorem bag_id_remove
    {U K V : Type} [Universe U] [HasCode U K] [HasCode U V] [DecidableEq K]
    [Inhabited V] (bag : _root_.Bag.Bag U) (k : K) :
    ((_root_.Bag.remove K V bag k).2).id = bag.id := rfl
