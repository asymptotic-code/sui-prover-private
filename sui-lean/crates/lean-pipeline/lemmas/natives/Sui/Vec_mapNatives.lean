-- Native implementations for sui::vec_map.
--
-- Move source: `public struct VecMap<K, V> has copy, drop, store
-- { contents: vector<Entry<K, V>> }` where `Entry<K, V> { key: K,
-- value: V }`. Operations are linear-scan over `contents`. Aborts
-- companion stubs return `false`; real abort conditions (missing
-- key, duplicate insert, empty pop) live in the verification harness.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.ProgramState
import MoveStdlib.MoveVector
import MoveStdlib.MoveOption

namespace Vec_map

structure Entry (tv0 : Type) (tv1 : Type) where
  key : tv0
  value : tv1
deriving DecidableEq
instance [Inhabited tv0] [Inhabited tv1] : Inhabited (Entry tv0 tv1) where default := ⟨default, default⟩

structure VecMap (tv0 : Type) (tv1 : Type) where
  contents : List (Entry tv0 tv1)
deriving DecidableEq
instance [Inhabited tv0] [Inhabited tv1] : Inhabited (VecMap tv0 tv1) where default := ⟨default⟩

/-- `vec_map::empty<K, V>(): VecMap<K, V>`. -/
def empty (K V : Type) [Inhabited K] [Inhabited V] : VecMap K V := ⟨[]⟩

def empty.aborts (K V : Type) [Inhabited K] [Inhabited V] : Bool := false

/-- `vec_map::insert<K, V>(self: &mut VecMap<K, V>, key: K, value: V)`.
Move return is `()`; after stage 3 augmentation, returns the
augmented `VecMap`. -/
def insert (K V : Type) [BEq K] [Inhabited V] (self : VecMap K V) (key : K) (value : V) : VecMap K V :=
  -- Append at the tail so `contents` stays in Move's insertion order
  -- (index 0 = oldest). `keys`/`into_keys_values`/`get_entry_by_idx`
  -- read `contents` in natural order, and `pop` removes the tail, so
  -- they all depend on this orientation.
  { contents := self.contents.filter (fun e => !(e.key == key)) ++ [{ key := key, value := value }] }

def insert.aborts (K V : Type) [BEq K] [Inhabited V] (self : VecMap K V) (key : K) (_value : V) : Bool :=
  (self.contents.find? (fun e => e.key == key)).isSome

/-- `vec_map::get<K, V>(self: &VecMap<K, V>, key: &K): &V`. Aborts
when the key is missing; the stub returns the type default. -/
def get (K V : Type) [BEq K] [Inhabited V] (self : VecMap K V) (key : K) : V :=
  match self.contents.find? (fun e => e.key == key) with
  | some e => e.value
  | none   => default

def get.aborts (K V : Type) [BEq K] [Inhabited V] (self : VecMap K V) (key : K) : Bool :=
  (self.contents.find? (fun e => e.key == key)).isNone

/-- sui-prover fork extension: `#[spec_only] vec_map::get_or_unknown<K, V>(
m: &VecMap<K, V>, k: &K): &V` -- spec-only TOTAL lookup: the value at `k`
when contained, else "an uninterpreted but deterministic value". Modeled as
`get` (which already falls back to `default` on a missing key): exact for
present keys; the absent-key value is determinized to `default`. Specs must
not rely on the absent-key value (Boogie keeps it uninterpreted there). -/
def get_or_unknown (K V : Type) [BEq K] [Inhabited V] (self : VecMap K V) (key : K) : V :=
  get K V self key

def get_or_unknown.aborts (K V : Type) [BEq K] [Inhabited V] (_self : VecMap K V) (_key : K) : Bool := false

/-- **NOT a Move source function** -- a writeback primitive added so
the new-pipeline renderer can express `*vec_map::get_mut(t, k) = v`
without peeking into `VecMap`'s internal `contents : List Entry`
representation from the Rust side. Replaces the value at `k` with
`v` if present; no-op when `k` is missing. Same role as
`Table.set` / `TypedMap.set`. -/
def set (K V : Type) [BEq K] [Inhabited V] (self : VecMap K V) (key : K) (value : V) : VecMap K V :=
  { contents := self.contents.map (fun e => if e.key == key then { e with value := value } else e) }

/-- `vec_map::try_get<K, V>(self: &VecMap<K, V>, key: &K): Option<V>`.
`some(v)` when the key is present, `none` otherwise. Built from the
`MoveOption` STRUCTURE directly (`vec := [v]` / `vec := []`) rather than
the generated `MoveOption.some`/`none` defs -- those only exist when the
client's Move code references them, but the structure is always emitted
(same reasoning as `MoveStringNatives.try_utf8`). -/
def try_get (K V : Type) [BEq K] [Inhabited V] (self : VecMap K V) (key : K) : MoveOption.MoveOption V :=
  match self.contents.find? (fun e => e.key == key) with
  | some e => { vec := [e.value] }
  | none   => { vec := [] }

def try_get.aborts (K V : Type) [BEq K] [Inhabited V] (_self : VecMap K V) (_key : K) : Bool := false

/-- `vec_map::contains<K, V>(self: &VecMap<K, V>, key: &K): bool`. -/
def contains (K V : Type) [BEq K] [Inhabited V] (self : VecMap K V) (key : K) : Bool :=
  self.contents.any (fun e => e.key == key)

def contains.aborts (K V : Type) [BEq K] [Inhabited V] (_self : VecMap K V) (_key : K) : Bool := false

/-- `vec_map::remove<K, V>(self: &mut VecMap<K, V>, key: &K): (K, V)`.
Stage 3 augments the return: `((K, V), VecMap K V)`. -/
-- Move source: `public fun remove<K, V>(self: &mut VecMap<K,V>, key: &K): (K, V)`.
-- Stage 4 (effects) threads `self` as a pass-back, augmenting the
-- return shape to `(K, V, VecMap K V)`. Use a FLAT triple to match
-- the IR-side destructure -- callers do `let (k, v, self') := remove(...)`.
def remove (K V : Type) [BEq K] [Inhabited K] [Inhabited V] (self : VecMap K V) (key : K) : (K × V × VecMap K V) :=
  match self.contents.find? (fun e => e.key == key) with
  | some e => (e.key, e.value, { contents := self.contents.filter (fun e => !(e.key == key)) })
  | none   => (default, default, self)

def remove.aborts (K V : Type) [BEq K] [Inhabited K] [Inhabited V] (self : VecMap K V) (key : K) : Bool :=
  (self.contents.find? (fun e => e.key == key)).isNone

/-- `vec_map::keys<K, V>(self: &VecMap<K, V>): vector<K>`. -/
def keys (K V : Type) [Inhabited V] (self : VecMap K V) : List K :=
  self.contents.map (fun e => e.key)

def keys.aborts (K V : Type) [Inhabited V] (_self : VecMap K V) : Bool := false

/-- `vec_map::size<K, V>(self: &VecMap<K, V>): u64`. -/
def size (K V : Type) [Inhabited V] (self : VecMap K V) : BoundedNat (2^64) :=
  ⟨self.contents.length % (2^64), Nat.mod_lt _ (by decide)⟩

def size.aborts (K V : Type) [Inhabited V] (_self : VecMap K V) : Bool := false

/-- `vec_map::is_empty<K, V>(self: &VecMap<K, V>): bool`. -/
def is_empty (K V : Type) [Inhabited V] (self : VecMap K V) : Bool := self.contents.isEmpty

def is_empty.aborts (K V : Type) [Inhabited V] (_self : VecMap K V) : Bool := false

/-- `vec_map::length<K, V>(self: &VecMap<K, V>): u64`. Pure read on
the entry list, no `&mut`. -/
def length (K V : Type) [Inhabited V] (self : VecMap K V) : BoundedNat (2^64) :=
  ⟨self.contents.length % (2^64), Nat.mod_lt _ (by decide)⟩

def length.aborts (K V : Type) [Inhabited V] (_self : VecMap K V) : Bool := false

/-- `vec_map::pop<K, V>(self: &mut VecMap<K,V>): (K, V)`. Returns the
last `(key, value)` pair and removes it. Aborts when `self` is
empty. Stage 4 (effects) threads `self` as a pass-back, augmenting
the return shape to the flat triple `(K, V, VecMap K V)` (matching
the `remove` shape above so callers can do
`let (k, v, self') := pop(...)`). -/
def pop (K V : Type) [BEq K] [Inhabited K] [Inhabited V] (self : VecMap K V) : (K × V × VecMap K V) :=
  -- Move's `pop_back`: removes and returns the LAST (newest) entry,
  -- now at the tail since `insert` appends.
  match self.contents.getLast? with
  | some e => (e.key, e.value, { contents := self.contents.dropLast })
  | none   => (default, default, self)

def pop.aborts (K V : Type) [BEq K] [Inhabited K] [Inhabited V] (self : VecMap K V) : Bool :=
  self.contents.isEmpty

/-- `vec_map::destroy_empty<K, V>(self: VecMap<K, V>)`. Consumes
`self`; aborts iff the map is non-empty. Move return is `()` and
`self` is consumed by value (not `&mut`), so no stage-3 augmented
return -- just a literal Unit return. -/
def destroy_empty (K V : Type) [Inhabited V] (_self : VecMap K V) : Unit := ()

def destroy_empty.aborts (K V : Type) [Inhabited V] (self : VecMap K V) : Bool :=
  !self.contents.isEmpty

/-- `vec_map::into_keys_values<K, V>(self: VecMap<K, V>): (vector<K>, vector<V>)`.
Consumes the map and returns its keys and values as parallel
vectors in insertion order. -/
def into_keys_values (K V : Type) [Inhabited K] [Inhabited V] (self : VecMap K V)
    : (List K × List V) :=
  (self.contents.map (fun e => e.key), self.contents.map (fun e => e.value))

def into_keys_values.aborts (K V : Type) [Inhabited K] [Inhabited V] (_self : VecMap K V) : Bool := false

/-- `vec_map::get_entry_by_idx<K, V>(self: &VecMap<K, V>, idx: u64): (&K, &V)`.
Aborts when `idx >= length(self)`. -/
def get_entry_by_idx (K V : Type) [Inhabited K] [Inhabited V]
    (self : VecMap K V) (idx : BoundedNat (2^64)) : (K × V) :=
  let e := self.contents.getD idx.val default
  (e.key, e.value)

def get_entry_by_idx.aborts (K V : Type) [Inhabited K] [Inhabited V]
    (self : VecMap K V) (idx : BoundedNat (2^64)) : Bool :=
  idx.val ≥ self.contents.length

end Vec_map

-- ---------------------------------------------------------------------------
-- Observer x writer matrix for VecMap. The file previously carried no lemmas
-- at all; this section supplies the abort-face bridges, the `empty` faces,
-- and the same/distinct-key transports for `insert` / `set` / `remove`.
-- Attribute discipline: `@[simp]` on rfl-class / unconditional
-- one-directional frames; conditional lemmas are citation-only. (This file
-- carries no `move_effect` precedent, so none is introduced.)
-- ---------------------------------------------------------------------------

namespace Vec_map

private theorem find?_isSome_eq_any {K V : Type} [BEq K]
    (l : List (Entry K V)) (key : K) :
    (l.find? (fun e => e.key == key)).isSome =
      l.any (fun e => e.key == key) := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
      cases h : (e.key == key) with
      | true => simp [List.find?, h]
      | false => simp [List.find?, h, ih]

private theorem find?_isNone_eq_not_any {K V : Type} [BEq K]
    (l : List (Entry K V)) (key : K) :
    (l.find? (fun e => e.key == key)).isNone =
      !l.any (fun e => e.key == key) := by
  rw [← find?_isSome_eq_any]
  cases l.find? (fun e => e.key == key) <;> rfl

-- Abort-face bridges.

@[simp] theorem vec_map_insert_aborts_eq_contains
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V) :
    insert.aborts K V self key value = contains K V self key := by
  unfold insert.aborts contains
  exact find?_isSome_eq_any self.contents key

@[simp] theorem vec_map_get_aborts_eq_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) :
    get.aborts K V self key = !contains K V self key := by
  unfold get.aborts contains
  exact find?_isNone_eq_not_any self.contents key

@[simp] theorem vec_map_remove_aborts_eq_not_contains
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K) :
    remove.aborts K V self key = !contains K V self key := by
  unfold remove.aborts contains
  exact find?_isNone_eq_not_any self.contents key

@[simp] theorem vec_map_pop_aborts_eq_is_empty
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) :
    pop.aborts K V self = is_empty K V self := rfl

@[simp] theorem vec_map_destroy_empty_aborts_eq_not_is_empty
    (K V : Type) [Inhabited V] (self : VecMap K V) :
    destroy_empty.aborts K V self = !is_empty K V self := rfl

-- Total faces.

@[simp] theorem vec_map_empty_aborts_eq_false
    (K V : Type) [Inhabited K] [Inhabited V] :
    empty.aborts K V = false := rfl

@[simp] theorem vec_map_get_or_unknown_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V] (self : VecMap K V) (key : K) :
    get_or_unknown.aborts K V self key = false := rfl

@[simp] theorem vec_map_try_get_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V] (self : VecMap K V) (key : K) :
    try_get.aborts K V self key = false := rfl

@[simp] theorem vec_map_contains_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V] (self : VecMap K V) (key : K) :
    contains.aborts K V self key = false := rfl

@[simp] theorem vec_map_keys_aborts_eq_false
    (K V : Type) [Inhabited V] (self : VecMap K V) :
    keys.aborts K V self = false := rfl

@[simp] theorem vec_map_size_aborts_eq_false
    (K V : Type) [Inhabited V] (self : VecMap K V) :
    size.aborts K V self = false := rfl

@[simp] theorem vec_map_is_empty_aborts_eq_false
    (K V : Type) [Inhabited V] (self : VecMap K V) :
    is_empty.aborts K V self = false := rfl

@[simp] theorem vec_map_length_aborts_eq_false
    (K V : Type) [Inhabited V] (self : VecMap K V) :
    length.aborts K V self = false := rfl

@[simp] theorem vec_map_into_keys_values_aborts_eq_false
    (K V : Type) [Inhabited K] [Inhabited V] (self : VecMap K V) :
    into_keys_values.aborts K V self = false := rfl

-- Spec-alias transport.

@[simp] theorem vec_map_get_or_unknown_eq_get
    (K V : Type) [BEq K] [Inhabited V] (self : VecMap K V) (key : K) :
    get_or_unknown K V self key = get K V self key := rfl

-- `empty` faces.

@[simp] theorem vec_map_contains_empty
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V] (key : K) :
    contains K V (empty K V) key = false := rfl

@[simp] theorem vec_map_get_empty
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V] (key : K) :
    get K V (empty K V) key = default := rfl

@[simp] theorem vec_map_size_empty
    (K V : Type) [Inhabited K] [Inhabited V] :
    size K V (empty K V) = (0 : BoundedNat (2^64)) := rfl

@[simp] theorem vec_map_length_empty
    (K V : Type) [Inhabited K] [Inhabited V] :
    length K V (empty K V) = (0 : BoundedNat (2^64)) := rfl

@[simp] theorem vec_map_is_empty_empty
    (K V : Type) [Inhabited K] [Inhabited V] :
    is_empty K V (empty K V) = true := rfl

@[simp] theorem vec_map_keys_empty
    (K V : Type) [Inhabited K] [Inhabited V] :
    keys K V (empty K V) = [] := rfl

@[simp] theorem vec_map_get_aborts_empty
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V] (key : K) :
    get.aborts K V (empty K V) key = true := rfl

@[simp] theorem vec_map_insert_aborts_empty
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V] (key : K) (value : V) :
    insert.aborts K V (empty K V) key value = false := rfl

@[simp] theorem vec_map_remove_aborts_empty
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V] (key : K) :
    remove.aborts K V (empty K V) key = true := rfl

@[simp] theorem vec_map_pop_aborts_empty
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V] :
    pop.aborts K V (empty K V) = true := rfl

@[simp] theorem vec_map_destroy_empty_aborts_empty
    (K V : Type) [Inhabited K] [Inhabited V] :
    destroy_empty.aborts K V (empty K V) = false := rfl

-- `insert` transports. Note `insert` FILTERS the key out before appending,
-- so the same-key read is unconditional (unlike `Table.add`, which appends
-- blindly and needs the non-abort face as a side condition).

/-- At an ABSENT key the upsert filter `insert` applies is the identity: nothing
    is dropped. Exposed (rather than re-derived inline) because it is the shared
    core of every "fresh key" transport below -- `vec_map_set_of_not_contains`
    and `vec_map_size_insert_val_of_not_contains` both reduce to it. -/
theorem vec_map_contents_filter_eq_self_of_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K)
    (h_not_contains : contains K V self key = false) :
    self.contents.filter (fun e => !(e.key == key)) = self.contents := by
  unfold contains at h_not_contains
  apply List.filter_eq_self.mpr
  intro e h_mem
  have h_false : (e.key == key) = false := by
    cases h_match : (e.key == key) with
    | false => rfl
    | true =>
        rw [List.any_eq_true.mpr ⟨e, h_mem, h_match⟩] at h_not_contains
        exact absurd h_not_contains (by decide)
  simp [h_false]

private theorem find?_filter_append_same {K V : Type} [BEq K] [LawfulBEq K]
    (l : List (Entry K V)) (key : K) (value : V) :
    List.find? (fun e => e.key == key)
        (l.filter (fun e => !(e.key == key)) ++ [{ key := key, value := value }]) =
      some { key := key, value := value } := by
  induction l with
  | nil => simp [List.find?]
  | cons e rest ih =>
      by_cases h : (e.key == key) = true
      · simpa [List.filter_cons, h] using ih
      · have hf : (e.key == key) = false := Bool.eq_false_iff.mpr h
        simpa [List.filter_cons, hf, List.find?] using ih

private theorem find?_filter_append_ne {K V : Type} [BEq K] [LawfulBEq K]
    (l : List (Entry K V)) (added key : K) (entry : Entry K V)
    (h_ne : key ≠ added) (h_entry : entry.key = added) :
    List.find? (fun e => e.key == key)
        (l.filter (fun e => !(e.key == added)) ++ [entry]) =
      List.find? (fun e => e.key == key) l := by
  have h_entry_false : (entry.key == key) = false := by
    apply Bool.eq_false_iff.mpr
    intro h_true
    exact h_ne ((LawfulBEq.eq_of_beq h_true).symm.trans h_entry)
  induction l with
  | nil => simp [List.find?, h_entry_false]
  | cons e rest ih =>
      by_cases h : (e.key == added) = true
      · have h_e_key_false : (e.key == key) = false := by
          apply Bool.eq_false_iff.mpr
          intro h_true
          exact h_ne ((LawfulBEq.eq_of_beq h_true).symm.trans
            (LawfulBEq.eq_of_beq h))
        simpa [List.filter_cons, h, List.find?, h_e_key_false] using ih
      · have hf : (e.key == added) = false := Bool.eq_false_iff.mpr h
        by_cases hk : (e.key == key) = true
        · simp [List.filter_cons, hf, List.find?, hk]
        · have hkf : (e.key == key) = false := Bool.eq_false_iff.mpr hk
          simpa [List.filter_cons, hf, List.find?, hkf] using ih

@[simp] theorem vec_map_get_insert_same
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V) :
    get K V (insert K V self key value) key = value := by
  unfold get insert
  rw [find?_filter_append_same self.contents key value]

@[simp] theorem vec_map_contains_insert_same
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V) :
    contains K V (insert K V self key value) key = true := by
  unfold contains insert
  simp [List.any_append]

theorem vec_map_get_insert_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (self : VecMap K V) (added key : K) (value : V)
    (h_ne : key ≠ added) :
    get K V (insert K V self added value) key = get K V self key := by
  unfold get insert
  rw [find?_filter_append_ne self.contents added key _ h_ne rfl]

theorem vec_map_contains_insert_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (self : VecMap K V) (added key : K) (value : V)
    (h_ne : key ≠ added) :
    contains K V (insert K V self added value) key =
      contains K V self key := by
  unfold contains insert
  rw [List.any_append]
  have h_entry : (({ key := added, value := value } : Entry K V).key == key) =
      false := by
    apply Bool.eq_false_iff.mpr
    intro h_true
    exact h_ne (LawfulBEq.eq_of_beq h_true).symm
  simp only [List.any_cons, List.any_nil, h_entry, Bool.or_false]
  rw [ListFacts.any_filter_not_of_disjoint]
  intro e h_added
  apply Bool.eq_false_iff.mpr
  intro h_true
  exact h_ne ((LawfulBEq.eq_of_beq h_true).symm.trans
    (LawfulBEq.eq_of_beq h_added))

-- `set` (the `get_mut` writeback) transports.

private theorem set_find_same_of_contains {K V : Type} [BEq K] [LawfulBEq K]
    (l : List (Entry K V)) (key : K) (value : V)
    (h_contains : (l.find? (fun e => e.key == key)).isSome = true) :
    List.find? (fun e => e.key == key)
        (l.map (fun e => if e.key == key then { e with value := value } else e)) =
      some { key := key, value := value } := by
  induction l with
  | nil => simp at h_contains
  | cons e rest ih =>
      by_cases h : (e.key == key) = true
      · have h_eq : e.key = key := LawfulBEq.eq_of_beq h
        subst h_eq
        simp [List.find?]
      · have hf : (e.key == key) = false := Bool.eq_false_iff.mpr h
        rw [List.find?_cons_of_neg (by simp [hf])] at h_contains
        simpa [List.map, hf, List.find?] using ih h_contains

private theorem set_find_ne {K V : Type} [BEq K] [LawfulBEq K]
    (l : List (Entry K V)) (updated key : K) (value : V)
    (h_ne : key ≠ updated) :
    List.find? (fun e => e.key == key)
        (l.map (fun e => if e.key == updated then { e with value := value } else e)) =
      List.find? (fun e => e.key == key) l := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
      by_cases h : (e.key == updated) = true
      · have h_e_key_false : (e.key == key) = false := by
          apply Bool.eq_false_iff.mpr
          intro h_true
          exact h_ne ((LawfulBEq.eq_of_beq h_true).symm.trans
            (LawfulBEq.eq_of_beq h))
        simpa [List.map, h, List.find?, h_e_key_false] using ih
      · have hf : (e.key == updated) = false := Bool.eq_false_iff.mpr h
        by_cases hk : (e.key == key) = true
        · simp [List.map, hf, List.find?, hk]
        · have hkf : (e.key == key) = false := Bool.eq_false_iff.mpr hk
          simpa [List.map, hf, List.find?, hkf] using ih

theorem vec_map_get_set_same_of_contains
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V)
    (h_contains : contains K V self key = true) :
    get K V (set K V self key value) key = value := by
  unfold contains at h_contains
  unfold get set
  rw [set_find_same_of_contains self.contents key value
    (by rw [find?_isSome_eq_any]; exact h_contains)]

theorem vec_map_get_set_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (self : VecMap K V) (updated key : K) (value : V)
    (h_ne : key ≠ updated) :
    get K V (set K V self updated value) key = get K V self key := by
  unfold get set
  rw [set_find_ne self.contents updated key value h_ne]

/-- Setting at an ABSENT key is a no-op on the whole map: the rewrite map
    fires on no entry. Companion of `vec_map_remove_snd_of_not_contains`, and
    the transport every `set`-at-a-fresh-key observer face reduces to. -/
theorem vec_map_set_of_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V)
    (h_not_contains : contains K V self key = false) :
    set K V self key value = self := by
  have h_filter :=
    vec_map_contents_filter_eq_self_of_not_contains K V self key h_not_contains
  have h_id : ∀ e ∈ self.contents,
      (if e.key == key then { e with value := value } else e) = id e := by
    intro e h_mem
    have h_false : (e.key == key) = false := by
      simpa using List.filter_eq_self.mp h_filter e h_mem
    simp [h_false]
  unfold set
  rw [List.map_congr_left (g := id) h_id, List.map_id]

/-- The third face of the `get` x `set` matrix: at the SAME key, when that key
    is ABSENT, `set` leaves the read alone (both sides are the missing-key
    default). The other two faces are `vec_map_get_set_same_of_contains` and
    `vec_map_get_set_ne`. -/
theorem vec_map_get_set_same_of_not_contains
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V)
    (h_not_contains : contains K V self key = false) :
    get K V (set K V self key value) key = get K V self key := by
  rw [vec_map_set_of_not_contains K V self key value h_not_contains]

/-- `set` never changes the key list (each entry keeps its own key). -/
@[simp] theorem vec_map_keys_set
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V) :
    keys K V (set K V self key value) = keys K V self := by
  unfold keys set
  generalize self.contents = l
  induction l with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.map]
      rw [ih]
      by_cases h : (e.key == key) = true
      · simp [h]
      · simp [Bool.eq_false_iff.mpr h]

@[simp] theorem vec_map_size_set
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V) :
    size K V (set K V self key value) = size K V self := by
  apply BoundedNat.ext
  show (self.contents.map _).length % (2^64) = self.contents.length % (2^64)
  rw [List.length_map]

@[simp] theorem vec_map_length_set
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V) :
    length K V (set K V self key value) = length K V self := by
  apply BoundedNat.ext
  show (self.contents.map _).length % (2^64) = self.contents.length % (2^64)
  rw [List.length_map]

@[simp] theorem vec_map_is_empty_set
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V) :
    is_empty K V (set K V self key value) = is_empty K V self := by
  unfold is_empty set
  cases self.contents <;> rfl

/-- Presence is untouched by `set` at EVERY key (same or different). -/
theorem vec_map_contains_set
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (self : VecMap K V) (updated key : K) (value : V) :
    contains K V (set K V self updated value) key =
      contains K V self key := by
  unfold contains set
  generalize self.contents = l
  induction l with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.map, List.any_cons]
      rw [ih]
      by_cases h : (e.key == updated) = true
      · simp [h]
      · simp [Bool.eq_false_iff.mpr h]

-- `remove` transports.

@[simp] theorem vec_map_contains_remove_same
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K) :
    contains K V (remove K V self key).2.2 key = false := by
  unfold contains remove
  cases h_find : List.find? (fun e => e.key == key) self.contents with
  | none =>
      simp only []
      rw [← find?_isSome_eq_any, h_find]
      rfl
  | some e =>
      simp only []
      apply Bool.eq_false_iff.mpr
      intro h_any
      rcases List.any_eq_true.mp h_any with ⟨entry, h_mem, h_match⟩
      have h_kept := (List.mem_filter.mp h_mem).2
      rw [h_match] at h_kept
      simp at h_kept

theorem vec_map_contains_remove_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (removed key : K)
    (h_ne : key ≠ removed) :
    contains K V (remove K V self removed).2.2 key =
      contains K V self key := by
  unfold contains remove
  cases h_find : List.find? (fun e => e.key == removed) self.contents with
  | none => rfl
  | some e =>
      simp only []
      rw [ListFacts.any_filter_not_of_disjoint]
      intro entry h_removed
      apply Bool.eq_false_iff.mpr
      intro h_true
      exact h_ne ((LawfulBEq.eq_of_beq h_true).symm.trans
        (LawfulBEq.eq_of_beq h_removed))

theorem vec_map_get_remove_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (removed key : K)
    (h_ne : key ≠ removed) :
    get K V (remove K V self removed).2.2 key = get K V self key := by
  unfold get remove
  cases h_find : List.find? (fun e => e.key == removed) self.contents with
  | none => rfl
  | some e =>
      simp only []
      have h_frame :
          List.find? (fun e => e.key == key)
              (self.contents.filter (fun e => !(e.key == removed))) =
            List.find? (fun e => e.key == key) self.contents := by
        have h_pred :
            (fun e : Entry K V => !(e.key == removed)) =
              (fun e : Entry K V => !((fun e : Entry K V => e.key == removed) e)) :=
          rfl
        rw [h_pred, List.find?_filter]
        apply congrArg (fun p : Entry K V → Bool => List.find? p self.contents)
        funext e
        by_cases hk : (e.key == key) = true
        · have h_not_removed : (e.key == removed) = false := by
            apply Bool.eq_false_iff.mpr
            intro h_true
            exact h_ne ((LawfulBEq.eq_of_beq hk).symm.trans
              (LawfulBEq.eq_of_beq h_true))
          simp [hk, h_not_removed]
        · simp [Bool.eq_false_iff.mpr hk]
      rw [h_frame]

/-- `remove`'s value component IS the `get` read (same `find?`). -/
@[simp] theorem vec_map_remove_val_eq_get
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K) :
    (remove K V self key).2.1 = get K V self key := by
  unfold remove get
  cases h_find : List.find? (fun e => e.key == key) self.contents <;> rfl

/-- `remove`'s key component is the queried key whenever it was present. -/
theorem vec_map_remove_fst_eq_key_of_contains
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K)
    (h_contains : contains K V self key = true) :
    (remove K V self key).1 = key := by
  unfold contains at h_contains
  unfold remove
  cases h_find : List.find? (fun e => e.key == key) self.contents with
  | none =>
      rw [← find?_isSome_eq_any, h_find] at h_contains
      simp at h_contains
  | some e =>
      have h_match := List.find?_some h_find
      exact LawfulBEq.eq_of_beq h_match

end Vec_map

-- ---------------------------------------------------------------------------
-- Pass 2: size x insert/remove rows, remove no-op transport, pop and
-- get_entry_by_idx transports. Same honesty notes as the Table twin: the
-- model's `remove` filters every match, so with duplicate keys (expressible
-- in an arbitrary `VecMap`, unreachable via the aborting `insert`) the
-- "size - 1" equality is false; supplied instead are eq-on-absent / le /
-- strict-lt-on-present. Both `size` and `length` head spellings are stated
-- (the defs are separate but identical).
-- ---------------------------------------------------------------------------

namespace Vec_map

-- (strict-decrease core consolidated into `ListFacts.ListFacts.length_filter_lt_of_any`
-- in `Prelude/Helpers.lean` by the lemma-wave landing.)

/-- The two size observers are one definition twice; collapse the heads. -/
@[simp] theorem vec_map_length_eq_size
    (K V : Type) [Inhabited V] (self : VecMap K V) :
    length K V self = size K V self := rfl

/-- Removing an absent key is a no-op on the whole map. -/
theorem vec_map_remove_snd_of_not_contains
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K)
    (h_not_contains : contains K V self key = false) :
    (remove K V self key).2.2 = self := by
  unfold contains at h_not_contains
  unfold remove
  cases h_find : List.find? (fun e => e.key == key) self.contents with
  | some e =>
      rw [← find?_isSome_eq_any, h_find] at h_not_contains
      simp at h_not_contains
  | none => simp [h_find]

theorem vec_map_size_remove_le
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K) :
    (size K V (remove K V self key).2.2).val ≤ (size K V self).val := by
  have h_bound := MoveVector.list_length_bounded (Entry K V) self.contents
  unfold size remove
  cases h_find : List.find? (fun e => e.key == key) self.contents with
  | none => simp
  | some e =>
      have h_le := List.length_filter_le
        (fun e : Entry K V => !(e.key == key)) self.contents
      simp only [h_find]
      show (self.contents.filter _).length % (2^64) ≤
        self.contents.length % (2^64)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h_bound]
      exact h_le

theorem vec_map_size_remove_lt_of_contains
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K)
    (h_contains : contains K V self key = true) :
    (size K V (remove K V self key).2.2).val < (size K V self).val := by
  have h_bound := MoveVector.list_length_bounded (Entry K V) self.contents
  unfold contains at h_contains
  unfold size remove
  cases h_find : List.find? (fun e => e.key == key) self.contents with
  | none =>
      rw [← find?_isSome_eq_any, h_find] at h_contains
      simp at h_contains
  | some e =>
      have h_lt := ListFacts.length_filter_lt_of_any self.contents
        (fun e => e.key == key) h_contains
      simp only [h_find]
      show (self.contents.filter _).length % (2^64) <
        self.contents.length % (2^64)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h_bound]
      exact h_lt

theorem vec_map_length_remove_le
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K) :
    (length K V (remove K V self key).2.2).val ≤ (length K V self).val :=
  vec_map_size_remove_le K V self key

theorem vec_map_length_remove_lt_of_contains
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K)
    (h_contains : contains K V self key = true) :
    (length K V (remove K V self key).2.2).val < (length K V self).val :=
  vec_map_size_remove_lt_of_contains K V self key h_contains

/-- `insert` on an absent key grows the size by exactly one (on a present
    key the model first drops the old entry, and Move's `insert` aborts, so
    the guarded form is the honest one). -/
theorem vec_map_size_insert_val_of_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V)
    (h_not_contains : contains K V self key = false) :
    (size K V (insert K V self key value)).val = (size K V self).val + 1 := by
  have h_filter :=
    vec_map_contents_filter_eq_self_of_not_contains K V self key h_not_contains
  have h_bound := MoveVector.list_length_bounded_pred (Entry K V) self.contents
  unfold size insert
  show (self.contents.filter _ ++ [_]).length % (2^64) =
    self.contents.length % (2^64) + 1
  rw [h_filter, List.length_append]
  simp only [List.length_cons, List.length_nil]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem vec_map_length_insert_val_of_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V)
    (h_not_contains : contains K V self key = false) :
    (length K V (insert K V self key value)).val =
      (length K V self).val + 1 :=
  vec_map_size_insert_val_of_not_contains K V self key value h_not_contains

/-- `BoundedNat`-level head spelling of the two `_val` rows above: the shape a
    generated `size(self) + 1` comparison actually carries, so a client rewrites
    with this one and never has to descend to `.val`. The `+ 1` cannot wrap --
    `MoveVector.list_length_bounded_pred` leaves headroom below `u64::MAX`. -/
theorem vec_map_size_insert_of_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V)
    (h_not_contains : contains K V self key = false) :
    size K V (insert K V self key value)
      = BoundedNat.add (size K V self) (1 : BoundedNat (2^64)) := by
  have h_bound := MoveVector.list_length_bounded_pred (Entry K V) self.contents
  have h_self : (size K V self).val = self.contents.length :=
    Nat.mod_eq_of_lt (by omega)
  have h_one : (1 : BoundedNat (2^64)).val = 1 := rfl
  apply BoundedNat.ext
  rw [vec_map_size_insert_val_of_not_contains K V self key value h_not_contains]
  unfold BoundedNat.add
  simp only [gt_iff_lt, Nat.zero_lt_two, Nat.pow_pos, dif_pos, h_one, h_self]
  omega

theorem vec_map_length_insert_of_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V)
    (h_not_contains : contains K V self key = false) :
    length K V (insert K V self key value)
      = BoundedNat.add (length K V self) (1 : BoundedNat (2^64)) :=
  vec_map_size_insert_of_not_contains K V self key value h_not_contains

-- `pop` transports (getLast?/dropLast faces).

theorem vec_map_pop_of_is_empty
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V)
    (h_empty : is_empty K V self = true) :
    pop K V self = (default, default, self) := by
  unfold is_empty at h_empty
  have h_nil : self.contents = [] := List.isEmpty_iff.mp h_empty
  unfold pop
  rw [h_nil]
  rfl

theorem vec_map_pop_fst_insert
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V) :
    (pop K V (insert K V self key value)).1 = key := by
  unfold pop insert
  rw [List.getLast?_concat]

theorem vec_map_pop_val_insert
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V) :
    (pop K V (insert K V self key value)).2.1 = value := by
  unfold pop insert
  rw [List.getLast?_concat]

@[simp] theorem vec_map_pop_aborts_insert
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V) :
    pop.aborts K V (insert K V self key value) = false := by
  unfold pop.aborts insert
  generalize self.contents.filter _ = l
  cases l <;> simp

theorem vec_map_size_pop_val_of_not_is_empty
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V)
    (h_not_empty : is_empty K V self = false) :
    (size K V (pop K V self).2.2).val = (size K V self).val - 1 := by
  have h_bound := MoveVector.list_length_bounded (Entry K V) self.contents
  unfold is_empty at h_not_empty
  unfold size pop
  cases h_last : self.contents.getLast? with
  | none =>
      have h_nil : self.contents = [] := List.getLast?_eq_none_iff.mp h_last
      rw [h_nil] at h_not_empty
      simp at h_not_empty
  | some e =>
      simp only [h_last]
      show self.contents.dropLast.length % (2^64) =
        self.contents.length % (2^64) - 1
      rw [List.length_dropLast]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h_bound]

theorem vec_map_length_pop_val_of_not_is_empty
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V)
    (h_not_empty : is_empty K V self = false) :
    (length K V (pop K V self).2.2).val = (length K V self).val - 1 :=
  vec_map_size_pop_val_of_not_is_empty K V self h_not_empty

-- `get_entry_by_idx` transports.

@[simp] theorem vec_map_get_entry_by_idx_aborts_empty
    (K V : Type) [Inhabited K] [Inhabited V] (idx : BoundedNat (2^64)) :
    get_entry_by_idx.aborts K V (empty K V) idx = true := by
  unfold get_entry_by_idx.aborts empty
  simp

/-- The abort face at the real observer head: out-of-range iff NOT
    `idx < size`. -/
theorem vec_map_get_entry_by_idx_aborts_eq_not_lt_size
    (K V : Type) [Inhabited K] [Inhabited V]
    (self : VecMap K V) (idx : BoundedNat (2^64)) :
    get_entry_by_idx.aborts K V self idx =
      !BoundedNat.lt idx (size K V self) := by
  have h_bound := MoveVector.list_length_bounded (Entry K V) self.contents
  unfold get_entry_by_idx.aborts size
  apply Bool.eq_iff_iff.mpr
  simp [BoundedNat.lt, Nat.mod_eq_of_lt h_bound, ge_iff_le,
    Bool.eq_false_iff, Nat.blt_eq, Nat.not_lt]

theorem vec_map_get_entry_by_idx_fst_of_lt
    (K V : Type) [Inhabited K] [Inhabited V]
    (self : VecMap K V) (idx : BoundedNat (2^64))
    (h_lt : BoundedNat.lt idx (size K V self) = true) :
    (get_entry_by_idx K V self idx).1 =
      (keys K V self).getD idx.val default := by
  have h_bound := MoveVector.list_length_bounded (Entry K V) self.contents
  have h_idx : idx.val < self.contents.length := by
    simp only [size, BoundedNat.lt] at h_lt
    rw [Nat.blt_eq, Nat.mod_eq_of_lt h_bound] at h_lt
    exact h_lt
  unfold get_entry_by_idx keys
  rw [ListFacts.getD_map_of_lt (fun e : Entry K V => e.key)
    self.contents idx.val h_idx]

theorem vec_map_get_entry_by_idx_snd_of_lt
    (K V : Type) [Inhabited K] [Inhabited V]
    (self : VecMap K V) (idx : BoundedNat (2^64))
    (h_lt : BoundedNat.lt idx (size K V self) = true) :
    (get_entry_by_idx K V self idx).2 =
      ((into_keys_values K V self).2).getD idx.val default := by
  have h_bound := MoveVector.list_length_bounded (Entry K V) self.contents
  have h_idx : idx.val < self.contents.length := by
    simp only [size, BoundedNat.lt] at h_lt
    rw [Nat.blt_eq, Nat.mod_eq_of_lt h_bound] at h_lt
    exact h_lt
  unfold get_entry_by_idx into_keys_values
  rw [ListFacts.getD_map_of_lt (fun e : Entry K V => e.value)
    self.contents idx.val h_idx]

end Vec_map

-- Pass 2: matrix-audit fills -- emptiness x insert, keys/contains interplay.

namespace Vec_map

@[simp] theorem vec_map_is_empty_insert
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V) :
    is_empty K V (insert K V self key value) = false := by
  unfold is_empty insert
  generalize self.contents.filter _ = l
  cases l <;> rfl

/-- `contains` is membership in `keys` (Bool form). -/
theorem vec_map_contains_eq_keys_any
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) :
    contains K V self key = (keys K V self).any (fun x => x == key) := by
  unfold contains keys
  rw [List.any_map]
  rfl

/-- `keys` after `insert`, in insertion order. Citation-only. -/
theorem vec_map_keys_insert
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V) :
    keys K V (insert K V self key value) =
      (keys K V self).filter (fun x => !(x == key)) ++ [key] := by
  unfold keys insert
  rw [List.map_append, List.filter_map]
  rfl

/-- `keys` after `remove` is the filtered key list (both branches: the
    absent branch is the identity, and so is the filter there). -/
theorem vec_map_keys_remove
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K) :
    keys K V (remove K V self key).2.2 =
      (keys K V self).filter (fun x => !(x == key)) := by
  unfold keys remove
  cases h_find : List.find? (fun e => e.key == key) self.contents with
  | some e =>
      simp only [h_find]
      rw [List.filter_map]
      rfl
  | none =>
      simp only [h_find]
      have h_all : ∀ x ∈ self.contents.map (fun e => e.key),
          (!(x == key)) = true := by
        intro x h_mem
        rcases List.mem_map.mp h_mem with ⟨e, h_e_mem, rfl⟩
        have h_false := List.find?_eq_none.mp h_find e h_e_mem
        simp only [Bool.not_eq_true'] at h_false ⊢
        simp [Bool.eq_false_iff.mpr h_false]
      exact (List.filter_eq_self.mpr h_all).symm

end Vec_map

-- Pass 2 audit stragglers: the try_get and into_keys_values observers,
-- bridged once to get/contains/keys so every writer transport carries over.

namespace Vec_map

/-- `try_get`'s payload, characterized against `contains` / `get`. If-form,
    so citation-only. -/
theorem vec_map_try_get_vec
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) :
    (try_get K V self key).vec =
      if contains K V self key then [get K V self key] else [] := by
  unfold try_get get contains
  cases h_find : List.find? (fun e => e.key == key) self.contents with
  | some e =>
      have h_any : self.contents.any (fun e => e.key == key) = true := by
        rw [← find?_isSome_eq_any, h_find]
        rfl
      simp [h_any]
  | none =>
      have h_any : self.contents.any (fun e => e.key == key) = false := by
        rw [← find?_isSome_eq_any, h_find]
        rfl
      simp [h_any]

/-- `into_keys_values`'s key column IS `keys`; every `keys` transport
    carries over. -/
@[simp] theorem vec_map_into_keys_values_fst_eq_keys
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V] (self : VecMap K V) :
    (into_keys_values K V self).1 = keys K V self := rfl

end Vec_map

-- ---------------------------------------------------------------------------
-- DATATYPE INVARIANT: key uniqueness.
--
-- `sui::vec_map::VecMap<K, V>` is a `vector<Entry<K, V>>` with NO structural
-- guarantee of key distinctness -- exactly as in Boogie, whose
-- `$IsValid'..VecMap..'` is element-wise validity over the same entry vector.
-- Uniqueness is enforced by the DEFINING MODULE's API (`insert` aborts on a
-- present key, `remove` deletes the single entry at `get_idx`) plus Move's
-- field encapsulation: `contents` is private, so only `sui::vec_map` can
-- construct or mutate a `VecMap`.
--
-- `Inv` names that invariant, and the block below discharges it for every
-- writer in the module. Every statement here is a PROVEN theorem -- there is
-- deliberately no `axiom Inv self`, because the model's structure constructor
-- is total: `Vec_map.Inv (VecMap.mk [(k,v), (k,v)])` unfolds to a decidably
-- FALSE `Nodup`, so a blanket "every VecMap is well-formed" axiom would prove
-- `False`. `Inv` is a HYPOTHESIS, never an assumption of the model.
-- See plans/lean-pipeline/container-datatype-invariants.md.
-- ---------------------------------------------------------------------------

namespace Vec_map

/-- The `VecMap` datatype invariant: entry keys are pairwise distinct.
Stated at the `keys` observer so client citations never mention `contents`. -/
def Inv (K V : Type) [Inhabited V] (self : VecMap K V) : Prop :=
  (keys K V self).Nodup

theorem inv_iff_contents_keys_nodup
    (K V : Type) [Inhabited V] (self : VecMap K V) :
    Inv K V self ↔ (self.contents.map (fun e => e.key)).Nodup := Iff.rfl

-- Entry-list core lemmas. Stated over a bare `List (Entry K V)` so the
-- `insert`/`remove`/`pop` preservation proofs share one induction each.

private theorem filter_ne_eq_self_of_not_mem_keys {K V : Type} [BEq K] [LawfulBEq K]
    (l : List (Entry K V)) (k : K) (h : k ∉ l.map (fun e => e.key)) :
    l.filter (fun e => !(e.key == k)) = l := by
  apply List.filter_eq_self.mpr
  intro e h_mem
  have h_ne : e.key ≠ k := by
    intro h_eq
    exact h (List.mem_map.mpr ⟨e, h_mem, h_eq⟩)
  simp [h_ne]

private theorem keys_filter_ne {K V : Type} [BEq K]
    (l : List (Entry K V)) (k : K) :
    (l.filter (fun e => !(e.key == k))).map (fun e => e.key) =
      (l.map (fun e => e.key)).filter (fun x => !(x == k)) := by
  rw [List.filter_map]
  rfl

/-- The one-entry-per-key counting fact: with distinct keys, deleting every
entry whose key matches a PRESENT key deletes exactly one entry. This is the
core the exact size-decrease payoff rests on. -/
private theorem filter_ne_length_succ_of_nodup {K V : Type} [BEq K] [LawfulBEq K]
    (l : List (Entry K V)) (k : K)
    (h_nodup : (l.map (fun e => e.key)).Nodup)
    (h_any : l.any (fun e => e.key == k) = true) :
    (l.filter (fun e => !(e.key == k))).length + 1 = l.length := by
  induction l with
  | nil => simp at h_any
  | cons e rest ih =>
      rw [List.map_cons, List.nodup_cons] at h_nodup
      by_cases h : (e.key == k) = true
      · have h_eq : e.key = k := LawfulBEq.eq_of_beq h
        have h_not_mem : k ∉ rest.map (fun e => e.key) := by
          rw [← h_eq]; exact h_nodup.1
        rw [List.filter_cons_of_neg (by simp [h]),
          filter_ne_eq_self_of_not_mem_keys rest k h_not_mem]
        simp
      · have hf : (e.key == k) = false := Bool.eq_false_iff.mpr h
        have h_any_rest : rest.any (fun e => e.key == k) = true := by
          rw [List.any_cons, hf, Bool.false_or] at h_any; exact h_any
        rw [List.filter_cons_of_pos (by simp [hf])]
        simp only [List.length_cons]
        rw [ih h_nodup.2 h_any_rest]

-- Establishment.

@[simp] theorem vec_map_inv_empty (K V : Type) [Inhabited K] [Inhabited V] :
    Inv K V (empty K V) := by
  simp [Inv, keys, empty]

-- Preservation, one theorem per writer in `sui::vec_map`.

/-- `insert` preserves the invariant UNCONDITIONALLY: the model filters the
key out before appending, so the result is duplicate-free whenever the input
is -- no appeal to `insert.aborts` is needed. (Move's `insert` does abort on a
present key; the model is the abort-free upsert, and both agree on every
non-aborting execution.) -/
theorem vec_map_inv_insert
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V)
    (h_inv : Inv K V self) :
    Inv K V (insert K V self key value) := by
  unfold Inv keys at h_inv
  unfold Inv keys insert
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [keys_filter_ne]
  refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
  · exact List.Nodup.sublist List.filter_sublist h_inv
  · simp
  · intro a h_mem_filter b h_mem_single
    have h_pred : (!(a == key)) = true := (List.mem_filter.mp h_mem_filter).2
    have h_a_ne : a ≠ key := by simpa using h_pred
    rw [List.eq_of_mem_singleton h_mem_single]
    exact h_a_ne

/-- `set` (the `get_mut` writeback) preserves the invariant: it rewrites
values only, leaving `keys` pointwise unchanged. -/
theorem vec_map_inv_set
    (K V : Type) [BEq K] [Inhabited V]
    (self : VecMap K V) (key : K) (value : V)
    (h_inv : Inv K V self) :
    Inv K V (set K V self key value) := by
  unfold Inv at h_inv ⊢
  rw [vec_map_keys_set]
  exact h_inv

/-- `remove` preserves the invariant (its key list is a filter of the old). -/
theorem vec_map_inv_remove
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K)
    (h_inv : Inv K V self) :
    Inv K V (remove K V self key).2.2 := by
  unfold Inv at h_inv ⊢
  rw [vec_map_keys_remove]
  exact List.Nodup.sublist List.filter_sublist h_inv

/-- `pop` preserves the invariant (its key list is a prefix of the old). -/
theorem vec_map_inv_pop
    (K V : Type) [BEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V)
    (h_inv : Inv K V self) :
    Inv K V (pop K V self).2.2 := by
  unfold Inv keys at h_inv
  unfold Inv keys pop
  cases h_last : self.contents.getLast? with
  | none => simpa [h_last] using h_inv
  | some e =>
      simp only [h_last]
      rw [List.map_dropLast]
      exact List.Nodup.sublist (List.dropLast_sublist _) h_inv

-- The payoff: exact size arithmetic. WITHOUT `Inv` the model's `remove`
-- filters EVERY matching entry, so only `≤` / `<` are available (see
-- `vec_map_size_remove_le` / `_lt_of_contains` above). WITH it, removing a
-- present key drops the size by exactly one -- which is what a client's
-- hand-rolled `*_key_is_unique` spec helper was encoding pointwise.

theorem vec_map_size_remove_val_eq_sub_one_of_contains
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K)
    (h_inv : Inv K V self)
    (h_contains : contains K V self key = true) :
    (size K V (remove K V self key).2.2).val + 1 = (size K V self).val := by
  have h_bound := MoveVector.list_length_bounded (Entry K V) self.contents
  have h_any : self.contents.any (fun e => e.key == key) = true := h_contains
  have h_core := filter_ne_length_succ_of_nodup self.contents key h_inv h_any
  have h_le := List.length_filter_le (fun e : Entry K V => !(e.key == key)) self.contents
  unfold size remove
  cases h_find : List.find? (fun e => e.key == key) self.contents with
  | none =>
      rw [← find?_isSome_eq_any, h_find] at h_any
      simp at h_any
  | some e =>
      simp only [h_find]
      show (self.contents.filter _).length % (2^64) + 1 =
        self.contents.length % (2^64)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h_bound]
      exact h_core

theorem vec_map_length_remove_val_eq_sub_one_of_contains
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K)
    (h_inv : Inv K V self)
    (h_contains : contains K V self key = true) :
    (length K V (remove K V self key).2.2).val + 1 = (length K V self).val :=
  vec_map_size_remove_val_eq_sub_one_of_contains K V self key h_inv h_contains

/-- `BoundedNat` head spelling -- the shape a generated `size(m) - 1`
comparison actually carries, so a client rewrites with this one and never
descends to `.val`. -/
theorem vec_map_size_remove_of_contains
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited K] [Inhabited V]
    (self : VecMap K V) (key : K)
    (h_inv : Inv K V self)
    (h_contains : contains K V self key = true) :
    size K V (remove K V self key).2.2
      = BoundedNat.sub (size K V self) (1 : BoundedNat (2^64)) := by
  have h_core :=
    vec_map_size_remove_val_eq_sub_one_of_contains K V self key h_inv h_contains
  have h_one : (1 : BoundedNat (2^64)).val = 1 := rfl
  apply BoundedNat.ext
  show (size K V (remove K V self key).2.2).val =
    (size K V self).val - (1 : BoundedNat (2^64)).val
  rw [h_one]
  omega

end Vec_map
