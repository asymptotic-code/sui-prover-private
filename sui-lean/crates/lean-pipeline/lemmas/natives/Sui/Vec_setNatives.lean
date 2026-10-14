-- Native struct definitions for sui::vec_set

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.ProgramState
import MoveStdlib.MoveVector

namespace Vec_set

structure VecSet (tv0 : Type) where
  contents : List tv0
deriving DecidableEq
instance [Inhabited tv0] : Inhabited (VecSet tv0) where default := ⟨default⟩

-- `vec_set::empty<K>(): VecSet<K>`.
def empty (tv0 : Type) : VecSet tv0 :=
  { contents := [] }

-- `vec_set::singleton<K>(k: K): VecSet<K>`.
def singleton (tv0 : Type) (k : tv0) : VecSet tv0 :=
  { contents := [k] }

-- `vec_set::insert<K>(self: &mut VecSet<K>, k: K)` -- stage-3
-- augmented form: returns the new VecSet. APPEND at the tail (Move's
-- `push_back`, vec_set.move) so `into_keys`/`keys` preserve insertion
-- order -- do NOT prepend (mirrors the already-correct `Vec_map.insert`).
def insert (tv0 : Type) (self : VecSet tv0) (k : tv0) : VecSet tv0 :=
  { contents := self.contents ++ [k] }

def insert.aborts (tv0 : Type) [BEq tv0] (self : VecSet tv0) (k : tv0) : Bool :=
  self.contents.any (fun x => x == k)

-- `vec_set::insert_pure<K>(self: VecSet<K>, k: K): VecSet<K>` -- the
-- by-value spec model of `insert` (the prover's pure variant, declared
-- as a native). In Lean `insert` already returns the new VecSet, so the
-- two coincide.
def insert_pure (tv0 : Type) (self : VecSet tv0) (k : tv0) : VecSet tv0 :=
  { contents := self.contents ++ [k] }

-- `vec_set::remove<K>(self: &mut VecSet<K>, k: &K)` -- stage-3 augmented.
def remove (tv0 : Type) [BEq tv0] (self : VecSet tv0) (k : tv0) : VecSet tv0 :=
  { contents := self.contents.filter (fun x => !(x == k)) }

def remove.aborts (tv0 : Type) [BEq tv0] (self : VecSet tv0) (k : tv0) : Bool :=
  !(self.contents.any (fun x => x == k))

-- `vec_set::contains<K>(self: &VecSet<K>, k: &K): bool`.
def contains (tv0 : Type) [BEq tv0] (self : VecSet tv0) (k : tv0) : Bool :=
  self.contents.any (fun x => x == k)

-- `vec_set::size<K>(self: &VecSet<K>): u64`.
-- The actual element count. (Previously a `default`=0 stub, which made
-- `vec_set::size(s) == n` checks spuriously fail -- e.g. scallop
-- obligation_access lock_key_test / reward_key_test assert size==3.)
-- Use the same bounded-length axiom as `MoveVector.length`; real Move vectors
-- are bounded by the u64 length model, and using modulo would make insertion
-- postconditions wrap around at 2^64.
def size (tv0 : Type) (self : VecSet tv0) : BoundedNat (2^64) :=
  ⟨self.contents.length, MoveVector.list_length_bounded tv0 self.contents⟩

-- `vec_set::length<K>(self: &VecSet<K>): u64`. In the Sui framework
-- `length` and `size` are identical (both `self.contents.length()`),
-- and the renderer emits `Vec_set.length` for a `.length()` method
-- call, so the model must define it too (mirrors `size`).
def length (tv0 : Type) (self : VecSet tv0) : BoundedNat (2^64) :=
  ⟨self.contents.length, MoveVector.list_length_bounded tv0 self.contents⟩

-- `vec_set::is_empty<K>(self: &VecSet<K>): bool`.
def is_empty (tv0 : Type) (self : VecSet tv0) : Bool :=
  self.contents.isEmpty

-- `vec_set::into_keys<K>(self: VecSet<K>): vector<K>`.
def into_keys (tv0 : Type) (self : VecSet tv0) : List tv0 :=
  self.contents

-- `vec_set::keys<K>(self: &VecSet<K>): &vector<K>`.
def keys (tv0 : Type) (self : VecSet tv0) : List tv0 :=
  self.contents

-- `vec_set::from_keys<K>(keys: vector<K>): VecSet<K>`. PurePartial:
-- aborts on duplicate keys.
def from_keys (tv0 : Type) (keys : List tv0) : VecSet tv0 :=
  { contents := keys }

end Vec_set

-- ---------------------------------------------------------------------------
-- Observer x writer matrix for VecSet. The file previously carried no lemmas
-- at all. Observers: contains / size / length / is_empty / keys / into_keys;
-- writers: empty / singleton / insert (+ insert_pure) / remove / from_keys.
-- Attribute discipline: `@[simp]` on rfl-class / unconditional
-- one-directional frames; conditional lemmas are citation-only. (No
-- `move_effect` precedent in this file, so none is introduced.)
-- ---------------------------------------------------------------------------

namespace Vec_set

-- Abort-face bridges (`insert` aborts on a PRESENT key, `remove` on an
-- absent one -- both faces are literally the `contains` observer).

@[simp] theorem vec_set_insert_aborts_eq_contains
    (K : Type) [BEq K] (self : VecSet K) (k : K) :
    insert.aborts K self k = contains K self k := rfl

@[simp] theorem vec_set_remove_aborts_eq_not_contains
    (K : Type) [BEq K] (self : VecSet K) (k : K) :
    remove.aborts K self k = !contains K self k := rfl

-- `empty` / `singleton` / `from_keys` faces.

@[simp] theorem vec_set_contains_empty
    (K : Type) [BEq K] (k : K) :
    contains K (empty K) k = false := rfl

@[simp] theorem vec_set_size_empty (K : Type) :
    size K (empty K) = (0 : BoundedNat (2^64)) := rfl

@[simp] theorem vec_set_length_empty (K : Type) :
    length K (empty K) = (0 : BoundedNat (2^64)) := rfl

@[simp] theorem vec_set_is_empty_empty (K : Type) :
    is_empty K (empty K) = true := rfl

@[simp] theorem vec_set_keys_empty (K : Type) :
    keys K (empty K) = [] := rfl

@[simp] theorem vec_set_into_keys_empty (K : Type) :
    into_keys K (empty K) = [] := rfl

@[simp] theorem vec_set_insert_aborts_empty
    (K : Type) [BEq K] (k : K) :
    insert.aborts K (empty K) k = false := rfl

@[simp] theorem vec_set_remove_aborts_empty
    (K : Type) [BEq K] (k : K) :
    remove.aborts K (empty K) k = true := rfl

@[simp] theorem vec_set_contains_singleton
    (K : Type) [BEq K] (a k : K) :
    contains K (singleton K a) k = (a == k) := by
  simp [contains, singleton]

@[simp] theorem vec_set_size_singleton (K : Type) (a : K) :
    size K (singleton K a) = (1 : BoundedNat (2^64)) := rfl

@[simp] theorem vec_set_length_singleton (K : Type) (a : K) :
    length K (singleton K a) = (1 : BoundedNat (2^64)) := rfl

@[simp] theorem vec_set_is_empty_singleton (K : Type) (a : K) :
    is_empty K (singleton K a) = false := rfl

@[simp] theorem vec_set_keys_singleton (K : Type) (a : K) :
    keys K (singleton K a) = [a] := rfl

@[simp] theorem vec_set_keys_from_keys (K : Type) (ks : List K) :
    keys K (from_keys K ks) = ks := rfl

@[simp] theorem vec_set_into_keys_from_keys (K : Type) (ks : List K) :
    into_keys K (from_keys K ks) = ks := rfl

/-- `contains` over `from_keys` is list membership (Bool form). -/
theorem vec_set_contains_from_keys
    (K : Type) [BEq K] (ks : List K) (k : K) :
    contains K (from_keys K ks) k = ks.any (fun x => x == k) := rfl

-- The spec-only pure variant IS `insert`.

@[simp] theorem vec_set_insert_pure_eq_insert
    (K : Type) (self : VecSet K) (k : K) :
    insert_pure K self k = insert K self k := rfl

-- `insert` transports.

@[simp] theorem vec_set_contains_insert_self
    (K : Type) [BEq K] [LawfulBEq K] (self : VecSet K) (k : K) :
    contains K (insert K self k) k = true := by
  simp [contains, insert, List.any_append]

/-- Both branches at once (or-form). Citation-only: the RHS is not a smaller
    term. -/
theorem vec_set_contains_insert
    (K : Type) [BEq K] (self : VecSet K) (added k : K) :
    contains K (insert K self added) k =
      (contains K self k || (added == k)) := by
  simp [contains, insert, List.any_append]

theorem vec_set_contains_insert_ne
    (K : Type) [BEq K] [LawfulBEq K] (self : VecSet K) (added k : K)
    (h_ne : k ≠ added) :
    contains K (insert K self added) k = contains K self k := by
  have h_beq : (added == k) = false := by
    apply Bool.eq_false_iff.mpr
    intro h_true
    exact h_ne (LawfulBEq.eq_of_beq h_true).symm
  simp [contains, insert, List.any_append, h_beq]

@[simp] theorem vec_set_is_empty_insert
    (K : Type) (self : VecSet K) (k : K) :
    is_empty K (insert K self k) = false := by
  unfold is_empty insert
  cases self.contents <;> rfl

/-- `keys` after `insert`, in insertion order. Citation-only (the append on
    the right is not a smaller term). -/
theorem vec_set_keys_insert
    (K : Type) (self : VecSet K) (k : K) :
    keys K (insert K self k) = keys K self ++ [k] := rfl

/-- `size` after `insert` grows by exactly one (the model appends
    unconditionally; Move's `insert` aborts on a present key, so reachable
    uses always satisfy it). Citation-only. -/
theorem vec_set_size_insert
    (K : Type) (self : VecSet K) (k : K) :
    size K (insert K self k) = BoundedNat.add (size K self) (1 : BoundedNat (2^64)) := by
  have h_bound := MoveVector.list_length_bounded_pred K self.contents
  apply BoundedNat.ext
  show (self.contents ++ [k]).length = (BoundedNat.add (size K self) (1 : BoundedNat (2^64))).val
  rw [List.length_append]
  simp only [List.length_cons, List.length_nil]
  show self.contents.length + 1 =
    if h : 2^64 > 0 then
      ((size K self).val + (1 : BoundedNat (2^64)).val) % 2^64
    else 0
  rw [dif_pos (by decide)]
  show self.contents.length + 1 = (self.contents.length + 1) % 2^64
  rw [Nat.mod_eq_of_lt (by omega)]

-- `remove` transports.

@[simp] theorem vec_set_contains_remove_same
    (K : Type) [BEq K] (self : VecSet K) (k : K) :
    contains K (remove K self k) k = false := by
  unfold contains remove
  apply Bool.eq_false_iff.mpr
  intro h_any
  rcases List.any_eq_true.mp h_any with ⟨x, h_mem, h_match⟩
  have h_kept := (List.mem_filter.mp h_mem).2
  rw [h_match] at h_kept
  simp at h_kept

theorem vec_set_contains_remove_ne
    (K : Type) [BEq K] [LawfulBEq K] (self : VecSet K) (removed k : K)
    (h_ne : k ≠ removed) :
    contains K (remove K self removed) k = contains K self k := by
  unfold contains remove
  simp only
  rw [ListFacts.any_filter_not_of_disjoint]
  intro x h_removed
  apply Bool.eq_false_iff.mpr
  intro h_true
  exact h_ne ((LawfulBEq.eq_of_beq h_true).symm.trans
    (LawfulBEq.eq_of_beq h_removed))

/-- `keys` after `remove` is the filtered key list. Citation-only. -/
theorem vec_set_keys_remove
    (K : Type) [BEq K] (self : VecSet K) (k : K) :
    keys K (remove K self k) = (keys K self).filter (fun x => !(x == k)) := rfl

@[simp] theorem vec_set_is_empty_remove_of_singleton
    (K : Type) [BEq K] [LawfulBEq K] (a : K) :
    is_empty K (remove K (singleton K a) a) = true := by
  simp [is_empty, remove, singleton]

end Vec_set

-- ---------------------------------------------------------------------------
-- Pass 2: the size x remove row and the remove no-op transport. Same honesty
-- note as the siblings: `remove` filters every match, so with duplicate
-- elements (expressible in an arbitrary `VecSet`, unreachable via the
-- aborting `insert`) "size - 1" is false; supplied are eq-on-absent (here a
-- full struct no-op -- `VecSet` has no ghost size field) / le / strict-lt.
-- Both `size` and `length` head spellings are stated.
-- ---------------------------------------------------------------------------

namespace Vec_set

-- (strict-decrease core consolidated into `ListFacts.ListFacts.length_filter_lt_of_any`
-- in `Prelude/Helpers.lean` by the lemma-wave landing.)

/-- The two size observers are one definition twice; collapse the heads. -/
@[simp] theorem vec_set_length_eq_size
    (K : Type) (self : VecSet K) :
    length K self = size K self := rfl

/-- Removing an absent element is a full no-op (`VecSet` carries no ghost
    size field, so the struct-level statement is honest here). -/
theorem vec_set_remove_of_not_contains
    (K : Type) [BEq K] (self : VecSet K) (k : K)
    (h_not_contains : contains K self k = false) :
    remove K self k = self := by
  unfold contains at h_not_contains
  unfold remove
  have h_all : ∀ x ∈ self.contents, (!(x == k)) = true := by
    intro x h_mem
    have h_false : (x == k) = false := by
      cases h_match : (x == k)
      · rfl
      · exfalso
        have h_any : self.contents.any (fun x => x == k) = true :=
          List.any_eq_true.mpr ⟨x, h_mem, h_match⟩
        rw [h_any] at h_not_contains
        simp at h_not_contains
    simp [h_false]
  rw [List.filter_eq_self.mpr h_all]

theorem vec_set_size_remove_le
    (K : Type) [BEq K] (self : VecSet K) (k : K) :
    (size K (remove K self k)).val ≤ (size K self).val := by
  unfold size remove
  exact List.length_filter_le (fun x => !(x == k)) self.contents

theorem vec_set_size_remove_lt_of_contains
    (K : Type) [BEq K] (self : VecSet K) (k : K)
    (h_contains : contains K self k = true) :
    (size K (remove K self k)).val < (size K self).val := by
  unfold contains at h_contains
  unfold size remove
  exact ListFacts.length_filter_lt_of_any self.contents (fun x => x == k) h_contains

theorem vec_set_length_remove_le
    (K : Type) [BEq K] (self : VecSet K) (k : K) :
    (length K (remove K self k)).val ≤ (length K self).val :=
  vec_set_size_remove_le K self k

theorem vec_set_length_remove_lt_of_contains
    (K : Type) [BEq K] (self : VecSet K) (k : K)
    (h_contains : contains K self k = true) :
    (length K (remove K self k)).val < (length K self).val :=
  vec_set_size_remove_lt_of_contains K self k h_contains

/-- `length` twin of `vec_set_size_insert` (both head spellings). -/
theorem vec_set_length_insert
    (K : Type) (self : VecSet K) (k : K) :
    length K (insert K self k) =
      BoundedNat.add (length K self) (1 : BoundedNat (2^64)) :=
  vec_set_size_insert K self k

end Vec_set

-- Pass 2: keys/contains interplay.

namespace Vec_set

/-- `contains` is membership in `keys` (Bool form; `keys` IS the contents). -/
theorem vec_set_contains_eq_keys_any
    (K : Type) [BEq K] (self : VecSet K) (k : K) :
    contains K self k = (keys K self).any (fun x => x == k) := rfl

end Vec_set

-- ---------------------------------------------------------------------------
-- DATATYPE INVARIANT: element uniqueness.
--
-- `sui::vec_set::VecSet<K>` is a `vector<K>` with no structural guarantee of
-- distinctness. Uniqueness is enforced by the DEFINING MODULE's API (`insert`
-- aborts on a present key, `from_keys` aborts on duplicates) plus Move's field
-- encapsulation: `contents` is private, so only `sui::vec_set` can construct
-- or mutate a `VecSet`.
--
-- `Inv` names that invariant. Every statement below is a PROVEN theorem;
-- there is deliberately no `axiom Inv self`, because the model's structure
-- constructor is total and `Inv (VecSet.mk [k, k])` is decidably FALSE, so a
-- blanket well-formedness axiom would prove `False`. `Inv` is a HYPOTHESIS,
-- never an assumption of the model.
-- See plans/lean-pipeline/container-datatype-invariants.md.
--
-- ASYMMETRY WITH `Vec_map`. `Vec_map.insert` is modeled as an upsert (it
-- filters the key out before appending), so it preserves the invariant
-- unconditionally. `Vec_set.insert` APPENDS blindly -- faithful to
-- `vec_set.move`, which aborts instead of replacing -- so its preservation
-- theorem is conditioned on its own abort face. That side condition is
-- discharged on every reachable execution by the generated abort guard.
-- ---------------------------------------------------------------------------

namespace Vec_set

/-- The `VecSet` datatype invariant: elements are pairwise distinct. Stated at
the `keys` observer so client citations never mention `contents`. -/
def Inv (K : Type) (self : VecSet K) : Prop :=
  (keys K self).Nodup

theorem inv_iff_contents_nodup (K : Type) (self : VecSet K) :
    Inv K self ↔ self.contents.Nodup := Iff.rfl

private theorem filter_ne_length_succ_of_nodup {K : Type} [BEq K] [LawfulBEq K]
    (l : List K) (k : K)
    (h_nodup : l.Nodup)
    (h_any : l.any (fun x => x == k) = true) :
    (l.filter (fun x => !(x == k))).length + 1 = l.length := by
  induction l with
  | nil => simp at h_any
  | cons a rest ih =>
      rw [List.nodup_cons] at h_nodup
      by_cases h : (a == k) = true
      · have h_eq : a = k := LawfulBEq.eq_of_beq h
        have h_filter : rest.filter (fun x => !(x == k)) = rest := by
          apply List.filter_eq_self.mpr
          intro x h_mem
          have h_ne : x ≠ k := by
            intro h_x
            apply h_nodup.1
            rw [h_eq, ← h_x]
            exact h_mem
          simp [h_ne]
        rw [List.filter_cons_of_neg (by simp [h]), h_filter]
        simp
      · have hf : (a == k) = false := Bool.eq_false_iff.mpr h
        have h_any_rest : rest.any (fun x => x == k) = true := by
          rw [List.any_cons, hf, Bool.false_or] at h_any; exact h_any
        rw [List.filter_cons_of_pos (by simp [hf])]
        simp only [List.length_cons]
        rw [ih h_nodup.2 h_any_rest]

-- Establishment.

@[simp] theorem vec_set_inv_empty (K : Type) : Inv K (empty K) := by
  simp [Inv, keys, empty]

@[simp] theorem vec_set_inv_singleton (K : Type) (k : K) :
    Inv K (singleton K k) := by
  simp [Inv, keys, singleton]

/-- `from_keys` establishes the invariant exactly when its argument is already
duplicate-free -- which is what `vec_set::from_keys` aborts on. NOTE: that
abort face is currently UNMODELED (`vec_set::from_keys` is classified partial
but registers no `.aborts` companion), so this hypothesis is not discharged by
a generated guard. See the design doc's "remaining establishment gap". -/
theorem vec_set_inv_from_keys (K : Type) (ks : List K) (h : ks.Nodup) :
    Inv K (from_keys K ks) := h

-- Preservation, one theorem per writer in `sui::vec_set`.

/-- `insert` preserves the invariant on any non-aborting execution. The side
condition IS the generated abort face (`insert.aborts = contains`). -/
theorem vec_set_inv_insert_of_no_abort
    (K : Type) [BEq K] [LawfulBEq K]
    (self : VecSet K) (k : K)
    (h_inv : Inv K self)
    (h_no_abort : insert.aborts K self k = false) :
    Inv K (insert K self k) := by
  unfold Inv keys at h_inv ⊢
  unfold insert
  have h_not_mem : k ∉ self.contents := by
    intro h_mem
    rw [show insert.aborts K self k = self.contents.any (fun x => x == k) from rfl,
      List.any_eq_true.mpr ⟨k, h_mem, by simp⟩] at h_no_abort
    exact absurd h_no_abort (by decide)
  refine List.nodup_append.mpr ⟨h_inv, by simp, ?_⟩
  intro a h_a b h_b
  rw [List.eq_of_mem_singleton h_b]
  intro h_eq
  exact h_not_mem (h_eq ▸ h_a)

/-- The `contains` spelling of the same fact (the two faces are equal by
`vec_set_insert_aborts_eq_contains`). -/
theorem vec_set_inv_insert_of_not_contains
    (K : Type) [BEq K] [LawfulBEq K]
    (self : VecSet K) (k : K)
    (h_inv : Inv K self)
    (h_not_contains : contains K self k = false) :
    Inv K (insert K self k) :=
  vec_set_inv_insert_of_no_abort K self k h_inv h_not_contains

theorem vec_set_inv_insert_pure_of_not_contains
    (K : Type) [BEq K] [LawfulBEq K]
    (self : VecSet K) (k : K)
    (h_inv : Inv K self)
    (h_not_contains : contains K self k = false) :
    Inv K (insert_pure K self k) :=
  vec_set_inv_insert_of_no_abort K self k h_inv h_not_contains

/-- `remove` preserves the invariant unconditionally (a filter of the old
element list). -/
theorem vec_set_inv_remove
    (K : Type) [BEq K] (self : VecSet K) (k : K)
    (h_inv : Inv K self) :
    Inv K (remove K self k) := by
  unfold Inv keys at h_inv ⊢
  exact List.Nodup.sublist List.filter_sublist h_inv

-- The payoff: exact size arithmetic. WITHOUT `Inv` the model's `remove`
-- filters EVERY matching element, so only `≤` / `<` are available (see
-- `vec_set_size_remove_le` / `_lt_of_contains` above).

theorem vec_set_size_remove_val_eq_sub_one_of_contains
    (K : Type) [BEq K] [LawfulBEq K] (self : VecSet K) (k : K)
    (h_inv : Inv K self)
    (h_contains : contains K self k = true) :
    (size K (remove K self k)).val + 1 = (size K self).val :=
  filter_ne_length_succ_of_nodup self.contents k h_inv h_contains

theorem vec_set_length_remove_val_eq_sub_one_of_contains
    (K : Type) [BEq K] [LawfulBEq K] (self : VecSet K) (k : K)
    (h_inv : Inv K self)
    (h_contains : contains K self k = true) :
    (length K (remove K self k)).val + 1 = (length K self).val :=
  vec_set_size_remove_val_eq_sub_one_of_contains K self k h_inv h_contains

/-- `BoundedNat` head spelling. -/
theorem vec_set_size_remove_of_contains
    (K : Type) [BEq K] [LawfulBEq K] (self : VecSet K) (k : K)
    (h_inv : Inv K self)
    (h_contains : contains K self k = true) :
    size K (remove K self k)
      = BoundedNat.sub (size K self) (1 : BoundedNat (2^64)) := by
  have h_core :=
    vec_set_size_remove_val_eq_sub_one_of_contains K self k h_inv h_contains
  have h_one : (1 : BoundedNat (2^64)).val = 1 := rfl
  apply BoundedNat.ext
  show (size K (remove K self k)).val
    = (size K self).val - (1 : BoundedNat (2^64)).val
  rw [h_one]
  omega

end Vec_set
