-- Native implementations for std::vector
-- These provide the short-named functions called by generated code

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.MoveAbort
import Prelude.ProgramState

namespace MoveVector

-- Core vector operations using Lean's List type
-- Move vectors are represented as List in Lean
--
-- After mutable threading: functions that took Mutable (List tv0) s
-- now take List tv0 directly and return the updated list alongside
-- any original return value.

def empty (tv0 : Type) [BEq tv0] [Inhabited tv0] : List tv0 :=
  []

/-- **Model assumption (Boogie parity).** A well-formed Move container's
length has strict headroom below `u64::MAX`: `length + 1 < 2^64`, i.e.
`length < 2^64 - 1`. This is the single trusted length bound; every other
container length fact below is DERIVED from it.

WHY an assumption and not a theorem: the Lean model represents a container's
backing as an unbounded `List`, so nothing in the type stops `List.length`
from reaching `2^64 - 1`. Real Move execution cannot: each element occupies a
distinct on-chain object / dynamic field, and a single transaction (the unit a
spec reasons about) allocates only boundedly many, so a container cannot be
driven to `u64::MAX` within one call. Boogie tracks the size as a real `u64`
that the transaction cannot saturate, so the `size + 1` overflow face of
`add`/`insert` is vacuous there. This axiom restores that parity: the strict
`+ 1` headroom makes every container `add`'s increment provably non-overflowing
and every `length() < u64::MAX` spec assert provably true (see
`Table.length_lt_u64_max_pred`), matching Boogie instead of leaving a
`length = 2^64 - 1` overflow witness the Lean side could never rule out.

Do NOT weaken this back to `length < 2^64`: that reintroduces the
`length = 2^64 - 1` add-overflow witness (the stale `activate_staking_pool`
analysis). Sibling containers (Table/Bag/ObjectBag/ObjectTable/TableVec/Vec_set)
do not restate their own length bound -- they either reuse this axiom directly
(Vec_set) or build `⟨list.length % 2^64, Nat.mod_lt⟩` (Table/Bag/...), and the
`% 2^64` is a no-op under this axiom (`length < 2^64`), so all stay consistent. -/
axiom list_length_bounded_pred (tv0 : Type) (v : List tv0) : v.length + 1 < 2^64

/-- Weaker corollary of `list_length_bounded_pred`: `length < 2^64`. Used to
build a `BoundedNat (2^64)` from a raw container length (and consumed as a plain
`< 2^64` bound elsewhere, e.g. `Prelude.Quantifiers`). Kept under its historical
name so existing call sites are unaffected. -/
theorem list_length_bounded (tv0 : Type) (v : List tv0) : v.length < 2^64 := by
  have h := list_length_bounded_pred tv0 v
  omega

def length (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) : BoundedNat (2^64) :=
  ⟨v.length, list_length_bounded tv0 v⟩

@[reducible] def borrow (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) : tv0 :=
  v.getD i.val default

@[reducible] def borrow_mut (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) : (Mutable tv0 (List tv0)) × List tv0 :=
  (Mutable.mk (v.getD i.val default) (fun val => v.set i.val val), v)

def push_back (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (e : tv0) : List tv0 :=
  v ++ [e]

def pop_back (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) : (tv0 × List tv0) :=
  (v.getD (v.length - 1) default, v.dropLast)

def swap (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) (j : BoundedNat (2^64)) : List tv0 :=
  let vi := v.getD i.val default
  let vj := v.getD j.val default
  (v.set i.val vj).set j.val vi

def reverse (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) : List tv0 :=
  v.reverse

def append (tv0 : Type) [BEq tv0] [Inhabited tv0] (lhs : List tv0) (other : List tv0) : List tv0 :=
  lhs ++ other

@[reducible] def is_empty (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) : Bool :=
  v.isEmpty

@[reducible] def contains (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (e : tv0) : Bool :=
  v.contains e

axiom findIdx_bounded (tv0 : Type) [BEq tv0] (v : List tv0) (e : tv0) (idx : Nat)
    (h : v.findIdx? (· == e) = some idx) : idx < 2^64

def index_of (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (e : tv0) : (Bool × BoundedNat (2^64)) :=
  match h : v.findIdx? (· == e) with
  | some idx => (true, ⟨idx, findIdx_bounded tv0 v e idx h⟩)
  | none => (false, 0)

def singleton (tv0 : Type) [BEq tv0] [Inhabited tv0] (e : tv0) : List tv0 :=
  [e]

def remove (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) : (tv0 × List tv0) :=
  let result := v.getD i.val default
  let newList := v.eraseIdx i.val
  (result, newList)

def destroy_empty (tv0 : Type) [BEq tv0] [Inhabited tv0] (_v : List tv0) : Unit :=
  ()

-- Abort predicates
def borrow.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) : Bool :=
  i.val ≥ v.length

def pop_back.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) : Bool :=
  (v.isEmpty = true)

def swap.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) (j : BoundedNat (2^64)) : Bool :=
  i.val ≥ v.length ∨ j.val ≥ v.length

def remove.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) : Bool :=
  i.val ≥ v.length

def destroy_empty.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) : Bool :=
  ¬(v.isEmpty = true)

def contains.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (_v : List tv0) (_e : tv0) : Bool :=
  False

def index_of.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (_v : List tv0) (_e : tv0) : Bool :=
  False

/-- `std::vector::insert<T>(v: &mut vector<T>, e: T, i: u64)`. Move
return is `()`; stage 3 augments to return the updated `List T`.
Aborts iff `i > length(v)`. -/
def insert (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (v : List tv0) (e : tv0) (i : BoundedNat (2^64)) : List tv0 :=
  v.take i.val ++ [e] ++ v.drop i.val

def insert.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (v : List tv0) (_e : tv0) (i : BoundedNat (2^64)) : Bool :=
  i.val > v.length

/-- `std::vector::swap_remove<T>(v: &mut vector<T>, i: u64): T`. Stage 3
augments the `&mut` return: caller destructures `(removed, new_list)`.
Aborts iff the vector is empty or `i >= length(v)`. -/
def swap_remove (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (v : List tv0) (i : BoundedNat (2^64)) : (tv0 × List tv0) :=
  let removed := v.getD i.val default
  let last := v.getD (v.length - 1) default
  let v_with_last_at_i := v.set i.val last
  (removed, v_with_last_at_i.dropLast)

def swap_remove.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (v : List tv0) (i : BoundedNat (2^64)) : Bool :=
  v.isEmpty = true ∨ i.val ≥ v.length

end MoveVector

theorem move_vector_index_of_no_abort
    (T : Type) [BEq T] [Inhabited T] (v : List T) (e : T) :
    _root_.MoveVector.index_of.aborts T v e = false := by
  simp [_root_.MoveVector.index_of.aborts]

theorem move_vector_contains_no_abort
    (T : Type) [BEq T] [Inhabited T] (v : List T) (e : T) :
    _root_.MoveVector.contains.aborts T v e = false := by
  simp [_root_.MoveVector.contains.aborts]

theorem move_vector_remove_zero_no_abort_of_nonempty
    (alpha : Type) [BEq alpha] [Inhabited alpha]
    (xs : List alpha)
    (h_nonempty : xs ≠ []) :
    _root_.MoveVector.remove.aborts alpha xs
      (0 : BoundedNat (2^64)) = false := by
  cases xs with
  | nil =>
      contradiction
  | cons _ _ =>
      have h_zero : (0 : BoundedNat (2^64)).val = 0 := by
        rfl
      simp [_root_.MoveVector.remove.aborts, h_zero]

theorem move_vector_remove_no_abort_of_lt_length
    (alpha : Type) [BEq alpha] [Inhabited alpha]
    (xs : List alpha)
    (index : BoundedNat (2^64))
    (h_lt :
      BoundedNat.lt index (_root_.MoveVector.length alpha xs) = true) :
    _root_.MoveVector.remove.aborts alpha xs index = false := by
  have h_lt_nat : index.val < xs.length := by
    unfold BoundedNat.lt at h_lt
    have h_lt_val := nat_lt_of_blt_eq_true h_lt
    simpa [_root_.MoveVector.length] using h_lt_val
  unfold _root_.MoveVector.remove.aborts
  exact decide_eq_false (Nat.not_le_of_gt h_lt_nat)

@[simp]
theorem move_vector_index_of_fst_eq_contains
    (α : Type) [BEq α] [LawfulBEq α] [Inhabited α]
    (xs : List α) (x : α) :
    (_root_.MoveVector.index_of α xs x).1 =
      _root_.MoveVector.contains α xs x := by
  unfold _root_.MoveVector.index_of _root_.MoveVector.contains
  rw [List.contains_eq_any_beq]
  have h_pred : (fun y : α => y == x) = (fun y : α => x == y) := by
    funext y
    by_cases h : y = x
    · subst h
      simp
    · have hyx : (y == x) = false := beq_false_of_ne h
      have hxy : (x == y) = false := beq_false_of_ne (Ne.symm h)
      simp [hyx, hxy]
  rw [← List.findIdx?_isSome (xs := xs) (p := fun y : α => x == y)]
  rw [← h_pred]
  split
  · rename_i idx h_find
    simp [h_find]
  · rename_i h_find
    simp [h_find]

@[simp]
theorem move_vector_remove_aborts_index_of_eq_false_of_contains
    (α : Type) [BEq α] [LawfulBEq α] [Inhabited α]
    (xs : List α) (x : α)
    (h_contains : _root_.MoveVector.contains α xs x = true) :
    _root_.MoveVector.remove.aborts α xs
      (_root_.MoveVector.index_of α xs x).2 = false := by
  unfold _root_.MoveVector.index_of _root_.MoveVector.remove.aborts
  split
  · rename_i idx h_find
    obtain ⟨h_lt, _h_val, _h_min⟩ :=
      (List.findIdx?_eq_some_iff_getElem.mp h_find)
    simpa using decide_eq_false (Nat.not_le_of_gt h_lt)
  · rename_i h_find
    have h_pred : (fun y : α => y == x) = (fun y : α => x == y) := by
      funext y
      by_cases h : y = x
      · subst h
        simp
      · have hyx : (y == x) = false := beq_false_of_ne h
        have hxy : (x == y) = false := beq_false_of_ne (Ne.symm h)
        simp [hyx, hxy]
    have h_any : xs.any (fun y : α => y == x) = true := by
      unfold _root_.MoveVector.contains at h_contains
      rw [List.contains_eq_any_beq] at h_contains
      simpa [h_pred] using h_contains
    have h_isSome :=
      List.findIdx?_isSome (xs := xs) (p := fun y : α => y == x)
    rw [h_find] at h_isSome
    simp [h_any] at h_isSome

@[simp]
theorem move_vector_contains_push_back_same
    (α : Type) [BEq α] [LawfulBEq α] [Inhabited α]
    (xs : List α) (x : α) :
    _root_.MoveVector.contains α (_root_.MoveVector.push_back α xs x) x = true := by
  unfold _root_.MoveVector.contains _root_.MoveVector.push_back
  rw [List.contains_eq_any_beq]
  simp

/-! ## Shared in-range index facts

The `idx < vector::length(v)` loop guard is the single most repeated
hypothesis in the corpora; these three lemmas are what every client then
re-derives from it. Namespaced per the standing rule in
`plans/lean-pipeline/shared-proof-infra.md`. -/

namespace MoveVectorFacts

theorem lt_length_iff {α : Type} [BEq α] [Inhabited α] (xs : List α)
    (idx : BoundedNat (2^64)) :
    BoundedNat.lt idx (_root_.MoveVector.length α xs) = true ↔
      idx.val < xs.length :=
  bn_lt_iff idx (_root_.MoveVector.length α xs)

theorem borrow_aborts_eq_false_of_lt_length {α : Type} [BEq α] [Inhabited α]
    (xs : List α) (idx : BoundedNat (2^64))
    (h : BoundedNat.lt idx (_root_.MoveVector.length α xs) = true) :
    _root_.MoveVector.borrow.aborts α xs idx = false := by
  have h_lt : idx.val < xs.length := (lt_length_iff xs idx).mp h
  simp [_root_.MoveVector.borrow.aborts, Nat.not_le_of_gt h_lt]

/-- The index bump inside a vector walk cannot overflow: the container-length
axiom leaves strict headroom below `u64::MAX`. -/
theorem add_one_aborts_eq_false_of_lt_length {α : Type} [BEq α] [Inhabited α]
    (xs : List α) (idx : BoundedNat (2^64))
    (h : BoundedNat.lt idx (_root_.MoveVector.length α xs) = true) :
    BoundedNat.add_aborts idx (1 : BoundedNat (2^64)) = false := by
  have h_lt : idx.val < xs.length := (lt_length_iff xs idx).mp h
  have h_len := _root_.MoveVector.list_length_bounded_pred α xs
  rw [bn_add_aborts_eq_false_iff, bn_one_val_u64]
  omega

theorem add_one_val_of_lt_length {α : Type} [BEq α] [Inhabited α]
    (xs : List α) (idx : BoundedNat (2^64))
    (h : BoundedNat.lt idx (_root_.MoveVector.length α xs) = true) :
    (BoundedNat.add idx (1 : BoundedNat (2^64))).val = idx.val + 1 := by
  rw [BoundedNatFacts.add_val_of_add_aborts_false idx (1 : BoundedNat (2^64))
    (add_one_aborts_eq_false_of_lt_length xs idx h), bn_one_val_u64]

end MoveVectorFacts
