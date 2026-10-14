-- TypedMap operations for per-struct dynamic fields.
-- Dynamic fields on container structs (Table, LinkedTable, SkipList) are stored
-- as typed List (K × V) directly in each struct.
-- These helper functions operate on the list representation.

import Prelude.Helpers
import Prelude.MoveAbort

set_option linter.unusedVariables false

namespace TypedMap

@[reducible] def has (K V : Type) [BEq K] (m : List (K × V)) (key : K) : Bool :=
  m.any (fun (k, _) => k == key)

def get (K V : Type) [BEq K] [Inhabited V] (m : List (K × V)) (key : K) : V :=
  match m.find? (fun (k, _) => k == key) with
  | some (_, v) => v
  | none => default

def set (K V : Type) [BEq K] (m : List (K × V)) (key : K) (value : V) : List (K × V) :=
  (key, value) :: m.filter (fun (k, _) => !(k == key))

def erase (K V : Type) [BEq K] [Inhabited V] (m : List (K × V)) (key : K) : (V × List (K × V)) :=
  (TypedMap.get K V m key, m.filter (fun (k, _) => !(k == key)))

-- Move's `dynamic_field::remove_if_exists<K, V>(uid, k) -> Option<V>` returns
-- `Some(value)` when present, `None` otherwise; the value is removed in either
-- case (no-op when absent). The first tuple element is the inner-vec
-- representation (`List V`) of the resulting Option — empty for `None`,
-- singleton for `Some` — matching the `MoveOption.MoveOption V`'s `vec` field
-- layout. The renderer wraps it with `MoveOption.mk` at consume sites that
-- need `MoveOption V` directly. Returning `List V` here keeps `Prelude` from
-- importing `MoveStdlib.MoveOption` and avoids the cycle
-- (`MoveOption.lean` already imports `Prelude.TypedMap`).
def erase_if_exists (K V : Type) [BEq K] [Inhabited V] (m : List (K × V)) (key : K)
    : (List V × List (K × V)) :=
  if has K V m key then
    ([TypedMap.get K V m key], m.filter (fun (k, _) => !(k == key)))
  else
    ([], m)

def get.aborts (K V : Type) [BEq K] (_m : List (K × V)) (_key : K) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none
def set.aborts (K V : Type) [BEq K] (_m : List (K × V)) (_key : K) (_value : V) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none
def erase.aborts (K V : Type) [BEq K] [Inhabited V] (_m : List (K × V)) (_key : K) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none
def erase_if_exists.aborts (K V : Type) [BEq K] [Inhabited V] (_m : List (K × V)) (_key : K) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none
def has.aborts (K V : Type) [BEq K] (_m : List (K × V)) (_key : K) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

-- Length lemmas for termination proofs

theorem set_length_le (K V : Type) [BEq K] (m : List (K × V)) (key : K) (value : V) :
    (set K V m key value).length ≤ m.length + 1 := by
  unfold set; simp only [List.length_cons]
  exact Nat.succ_le_succ (List.length_filter_le _ _)

-- Observational equivalence lemmas for set/get/has.
-- These are provable for the association-list representation.

theorem get_set_eq (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V] (m : List (K × V)) (key : K) (val : V) :
    get K V (set K V m key val) key = val := by
  simp [get, set]

theorem get_set_ne (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V] (m : List (K × V)) (k1 k2 : K) (val : V)
    (h : ¬(k1 == k2) = true) :
    get K V (set K V m k1 val) k2 = get K V m k2 := by
  have h : k1 ≠ k2 := by intro heq; exact h (beq_iff_eq.mpr heq)
  unfold get set
  have hbeq : (k1 == k2) = false := beq_eq_false_iff_ne.mpr h
  rw [List.find?_cons]
  simp only [hbeq]
  congr 1
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter_cons]
    split
    · simp only [List.find?_cons]
      split
      · rfl
      · exact ih
    · simp only [List.find?_cons]
      next hfilt =>
        have hfilt' : (hd.1 == k1) = true := by
          cases h_bool : (hd.1 == k1)
          · simp [h_bool] at hfilt
          · rfl
        have hdeq : hd.1 = k1 := beq_iff_eq.mp hfilt'
        have hdk2 : (hd.1 == k2) = false := by
          rw [beq_eq_false_iff_ne, hdeq]; exact h
        simp only [hdk2]
        exact ih

theorem has_set_eq (K V : Type) [BEq K] [LawfulBEq K] (m : List (K × V)) (key : K) (val : V) :
    has K V (set K V m key val) key = true := by
  simp [has, set, List.any_cons]

theorem has_set_ne (K V : Type) [BEq K] [LawfulBEq K] (m : List (K × V)) (k1 k2 : K) (val : V)
    (h : ¬(k1 == k2) = true) :
    has K V (set K V m k1 val) k2 = has K V m k2 := by
  have h : k1 ≠ k2 := by intro heq; exact h (beq_iff_eq.mpr heq)
  unfold has set
  have hbeq : (k1 == k2) = false := beq_eq_false_iff_ne.mpr h
  rw [List.any_cons]
  simp only [hbeq, Bool.false_or]
  induction m with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter_cons]
    split
    · rw [List.any_cons, List.any_cons, ih]
    · next hfilt =>
        rw [List.any_cons]
        have hfilt' : (hd.1 == k1) = true := by
          cases h_bool : (hd.1 == k1)
          · simp [h_bool] at hfilt
          · rfl
        have hdeq : hd.1 = k1 := beq_iff_eq.mp hfilt'
        have hdk2 : (hd.1 == k2) = false := by
          rw [beq_eq_false_iff_ne, hdeq]; exact h
        rw [hdk2, Bool.false_or, ih]

-- has is monotone: setting any key preserves existing has results
theorem has_set_of_has (K V : Type) [BEq K] [LawfulBEq K] (m : List (K × V)) (k1 k2 : K) (val : V)
    (h : has K V m k2 = true) :
    has K V (set K V m k1 val) k2 = true := by
  by_cases heq : (k1 == k2) = true
  · rw [beq_iff_eq] at heq; rw [heq]; exact has_set_eq K V m k2 val
  · rw [has_set_ne K V m k1 k2 val heq]; exact h



-- After erasing a key, has returns false for that key
theorem has_erase_eq (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V] (m : List (K × V)) (key : K) :
    has K V (erase K V m key).2 key = false := by
  unfold erase has
  simp only [List.any_eq_false, List.mem_filter, Bool.not_eq_true', Bool.not_eq_true]
  intro x hx
  exact hx.2

-- The erased value equals get
theorem erase_fst_eq_get (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V] (m : List (K × V)) (key : K) :
    (erase K V m key).1 = get K V m key := rfl

-- Stored-value data invariants: `all K V P m` states that every value stored
-- in the map satisfies `P`. The generated `hdinv` spec-boundary hypotheses and
-- the `_data_inv` preservation goals are stated with this predicate; client
-- proofs discharge them with the algebra below (`all_nil` for fresh tables,
-- `all_set` at each write, `all_erase` at each removal, `get_of_all` to
-- recover `P` for a fetched value — conditioned on membership, since `get`
-- returns `default` for a missing key).

def all (K V : Type) (P : V → Prop) (m : List (K × V)) : Prop :=
  ∀ kv ∈ m, P kv.2

theorem all_nil (K V : Type) (P : V → Prop) : all K V P [] := by
  intro kv h; cases h

theorem get_of_all (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V] {P : V → Prop}
    {m : List (K × V)} {k : K}
    (h : all K V P m) (hmem : has K V m k = true) : P (get K V m k) := by
  induction m with
  | nil => simp [has] at hmem
  | cons hd tl ih =>
    by_cases hk : (hd.1 == k) = true
    · have hget : get K V (hd :: tl) k = hd.2 := by
        simp [get, hk]
      rw [hget]
      exact h hd (List.mem_cons_self ..)
    · have hget : get K V (hd :: tl) k = get K V tl k := by
        simp [get, hk]
      rw [hget]
      have hmem' : has K V tl k = true := by
        simp [has, List.any_cons, hk] at hmem ⊢
        exact hmem
      exact ih (fun kv hkv => h kv (List.mem_cons_of_mem _ hkv)) hmem'

theorem all_set (K V : Type) [BEq K] {P : V → Prop} {m : List (K × V)} {k : K} {v : V}
    (h : all K V P m) (hv : P v) : all K V P (set K V m k v) := by
  intro kv hkv
  unfold set at hkv
  rcases List.mem_cons.mp hkv with heq | hmem
  · subst heq; exact hv
  · exact h _ (List.mem_filter.mp hmem).1

theorem all_erase (K V : Type) [BEq K] [Inhabited V] {P : V → Prop}
    {m : List (K × V)} {k : K}
    (h : all K V P m) : all K V P (erase K V m k).2 := by
  intro kv hkv
  exact h _ (List.mem_filter.mp hkv).1

theorem all_of_all_imp (K V : Type) {P Q : V → Prop} {m : List (K × V)}
    (h : all K V P m) (himp : ∀ v, P v → Q v) : all K V Q m := by
  intro kv hkv
  exact himp _ (h kv hkv)

end TypedMap
