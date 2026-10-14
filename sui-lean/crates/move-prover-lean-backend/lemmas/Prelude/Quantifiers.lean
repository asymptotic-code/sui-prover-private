import Prelude.BoundedNat
import Prelude.Helpers
import MoveStdlib.MoveVectorNatives
import MoveStdlib.IntegerNatives

-- Spec quantifier helpers for Move verification macros.
-- These mirror the Move prover's quantifier operations (forall!, any!, find_index!, etc.)

-- Move vectors are bounded by u64 max. This axiom is also declared in
-- MoveVectorNatives but duplicated here so the Prelude is self-contained.
-- KNOWN INCONSISTENT as stated (false for e.g. `List.replicate (2^64) ()`):
-- it models the Move VM invariant and is scheduled to be replaced by a
-- length-carrying vector subtype (unified-backend-design §13, "BoundedNat
-- soundness overhaul", item 4). Same status: MoveVector.list_length_bounded
-- and MoveVector.findIdx_bounded in MoveVectorNatives.lean.
axiom List.length_bounded_u64 (α : Type) (v : List α) : v.length < 2^64

noncomputable section

-- Move's `forall!`/`exists!` quantify over an entire type and are logical
-- propositions, not computable booleans. They render as native Lean `∀`/`∃`
-- (see the backend renderer), so there is intentionally NO opaque
-- `spec_forall`/`spec_exists` helper here — a quantifier obligation is proven
-- with ordinary `∀`/`∃` intro/elim, not an uninterpreted symbol.

-- Existential any over a vector: checks if any element satisfies the predicate.
-- Used for Move's `any!(vec, |elem| P(elem))` macro.
def spec_any [BEq α] [Inhabited α] (vec : List α) (pred : α → Bool) : Bool :=
  vec.any pred

-- Existential any over a range [start, end) of a vector's indices.
-- The predicate receives the *element* at each index (vec[i]).
-- Used for Move's `any_range!(vec, start, end, |elem| P(elem))` macro.
def spec_any_range [BEq α] [Inhabited α] (start stop : BoundedNat (2^64)) (vec : List α) (pred : α → Bool) : Bool :=
  (List.range (stop.val - start.val)).any (fun i => pred (vec.getD (i + start.val) default))

-- Universal all over a vector: checks if all elements satisfy the predicate.
-- Used for Move's `all!(vec, |elem| P(elem))` macro.
def spec_all [BEq α] [Inhabited α] (vec : List α) (pred : α → Bool) : Bool :=
  vec.all pred

-- Find first index in a vector where predicate holds, returns Option-compatible list.
-- Move's Option<T> is { vec: vector<T> }, and MoveOption wraps this as { vec : List T }.
-- We return just the inner list; the renderer wraps it with MoveOption.mk when needed.
-- Used for Move's `find_index!(vec, |elem| P(elem))` macro.
def spec_find_index [BEq α] [Inhabited α] (vec : List α) (pred : α → Bool) : List (BoundedNat (2^64)) :=
  match h : vec.findIdx? (fun x => pred x) with
  | some idx => [⟨idx, by
      have hlt : idx < vec.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1
      exact Nat.lt_trans hlt (MoveVector.list_length_bounded α vec)⟩]
  | none => []

-- Map a function over a range [start, end), producing a vector.
-- Non-vector-based: the callback receives the index directly.
-- Used for Move's `range_map!(start, end, |i| f(i))` macro.
def spec_range_map [Inhabited β] (start stop : BoundedNat (2^64)) (f : BoundedNat (2^64) → β) : List β :=
  if hle : start.val ≤ stop.val then
    (List.range (stop.val - start.val)).attach.map (fun ⟨i, hi⟩ =>
      have hlt : i < stop.val - start.val := List.mem_range.mp hi
      f ⟨i + start.val, by exact Nat.lt_of_lt_of_le (by omega) stop.property⟩)
  else
    []

-- Map a function over a range of vector indices [start, end).
-- Vector-based: the callback receives the *element* at each index.
def spec_map_range [BEq α] [Inhabited α] [Inhabited β] (start stop : BoundedNat (2^64)) (vec : List α) (f : α → β) : List β :=
  if start.val ≤ stop.val then
    (List.range (stop.val - start.val)).map (fun i => f (vec.getD (i + start.val) default))
  else
    []

-- Universal all over a range of vector indices [start, end).
def spec_all_range [BEq α] [Inhabited α] (start stop : BoundedNat (2^64)) (vec : List α) (pred : α → Bool) : Bool :=
  (List.range (stop.val - start.val)).all (fun i => pred (vec.getD (i + start.val) default))

-- Map a function over a vector, producing a new vector.
def spec_map [BEq α] [Inhabited α] [Inhabited β] (vec : List α) (f : α → β) : List β :=
  vec.map f

-- Filter elements of a vector by predicate.
def spec_filter [BEq α] [Inhabited α] (vec : List α) (pred : α → Bool) : List α :=
  vec.filter pred

-- Filter elements of a vector range [start, end) by predicate.
def spec_filter_range [BEq α] [Inhabited α] (start stop : BoundedNat (2^64)) (vec : List α) (pred : α → Bool) : List α :=
  (List.range (stop.val - start.val)).filterMap (fun i =>
    let elem := vec.getD (i + start.val) default
    if pred elem then some elem else none)

-- Count elements in a vector satisfying predicate.
opaque spec_count [BEq α] [Inhabited α] (vec : List α) (pred : α → Bool) : BoundedNat (2^64)

-- Count elements in a vector range [start, end) satisfying predicate.
opaque spec_count_range [BEq α] [Inhabited α] (start stop : BoundedNat (2^64)) (vec : List α) (pred : α → Bool) : BoundedNat (2^64)

-- Find first element in a vector satisfying predicate, returns MoveOption-compatible list.
def spec_find [BEq α] [Inhabited α] (vec : List α) (pred : α → Bool) : List α :=
  match vec.find? pred with
  | some x => [x]
  | none => []

-- Find first element in a vector range satisfying predicate.
opaque spec_find_range [BEq α] [Inhabited α] (start stop : BoundedNat (2^64)) (vec : List α) (pred : α → Bool) : List α

-- Find first index in a vector range where predicate holds.
opaque spec_find_index_range [BEq α] [Inhabited α] (start stop : BoundedNat (2^64)) (vec : List α) (pred : α → Bool) : List (BoundedNat (2^64))

-- Find all indices in a vector where predicate holds.
opaque spec_find_indices [BEq α] [Inhabited α] (vec : List α) (pred : α → Bool) : List (BoundedNat (2^64))

-- Find all indices in a vector range where predicate holds.
opaque spec_find_indices_range [BEq α] [Inhabited α] (start stop : BoundedNat (2^64)) (vec : List α) (pred : α → Bool) : List (BoundedNat (2^64))

-- Lift a per-element value into the arbitrary-precision `Integer` accumulator
-- used by `spec_sum_map`. The Move prover's `sum_map!` lambda returns a numeric
-- type (in practice always a `BoundedNat`); this class supplies the canonical
-- non-negative embedding `BoundedNat n ↪ Integer` (= `.val`).
class ToInteger (β : Type) where
  toInteger : β → Integer.Integer
  toInteger_nonneg : ∀ x, 0 ≤ toInteger x

instance : ToInteger (BoundedNat bound) where
  toInteger x := (x.val : Integer.Integer)
  toInteger_nonneg x := Int.ofNat_nonneg x.val

-- Sum a mapped function over a vector.
-- Returns `Integer` because the Move-prover's `sum_map!` macro is declared
-- as `... -> Integer`: `public macro fun sum_map<$T, $U>(...): Integer`.
-- The lambda's β is the per-element type (typically a `BoundedNat`); the
-- accumulated sum lifts into arbitrary-precision `Integer` (via `ToInteger`) to
-- avoid overflow. Defined as a left fold so its algebra (membership ≤ sum,
-- additivity under cons/erase) is provable rather than axiomatized.
def spec_sum_map [BEq α] [Inhabited α] [Inhabited β] [ToInteger β] (vec : List α) (f : α → β) : Integer.Integer :=
  (vec.map (fun x => ToInteger.toInteger (f x))).foldl (· + ·) 0

-- `spec_sum_map` algebra (now provable, since the def is a concrete fold).

theorem foldl_add_acc (l : List Integer.Integer) (acc : Integer.Integer) :
    l.foldl (· + ·) acc = acc + l.foldl (· + ·) 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (acc + x), ih (0 + x)]
    simp only [Int.zero_add, Int.add_assoc]

theorem spec_sum_foldl_nonneg [Inhabited β] [ToInteger β] (l : List β) :
    0 ≤ (l.map ToInteger.toInteger).foldl (· + ·) 0 := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_add_acc _ (0 + ToInteger.toInteger y)]
    simp only [Int.zero_add]
    exact Int.add_nonneg (ToInteger.toInteger_nonneg y) ih

theorem mapf_foldl_nonneg [Inhabited β] [ToInteger β] (l : List α) (f : α → β) :
    0 ≤ (l.map (fun x => ToInteger.toInteger (f x))).foldl (· + ·) 0 := by
  have h := spec_sum_foldl_nonneg (l.map f); rwa [List.map_map] at h

-- Every summand is ≤ the total (all summands are non-negative).
theorem spec_sum_map_mem [BEq α] [Inhabited α] [Inhabited β] [ToInteger β]
    (vec : List α) (f : α → β) (a : α) (h : a ∈ vec) :
    ToInteger.toInteger (f a) ≤ spec_sum_map vec f := by
  unfold spec_sum_map
  induction vec with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_add_acc _ (0 + ToInteger.toInteger (f x))]
    simp only [Int.zero_add]
    generalize hS : (xs.map (fun x => ToInteger.toInteger (f x))).foldl (· + ·) 0 = S
    have hSnn : 0 ≤ S := by rw [← hS]; exact mapf_foldl_nonneg xs f
    rcases List.mem_cons.mp h with hx | hxs
    · subst hx
      exact Int.le_add_of_nonneg_right hSnn
    · have hih := ih hxs
      rw [hS] at hih
      exact Int.le_trans hih (Int.le_add_of_nonneg_left (ToInteger.toInteger_nonneg (f x)))

-- Sum a mapped function over a vector range. Returns `Integer` for the
-- same reason as `spec_sum_map`.
opaque spec_sum_map_range [BEq α] [Inhabited α] [Inhabited β] (start stop : BoundedNat (2^64)) (vec : List α) (f : α → β) : Integer.Integer

-- Count indices in a range [start, end) where the predicate holds.
-- Non-vector-based: callback receives the index directly.
-- Used for Move's `range_count!(start, end, |i| P(i))` macro.
opaque spec_range_count (start stop : BoundedNat (2^64)) (pred : BoundedNat (2^64) → Bool) : BoundedNat (2^64)

-- Sum a mapped function over a range [start, end).
-- Non-vector-based: callback receives the index directly.
-- Used for Move's `range_sum_map!(start, end, |i| f(i))` macro. Returns
-- `Integer` for the same reason as `spec_sum_map`.
opaque spec_range_sum_map [Inhabited β] (start stop : BoundedNat (2^64)) (f : BoundedNat (2^64) → β) : Integer.Integer

end
