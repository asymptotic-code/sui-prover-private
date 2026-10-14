import Prelude.BoundedNat
import Prelude.Helpers
import MoveStdlib.MoveVectorNatives
import MoveStdlib.IntegerNatives

-- Spec quantifier helpers for Move verification macros.
-- These mirror the Move prover's quantifier operations (forall!, any!, find_index!, etc.)

-- Move vectors are bounded by u64 max. This axiom is also declared in
-- MoveVectorNatives but duplicated here so the Prelude is self-contained.
axiom List.length_bounded_u64 (α : Type) (v : List α) : v.length < 2^64

-- Universal quantifier over all valid values of a type.
-- Used for Move's `forall!(|x| P(x))` macro.
-- Surfaces as `Bool` so callers in either Bool or Prop context type-check
-- uniformly: Bool callers use it directly, Prop callers wrap with ToProp as
-- `spec_forall pred = true`.
noncomputable def spec_forall [BEq α] [Inhabited α] (pred : α → Bool) : Bool :=
  by
    classical
    exact if h : ∀ x, pred x = true then true else false

theorem spec_forall_eq_true [BEq α] [Inhabited α] {pred : α → Bool} :
    spec_forall pred = true ↔ ∀ x, pred x = true := by
  unfold spec_forall
  classical
  by_cases h : ∀ x, pred x = true <;> simp [h]

theorem spec_forall_intro [BEq α] [Inhabited α] {pred : α → Bool}
    (h : ∀ x, pred x = true) :
    spec_forall pred = true :=
  spec_forall_eq_true.mpr h

theorem spec_forall_elim [BEq α] [Inhabited α] {pred : α → Bool}
    (h : spec_forall pred = true) :
    ∀ x, pred x = true :=
  spec_forall_eq_true.mp h

-- Existential quantifier over all valid values of a type.
-- Used for Move's `exists!(|x| P(x))` macro.
-- In ensures, ToProp wraps as `spec_exists pred = true`.
noncomputable def spec_exists [BEq α] [Inhabited α] (pred : α → Bool) : Bool :=
  by
    classical
    exact if h : ∃ x, pred x = true then true else false

theorem spec_exists_eq_true [BEq α] [Inhabited α] {pred : α → Bool} :
    spec_exists pred = true ↔ ∃ x, pred x = true := by
  unfold spec_exists
  classical
  by_cases h : ∃ x, pred x = true <;> simp [h]

theorem spec_exists_intro [BEq α] [Inhabited α] {pred : α → Bool}
    (h : ∃ x, pred x = true) :
    spec_exists pred = true :=
  spec_exists_eq_true.mpr h

theorem spec_exists_elim [BEq α] [Inhabited α] {pred : α → Bool}
    (h : spec_exists pred = true) :
    ∃ x, pred x = true :=
  spec_exists_eq_true.mp h

def spec_bounded_u64 (n : Nat) : BoundedNat (2^64) :=
  ⟨n % 2^64, Nat.mod_lt _ (by decide)⟩

def spec_range_indices (start stop : BoundedNat (2^64)) : List (BoundedNat (2^64)) :=
  if hle : start.val ≤ stop.val then
    (List.range (stop.val - start.val)).attach.map (fun ⟨i, hi⟩ =>
      have hlt : i < stop.val - start.val := List.mem_range.mp hi
      ⟨i + start.val, by exact Nat.lt_of_lt_of_le (by omega) stop.property⟩)
  else
    []

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
def spec_count [BEq α] [Inhabited α] (vec : List α) (pred : α → Bool) : BoundedNat (2^64) :=
  spec_bounded_u64 (vec.filter pred).length

-- Count elements in a vector range [start, end) satisfying predicate.
def spec_count_range [BEq α] [Inhabited α] (start stop : BoundedNat (2^64)) (vec : List α) (pred : α → Bool) : BoundedNat (2^64) :=
  spec_bounded_u64 ((List.range (stop.val - start.val)).filter (fun i => pred (vec.getD (i + start.val) default))).length

-- Find first element in a vector satisfying predicate, returns MoveOption-compatible list.
def spec_find [BEq α] [Inhabited α] (vec : List α) (pred : α → Bool) : List α :=
  match vec.find? pred with
  | some x => [x]
  | none => []

-- Find first element in a vector range satisfying predicate.
def spec_find_range [BEq α] [Inhabited α] (start stop : BoundedNat (2^64)) (vec : List α) (pred : α → Bool) : List α :=
  match (List.range (stop.val - start.val)).find? (fun i => pred (vec.getD (i + start.val) default)) with
  | some i => [vec.getD (i + start.val) default]
  | none => []

-- Find first index in a vector range where predicate holds.
def spec_find_index_range [BEq α] [Inhabited α] (start stop : BoundedNat (2^64)) (vec : List α) (pred : α → Bool) : List (BoundedNat (2^64)) :=
  match (spec_range_indices start stop).find? (fun i => pred (vec.getD i.val default)) with
  | some i => [i]
  | none => []

-- Find all indices in a vector where predicate holds.
def spec_find_indices [BEq α] [Inhabited α] (vec : List α) (pred : α → Bool) : List (BoundedNat (2^64)) :=
  (List.range vec.length).attach.filterMap (fun ⟨i, hi⟩ =>
    if pred (vec.getD i default) then
      some ⟨i, Nat.lt_trans (List.mem_range.mp hi) (MoveVector.list_length_bounded α vec)⟩
    else
      none)

-- Find all indices in a vector range where predicate holds.
def spec_find_indices_range [BEq α] [Inhabited α] (start stop : BoundedNat (2^64)) (vec : List α) (pred : α → Bool) : List (BoundedNat (2^64)) :=
  (spec_range_indices start stop).filter (fun i => pred (vec.getD i.val default))

class SpecToInteger (β : Type) where
  toInteger : β → Integer.Integer

instance : SpecToInteger Integer.Integer where
  toInteger x := x

instance : SpecToInteger Nat where
  toInteger x := Int.ofNat x

instance {bound : Nat} : SpecToInteger (BoundedNat bound) where
  toInteger x := Int.ofNat x.val

-- Sum a mapped function over a vector.
-- Returns `Integer` because the Move-prover's `sum_map!` macro is declared
-- as `... -> Integer`: `public macro fun sum_map<$T, $U>(...): Integer`.
-- The lambda's β is the per-element type (typically a `BoundedNat`); the
-- accumulated sum lifts into arbitrary-precision `Integer` to avoid overflow.
def spec_sum_map [BEq α] [Inhabited α] [Inhabited β] [SpecToInteger β] (vec : List α) (f : α → β) : Integer.Integer :=
  vec.foldl (fun acc x => acc + SpecToInteger.toInteger (f x)) 0

-- Sum a mapped function over a vector range. Returns `Integer` for the
-- same reason as `spec_sum_map`.
def spec_sum_map_range [BEq α] [Inhabited α] [Inhabited β] [SpecToInteger β] (start stop : BoundedNat (2^64)) (vec : List α) (f : α → β) : Integer.Integer :=
  (List.range (stop.val - start.val)).foldl (fun acc i => acc + SpecToInteger.toInteger (f (vec.getD (i + start.val) default))) 0

-- Count indices in a range [start, end) where the predicate holds.
-- Non-vector-based: callback receives the index directly.
-- Used for Move's `range_count!(start, end, |i| P(i))` macro.
def spec_range_count (start stop : BoundedNat (2^64)) (pred : BoundedNat (2^64) → Bool) : BoundedNat (2^64) :=
  spec_bounded_u64 ((spec_range_indices start stop).filter pred).length

-- Sum a mapped function over a range [start, end).
-- Non-vector-based: callback receives the index directly.
-- Used for Move's `range_sum_map!(start, end, |i| f(i))` macro. Returns
-- `Integer` for the same reason as `spec_sum_map`.
def spec_range_sum_map [Inhabited β] [SpecToInteger β] (start stop : BoundedNat (2^64)) (f : BoundedNat (2^64) → β) : Integer.Integer :=
  (spec_range_indices start stop).foldl (fun acc i => acc + SpecToInteger.toInteger (f i)) 0

theorem spec_all_getD_of_lt
    {α : Type} [BEq α] [Inhabited α]
    (xs : List α) (pred : α → Bool) (i : Nat)
    (h_all : spec_all xs pred = true)
    (h_lt : i < xs.length) :
    pred (xs.getD i default) = true := by
  unfold spec_all at h_all
  have h_pred := (List.all_eq_true.mp h_all) xs[i] (List.getElem_mem h_lt)
  simpa [List.getD, h_lt] using h_pred

theorem spec_all_drop
    {α : Type} [BEq α] [Inhabited α]
    (xs : List α) (pred : α → Bool) (n : Nat)
    (h_all : spec_all xs pred = true) :
    spec_all (xs.drop n) pred = true := by
  unfold spec_all at h_all ⊢
  exact List.all_eq_true.mpr (by
    intro x hx
    exact (List.all_eq_true.mp h_all) x (List.mem_of_mem_drop hx))

theorem spec_any_exists_mem_true
    {α : Type} [BEq α] [Inhabited α]
    (xs : List α) (pred : α → Bool)
    (h_any : spec_any xs pred = true) :
    ∃ x, x ∈ xs ∧ pred x = true := by
  unfold spec_any at h_any
  simpa [List.any_eq_true] using h_any

theorem spec_any_exists_getD_true
    {α : Type} [BEq α] [Inhabited α]
    (xs : List α) (pred : α → Bool)
    (h_any : spec_any xs pred = true) :
    ∃ i : Nat, i < xs.length ∧ pred (xs.getD i default) = true := by
  induction xs with
  | nil =>
      simp [spec_any] at h_any
  | cons x xs ih =>
      unfold spec_any at h_any
      simp at h_any
      rcases h_any with h_head | h_tail
      · exact ⟨0, by simp, by simpa [List.getD] using h_head⟩
      · rcases ih (by simpa [spec_any] using h_tail) with ⟨i, h_lt, h_pred⟩
        refine ⟨i + 1, by simpa [Nat.succ_eq_add_one] using Nat.succ_lt_succ h_lt, ?_⟩
        simpa [List.getD, Nat.succ_eq_add_one, h_lt] using h_pred

theorem spec_any_getD_false_of_false
    {α : Type} [BEq α] [Inhabited α]
    (xs : List α) (pred : α → Bool) (i : Nat)
    (h_any : spec_any xs pred = false)
    (h_lt : i < xs.length) :
    pred (xs.getD i default) = false := by
  by_cases h_pred : pred (xs.getD i default) = true
  · have h_mem : xs.getD i default ∈ xs := by
      simp [List.getD, h_lt]
    have h_any_true : spec_any xs pred = true := by
      unfold spec_any
      exact List.any_eq_true.mpr ⟨xs.getD i default, h_mem, h_pred⟩
    rw [h_any] at h_any_true
    cases h_any_true
  · cases h_val : pred (xs.getD i default)
    · rfl
    · exact False.elim (h_pred h_val)

private theorem spec_sum_map_boundedNat_foldl_ge_acc
    {α : Type} {bound : Nat}
    (xs : List α) (f : α → BoundedNat bound) (acc : Int) :
    acc ≤ xs.foldl (fun acc x => acc + ((f x).val : Int)) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x rest ih =>
      have h_step : acc ≤ acc + ((f x).val : Int) := by
        omega
      exact Int.le_trans h_step (ih (acc + ((f x).val : Int)))

theorem spec_sum_map_boundedNat_cons_ge_head
    {α : Type} [BEq α] [Inhabited α] {bound : Nat}
    [Inhabited (BoundedNat bound)]
    (x : α) (xs : List α) (f : α → BoundedNat bound) :
    ((f x).val : Int) ≤ spec_sum_map (x :: xs) f := by
  unfold spec_sum_map SpecToInteger.toInteger
  simp
  exact spec_sum_map_boundedNat_foldl_ge_acc xs f ((f x).val : Int)

theorem spec_sum_map_boundedNat_getD_zero_le
    {α : Type} [BEq α] [Inhabited α] {bound : Nat}
    [Inhabited (BoundedNat bound)]
    (xs : List α) (f : α → BoundedNat bound)
    (h_nonempty : 0 < xs.length) :
    ((f (xs.getD 0 default)).val : Int) ≤ spec_sum_map xs f := by
  cases xs with
  | nil =>
      simp at h_nonempty
  | cons x rest =>
      simpa [List.getD] using
        spec_sum_map_boundedNat_cons_ge_head x rest f

theorem spec_filter_getD_zero_ne_nil_of_pred
    {α : Type} [BEq α] [Inhabited α]
    (xs : List α) (pred : α → Bool)
    (h_nonempty : 0 < xs.length)
    (h_pred : pred (xs.getD 0 default) = true) :
    spec_filter xs pred ≠ [] := by
  cases xs with
  | nil =>
      simp at h_nonempty
  | cons x rest =>
      have h_pred_x : pred x = true := by
        simpa [List.getD] using h_pred
      simp [spec_filter, h_pred_x]

theorem spec_sum_map_boundedNat_filter_getD_zero_le
    {α : Type} [BEq α] [Inhabited α] {bound : Nat}
    [Inhabited (BoundedNat bound)]
    (xs : List α) (pred : α → Bool) (f : α → BoundedNat bound)
    (h_nonempty : 0 < xs.length)
    (h_pred : pred (xs.getD 0 default) = true) :
    ((f (xs.getD 0 default)).val : Int) ≤
      spec_sum_map (spec_filter xs pred) f := by
  cases xs with
  | nil =>
      simp at h_nonempty
  | cons x rest =>
      have h_pred_x : pred x = true := by
        simpa [List.getD] using h_pred
      simpa [spec_filter, h_pred_x] using
        spec_sum_map_boundedNat_cons_ge_head
          x (List.filter pred rest) f

theorem spec_filter_cons_of_true
    {α : Type} [BEq α] [Inhabited α]
    (x : α) (xs : List α) (pred : α → Bool)
    (h_pred : pred x = true) :
    spec_filter (x :: xs) pred = x :: spec_filter xs pred := by
  simp [spec_filter, h_pred]

theorem spec_filter_cons_of_false
    {α : Type} [BEq α] [Inhabited α]
    (x : α) (xs : List α) (pred : α → Bool)
    (h_pred : pred x = false) :
    spec_filter (x :: xs) pred = spec_filter xs pred := by
  simp [spec_filter, h_pred]

theorem spec_filter_drop_one_eq_tail_of_head_false
    {α : Type} [BEq α] [Inhabited α]
    (xs : List α) (pred : α → Bool)
    (h_head : pred (xs.getD 0 default) = false) :
    spec_filter (xs.drop 1) pred = spec_filter xs pred := by
  cases xs with
  | nil =>
      simp [spec_filter]
  | cons x rest =>
      have h_pred_x : pred x = false := by
        simpa [List.getD] using h_head
      simp [spec_filter, h_pred_x]

private theorem spec_sum_map_foldl_add
    {α β : Type} [Inhabited β] [SpecToInteger β]
    (xs : List α) (f : α → β) (acc : Int) :
    xs.foldl (fun acc x => acc + SpecToInteger.toInteger (f x)) acc =
      acc + xs.foldl (fun acc x => acc + SpecToInteger.toInteger (f x)) 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x rest ih =>
      change
        rest.foldl (fun acc x => acc + SpecToInteger.toInteger (f x))
            (acc + SpecToInteger.toInteger (f x)) =
          acc +
            rest.foldl (fun acc x => acc + SpecToInteger.toInteger (f x))
              (0 + SpecToInteger.toInteger (f x))
      rw [ih (acc + SpecToInteger.toInteger (f x)),
        ih (0 + SpecToInteger.toInteger (f x))]
      simp [Int.add_assoc]

theorem spec_sum_map_cons
    {α β : Type} [BEq α] [Inhabited α] [Inhabited β] [SpecToInteger β]
    (x : α) (xs : List α) (f : α → β) :
    spec_sum_map (x :: xs) f =
      SpecToInteger.toInteger (f x) + spec_sum_map xs f := by
  unfold spec_sum_map
  change
    xs.foldl (fun acc x => acc + SpecToInteger.toInteger (f x))
        (0 + SpecToInteger.toInteger (f x)) =
      SpecToInteger.toInteger (f x) +
        xs.foldl (fun acc x => acc + SpecToInteger.toInteger (f x)) 0
  rw [spec_sum_map_foldl_add]
  simp

theorem spec_sum_map_drop_one
    {α β : Type} [BEq α] [Inhabited α] [Inhabited β] [SpecToInteger β]
    (xs : List α) (f : α → β)
    (h_nonempty : 0 < xs.length) :
    spec_sum_map xs f =
      SpecToInteger.toInteger (f (xs.getD 0 default)) +
        spec_sum_map (xs.drop 1) f := by
  cases xs with
  | nil =>
      simp at h_nonempty
  | cons x rest =>
      simp [List.getD, spec_sum_map_cons]

theorem spec_range_map_length_of_le
    {β : Type} [Inhabited β]
    (start stop : BoundedNat (2^64)) (f : BoundedNat (2^64) → β)
    (h_le : start.val ≤ stop.val) :
    (spec_range_map start stop f).length = stop.val - start.val := by
  unfold spec_range_map
  simp [h_le]

theorem spec_range_map_getD_zero_of_lt
    {β : Type} [Inhabited β]
    (start stop : BoundedNat (2^64)) (f : BoundedNat (2^64) → β)
    (h_lt : start.val < stop.val) :
    (spec_range_map start stop f).getD 0 default = f start := by
  unfold spec_range_map
  have hle : start.val ≤ stop.val := Nat.le_of_lt h_lt
  have h_pos : 0 < stop.val - start.val := Nat.sub_pos_of_lt h_lt
  simp [hle, h_pos]

theorem spec_range_map_getElem?_of_lt
    {β : Type} [Inhabited β]
    (start stop : BoundedNat (2^64)) (f : BoundedNat (2^64) → β)
    (h_le : start.val ≤ stop.val) {i : Nat}
    (h_i : i < stop.val - start.val) :
    (spec_range_map start stop f)[i]? =
      some (f (⟨i + start.val, by
        have h_lt_stop : i + start.val < stop.val := by omega
        exact Nat.lt_trans h_lt_stop stop.property⟩ : BoundedNat (2^64))) := by
  unfold spec_range_map
  simp [h_le, List.getElem?_map, List.getElem?_attach,
    List.getElem?_range h_i]

theorem spec_range_map_getElem?_of_ge
    {β : Type} [Inhabited β]
    (start stop : BoundedNat (2^64)) (f : BoundedNat (2^64) → β)
    (h_le : start.val ≤ stop.val) {i : Nat}
    (h_i : stop.val - start.val ≤ i) :
    (spec_range_map start stop f)[i]? = none := by
  unfold spec_range_map
  simp [h_le, h_i]

theorem spec_range_map_snoc
    {β : Type} [Inhabited β]
    (start stop : BoundedNat (2^64))
    (f_new f_old : BoundedNat (2^64) → β)
    (h_le : start.val ≤ stop.val)
    (h_stop_lt :
      BoundedNat.lt stop
        (18446744073709551615 : BoundedNat (2^64)) = true)
    (h_preserve :
      ∀ i : BoundedNat (2^64),
        start.val ≤ i.val → i.val < stop.val → f_new i = f_old i) :
    spec_range_map start (BoundedNat.add stop (1 : BoundedNat (2^64)))
        f_new =
      spec_range_map start stop f_old ++ [f_new stop] := by
  apply List.ext_getElem?
  intro i
  have h_new_tail_val :=
    boundedNat_u64_add_one_val_of_lt_max stop h_stop_lt
  have h_new_le :
      start.val ≤ (BoundedNat.add stop (1 : BoundedNat (2^64))).val := by
    omega
  have h_old_len := spec_range_map_length_of_le start stop f_old h_le
  by_cases h_i_lt_old : i < stop.val - start.val
  · have h_i_lt_new :
        i < (BoundedNat.add stop (1 : BoundedNat (2^64))).val -
          start.val := by
      omega
    rw [spec_range_map_getElem?_of_lt start
      (BoundedNat.add stop (1 : BoundedNat (2^64))) f_new
      h_new_le h_i_lt_new]
    rw [List.getElem?_append]
    simp [h_old_len, h_i_lt_old]
    have h_old_get? :=
      spec_range_map_getElem?_of_lt start stop f_old h_le h_i_lt_old
    have h_old_get_some :
        (spec_range_map start stop f_old)[i]? =
          some ((spec_range_map start stop f_old)[i]) :=
      List.getElem?_eq_getElem (l := spec_range_map start stop f_old)
        (i := i) (by simpa [h_old_len] using h_i_lt_old)
    rw [h_old_get_some] at h_old_get?
    injection h_old_get? with h_old_get
    rw [h_old_get]
    apply h_preserve
    · exact Nat.le_add_left start.val i
    · simp
      omega
  · by_cases h_i_eq_old : i = stop.val - start.val
    · subst i
      have h_i_lt_new :
          stop.val - start.val <
            (BoundedNat.add stop (1 : BoundedNat (2^64))).val -
              start.val := by
        omega
      rw [spec_range_map_getElem?_of_lt start
        (BoundedNat.add stop (1 : BoundedNat (2^64))) f_new
        h_new_le h_i_lt_new]
      rw [List.getElem?_append]
      simp [h_old_len]
      apply congrArg f_new
      apply BoundedNat.ext
      simp
      omega
    · have h_i_gt_old : stop.val - start.val < i :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_gt h_i_lt_old)
          (Ne.symm h_i_eq_old)
      have h_i_ge_new :
          (BoundedNat.add stop (1 : BoundedNat (2^64))).val -
            start.val ≤ i := by
        omega
      rw [spec_range_map_getElem?_of_ge start
        (BoundedNat.add stop (1 : BoundedNat (2^64))) f_new
        h_new_le h_i_ge_new]
      rw [List.getElem?_append]
      have h_not_lt : ¬ i < (spec_range_map start stop f_old).length := by
        rw [h_old_len]
        exact Nat.not_lt_of_ge (Nat.le_of_lt h_i_gt_old)
      simp [h_not_lt]
      have h_sub_pos :
          0 < i - (spec_range_map start stop f_old).length := by
        rw [h_old_len]
        exact Nat.sub_pos_of_lt h_i_gt_old
      cases h_sub : i - (spec_range_map start stop f_old).length with
      | zero =>
          omega
      | succ k =>
          simp

theorem spec_range_map_tail
    {β : Type} [Inhabited β]
    (start stop : BoundedNat (2^64))
    (f_new f_old : BoundedNat (2^64) → β)
    (h_lt : start.val < stop.val)
    (h_start_lt_max :
      BoundedNat.lt start
        (18446744073709551615 : BoundedNat (2^64)) = true)
    (h_preserve :
      ∀ i : BoundedNat (2^64),
        start.val < i.val → i.val < stop.val → f_new i = f_old i) :
    spec_range_map (BoundedNat.add start (1 : BoundedNat (2^64)))
        stop f_new =
      (spec_range_map start stop f_old).drop 1 := by
  apply List.ext_getElem?
  intro i
  have h_start_add_val :=
    boundedNat_u64_add_one_val_of_lt_max start h_start_lt_max
  have h_new_le :
      (BoundedNat.add start (1 : BoundedNat (2^64))).val ≤ stop.val := by
    omega
  have h_old_le : start.val ≤ stop.val := Nat.le_of_lt h_lt
  by_cases h_i_lt_new :
      i < stop.val -
        (BoundedNat.add start (1 : BoundedNat (2^64))).val
  · have h_i1_lt_old : 1 + i < stop.val - start.val := by
      omega
    rw [spec_range_map_getElem?_of_lt
      (BoundedNat.add start (1 : BoundedNat (2^64))) stop f_new
      h_new_le h_i_lt_new]
    rw [List.getElem?_drop]
    rw [spec_range_map_getElem?_of_lt start stop f_old h_old_le
      h_i1_lt_old]
    apply congrArg some
    let idx_new : BoundedNat (2^64) :=
      ⟨i + (BoundedNat.add start (1 : BoundedNat (2^64))).val, by
        have h_lt_stop :
            i + (BoundedNat.add start (1 : BoundedNat (2^64))).val <
              stop.val := by
          omega
        exact Nat.lt_trans h_lt_stop stop.property⟩
    let idx_old : BoundedNat (2^64) :=
      ⟨1 + i + start.val, by
        have h_lt_stop : 1 + i + start.val < stop.val := by
          omega
        exact Nat.lt_trans h_lt_stop stop.property⟩
    have h_idx_eq : idx_new = idx_old := by
      apply BoundedNat.ext
      simp [idx_new, idx_old, h_start_add_val]
      omega
    change f_new idx_new = f_old idx_old
    rw [← h_idx_eq]
    apply h_preserve
    · simp [idx_new, h_start_add_val]
      omega
    · simp [idx_new]
      omega
  · have h_i_ge_new :
        stop.val -
          (BoundedNat.add start (1 : BoundedNat (2^64))).val ≤ i :=
      Nat.le_of_not_gt h_i_lt_new
    have h_i1_ge_old : stop.val - start.val ≤ 1 + i := by
      omega
    rw [spec_range_map_getElem?_of_ge
      (BoundedNat.add start (1 : BoundedNat (2^64))) stop f_new
      h_new_le h_i_ge_new]
    rw [List.getElem?_drop]
    rw [spec_range_map_getElem?_of_ge start stop f_old h_old_le
      h_i1_ge_old]
