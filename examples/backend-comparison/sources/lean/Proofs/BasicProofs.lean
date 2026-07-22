import BackendComparison.Basic

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace Basic_proofs

open _root_.Basic

theorem increment_spec_aborts (value : BoundedNat (2^64)) :
    increment_spec.asserts_cond value →
    Basic.increment.aborts value = Option.none := by
  intro h
  simp [Basic.increment.aborts, increment_spec.asserts_cond] at h ⊢
  omega

theorem increment_spec_ensures (value : BoundedNat (2^64)) :
    increment_spec.asserts_cond value →
    increment_spec.ensures value := by
  intro _
  simp [increment_spec.ensures, Basic.increment]

theorem increment_spec_ensures_1 (value : BoundedNat (2^64)) :
    increment_spec.asserts_cond value →
    increment_spec.ensures_1 value := by
  intro h
  simp [increment_spec.asserts_cond] at h
  have hv : value.val + 1 < 2^64 := by omega
  have hadd : (value + (1 : BoundedNat (2^64))).val = value.val + 1 :=
    BoundedNat.add_val_u64 value 1 hv
  simp only [increment_spec.ensures_1, Basic.increment, decide_eq_true_eq,
    BoundedNat.lt_def]
  rw [hadd]
  omega

theorem max_spec_aborts (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) :
    max_spec.aborts a b = Option.none := by
  simp [max_spec.aborts, Basic.max.aborts]

theorem max_spec_ensures (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) :
    max_spec.ensures a b := by
  by_cases h : a ≥ b
  · simp [max_spec.ensures, Basic.max, h]
  · have h' : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge h)
    simp [max_spec.ensures, Basic.max, h, h']

theorem max_spec_ensures_1 (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) :
    max_spec.ensures_1 a b := by
  by_cases h : a ≥ b
  · simp [max_spec.ensures_1, Basic.max, h]
  · simp [max_spec.ensures_1, Basic.max, h]

theorem max_spec_ensures_2 (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) :
    max_spec.ensures_2 a b := by
  by_cases h : a ≥ b
  · simp [max_spec.ensures_2, Basic.max, h]
  · simp [max_spec.ensures_2, Basic.max, h]

theorem wrapped_value_is_some_spec_aborts (value : BoundedNat (2^64)) :
    wrapped_value_is_some_spec.aborts value = Option.none := by
  simp [wrapped_value_is_some_spec.aborts, Basic.wrapped_value_is_some.aborts,
    MoveOption.some.aborts, MoveOption.is_some.aborts]

theorem wrapped_value_is_some_spec_ensures (value : BoundedNat (2^64)) :
    wrapped_value_is_some_spec.ensures value := by
  simp [wrapped_value_is_some_spec.ensures, Basic.wrapped_value_is_some,
    MoveOption.is_some, MoveVector.singleton]

end Basic_proofs
