import BackendComparison.Lean_only

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace Lean_only_proofs

open _root_.Lean_only

theorem square_mod_four_spec_aborts (value : BoundedNat (2^8)) :
    square_mod_four_spec.aborts value = Option.none := by
  have hcv : (BoundedNat.convert value : BoundedNat (2^64)).val = value.val :=
    BoundedNat.convert_val_of_lt value (by have := value.property; omega)
  have hsmall : value.val * value.val < 256 * 256 := by
    by_cases hz : value.val = 0
    · simp [hz]
    · have h1 := Nat.mul_lt_mul_of_pos_right value.property (by omega : 0 < value.val)
      have h2 := Nat.mul_lt_mul_of_pos_left value.property (by omega : 0 < 256)
      exact Nat.lt_trans h1 h2
  have hprod :
      (BoundedNat.convert value : BoundedNat (2^64)).val *
          (BoundedNat.convert value : BoundedNat (2^64)).val < 2^64 := by
    rw [hcv]
    exact Nat.lt_trans hsmall (by decide)
  simp [square_mod_four_spec.aborts, square_mod_four.aborts,
    BoundedNat.mul_overflows_false_of_bounds _ _ hprod]
  decide

theorem square_mod_four_spec_ensures (value : BoundedNat (2^8)) :
    square_mod_four_spec.ensures value := by
  have hcv : (BoundedNat.convert value : BoundedNat (2^64)).val = value.val :=
    BoundedNat.convert_val_of_lt value (by have := value.property; omega)
  have hsmall : value.val * value.val < 256 * 256 := by
    by_cases hz : value.val = 0
    · simp [hz]
    · have h1 := Nat.mul_lt_mul_of_pos_right value.property (by omega : 0 < value.val)
      have h2 := Nat.mul_lt_mul_of_pos_left value.property (by omega : 0 < 256)
      exact Nat.lt_trans h1 h2
  have hprod :
      (BoundedNat.convert value : BoundedNat (2^64)).val *
          (BoundedNat.convert value : BoundedNat (2^64)).val < 2^64 := by
    rw [hcv]
    exact Nat.lt_trans hsmall (by decide)
  unfold square_mod_four_spec.ensures
  rw [bne_iff_ne]
  intro heq
  have heqv := congrArg BoundedNat.val heq
  have mod_val (a b : BoundedNat (2^64)) : (a % b).val = a.val % b.val := by
    change (BoundedNat.mod a b).val = a.val % b.val
    by_cases hb : b.val = 0
    · simp [BoundedNat.mod, hb]
    · simp [BoundedNat.mod, hb]
  simp [square_mod_four, mod_val, BoundedNat.mul_val _ _ hprod, hcv] at heqv
  have val_four : (4 : BoundedNat (2^64)).val = 4 := by decide
  have val_two : (2 : BoundedNat (2^64)).val = 2 := by decide
  rw [val_four, val_two, Nat.mul_mod] at heqv
  have hrem : value.val % 4 < 4 := Nat.mod_lt _ (by omega)
  have cases : value.val % 4 = 0 ∨ value.val % 4 = 1 ∨
      value.val % 4 = 2 ∨ value.val % 4 = 3 := by omega
  rcases cases with h | h | h | h <;> simp [h] at heqv

end Lean_only_proofs
