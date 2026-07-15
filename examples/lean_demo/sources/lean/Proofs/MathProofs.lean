import lean_demo.Math
import Auto.Tactic

set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "z3"
set_option auto.smt.additionalFlags "smt.random_seed=0"

namespace Math_proofs

open _root_.Math

theorem clamp_spec_aborts (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) :
    clamp_spec.requires value low high →
    Math.clamp.aborts value low high = Option.none := by
  intro _
  simp [Math.clamp.aborts, MoveAbort.orElse]

theorem clamp_spec_ensures (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) :
    clamp_spec.requires value low high →
    clamp_spec.ensures value low high := by
  intro hreq
  simp only [Math.clamp_spec.requires, decide_eq_true_eq,
    BoundedNat.le_def] at hreq
  simp only [Math.clamp_spec.ensures, Math.clamp, decide_eq_true_eq,
    BoundedNat.le_def]
  split
  · simp only [BoundedNat.lt_def] at *
    auto
  · split <;>
      simp only [BoundedNat.lt_def, gt_iff_lt] at * <;>
      auto

theorem clamp_spec_ensures_1 (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) :
    clamp_spec.requires value low high →
    clamp_spec.ensures_1 value low high := by
  intro hreq
  simp only [Math.clamp_spec.requires, decide_eq_true_eq,
    BoundedNat.le_def] at hreq
  simp only [Math.clamp_spec.ensures_1, Math.clamp, decide_eq_true_eq,
    BoundedNat.le_def]
  split
  · simp only [BoundedNat.lt_def] at *
    auto
  · split <;>
      simp only [BoundedNat.lt_def, gt_iff_lt] at * <;>
      auto

theorem clamp_spec_ensures_2 (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) :
    clamp_spec.requires value low high →
    clamp_spec.ensures_2 value low high := by
  intro _
  simp only [Math.clamp_spec.ensures_2, Math.clamp]
  split
  · simp
  · split <;> simp

theorem clamp_spec_requires (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) :
    clamp_spec.requires value low high →
    clamp_spec.requires value low high := by
  intro h
  exact h

theorem distance_spec_aborts (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) :
    distance_spec.aborts a b = Option.none := by
  discharge_aborts [Math.distance_spec.aborts, Math.distance.aborts]

theorem distance_spec_ensures (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) :
    distance_spec.ensures a b := by
  simp only [Math.distance_spec.ensures, Math.distance, Bool.or_eq_true,
    decide_eq_true_eq, BoundedNat.le_def]
  split
  · rename_i hab
    rw [BoundedNat.sub_val a b hab]
    auto
  · rename_i hab
    have hle : a.val ≤ b.val := by auto
    rw [BoundedNat.sub_val b a hle]
    auto

theorem distance_spec_ensures_1 (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) :
    distance_spec.ensures_1 a b := by
  simp only [Math.distance_spec.ensures_1, Prover.implies,
    Bool.or_eq_true, Bool.not_eq_true', BoundedNat.beq_eq_decide,
    decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases hab : a = b
  · subst b
    right
    simp [Math.distance]
    apply BoundedNat.ext
    rw [BoundedNat.sub_val a a (Nat.le_refl _)]
    exact Nat.sub_self _
  · left
    exact hab

theorem distance_spec_ensures_2 (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) :
    distance_spec.ensures_2 a b := by
  simp only [Math.distance_spec.ensures_2, Prover.implies,
    Bool.or_eq_true, Bool.not_eq_true', BoundedNat.beq_eq_decide,
    decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases hzero : Math.distance a b = (0 : BoundedNat (2^64))
  · right
    unfold Math.distance at hzero
    split at hzero
    · rename_i hab
      apply BoundedNat.ext
      have hle : b.val ≤ a.val := by
        simp only [decide_eq_true_eq, BoundedNat.le_def, ge_iff_le] at hab
        exact hab
      have hval := congrArg BoundedNat.val hzero
      rw [BoundedNat.sub_val a b hle] at hval
      change a.val - b.val = 0 at hval
      have hrev : a.val ≤ b.val := Nat.sub_eq_zero_iff_le.mp hval
      auto
    · rename_i hab
      apply BoundedNat.ext
      have hle : a.val ≤ b.val := by
        simp only [BoundedNat.le_def, ge_iff_le] at hab
        auto
      have hval := congrArg BoundedNat.val hzero
      rw [BoundedNat.sub_val b a hle] at hval
      change b.val - a.val = 0 at hval
      have hrev : b.val ≤ a.val := Nat.sub_eq_zero_iff_le.mp hval
      auto
  · left
    exact hzero

theorem max_spec_aborts (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) :
    max_spec.aborts a b = Option.none := by
  simp [Math.max_spec.aborts, MoveAbort.orElse]

theorem max_spec_ensures (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) :
    max_spec.ensures a b := by
  simp only [Math.max_spec.ensures, Math.max, decide_eq_true_eq,
    BoundedNat.le_def]
  split <;> auto

theorem max_spec_ensures_1 (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) :
    max_spec.ensures_1 a b := by
  simp only [Math.max_spec.ensures_1, Math.max, decide_eq_true_eq,
    BoundedNat.le_def]
  split <;> auto

theorem max_spec_ensures_2 (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) :
    max_spec.ensures_2 a b := by
  simp only [Math.max_spec.ensures_2, Math.max]
  split <;> simp

theorem withdraw_spec_aborts (balance : Balance) (amount : BoundedNat (2^64)) :
    withdraw_spec.asserts_cond balance amount →
    Math.withdraw.aborts balance amount = Option.none := by
  discharge_aborts [Math.withdraw_spec.asserts_cond, Math.withdraw.aborts]

theorem withdraw_spec_ensures (balance : Balance) (amount : BoundedNat (2^64)) :
    withdraw_spec.asserts_cond balance amount →
    withdraw_spec.ensures balance amount := by
  intro _
  simp [Math.withdraw_spec.ensures]

theorem withdraw_spec_ensures_1 (balance : Balance) (amount : BoundedNat (2^64)) :
    withdraw_spec.asserts_cond balance amount →
    withdraw_spec.ensures_1 balance amount := by
  intro _
  simp [Math.withdraw_spec.ensures_1]

theorem transfer_spec_aborts (from_ : Balance) (to : Balance) (amount : BoundedNat (2^64)) :
    transfer_spec.asserts_cond from_ to amount →
    transfer_spec.asserts_cond_1 from_ to amount →
    Math.transfer.aborts from_ to amount = Option.none := by
  intros hfrom hto
  simp only [Math.transfer_spec.asserts_cond, Math.transfer_spec.asserts_cond_1,
    decide_eq_true_eq, BoundedNat.le_def] at hfrom hto
  have hamount_bound := amount.property
  have hamount_max : amount.val ≤ (18446744073709551615 : BoundedNat (2^64)).val := by
    rw [BoundedNat.val_u64_max]
    omega
  have hto_amount : to.value.val + amount.val < 2^64 := by
    rw [BoundedNat.sub_val _ _ hamount_max, BoundedNat.val_u64_max] at hto
    omega
  discharge_aborts [Math.transfer_spec.asserts_cond, Math.transfer_spec.asserts_cond_1,
    Math.transfer.aborts, Math.withdraw.aborts]

theorem transfer_spec_ensures (from_ : Balance) (to : Balance)
    (amount : BoundedNat (2^64)) :
    transfer_spec.asserts_cond from_ to amount →
    transfer_spec.asserts_cond_1 from_ to amount →
    transfer_spec.ensures from_ to amount := by
  intros
  simp [Math.transfer_spec.ensures]

theorem transfer_spec_ensures_1 (from_ : Balance) (to : Balance)
    (amount : BoundedNat (2^64)) :
    transfer_spec.asserts_cond from_ to amount →
    transfer_spec.asserts_cond_1 from_ to amount →
    transfer_spec.ensures_1 from_ to amount := by
  intros
  simp [Math.transfer_spec.ensures_1]

theorem transfer_spec_ensures_2 (from_ : Balance) (to : Balance)
    (amount : BoundedNat (2^64)) :
    transfer_spec.asserts_cond from_ to amount →
    transfer_spec.asserts_cond_1 from_ to amount →
    transfer_spec.ensures_2 from_ to amount := by
  intros hfrom hto
  simp only [Math.transfer_spec.asserts_cond, Math.transfer_spec.asserts_cond_1,
    decide_eq_true_eq, BoundedNat.le_def] at hfrom hto
  simp only [Math.transfer_spec.ensures_2, BoundedNat.beq_eq_decide,
    decide_eq_true_eq]
  apply BoundedNat.ext
  have hamount_bound := amount.property
  have hfrom_bound := from_.value.property
  have hto_bound := to.value.property
  have hamount_max : amount.val ≤ (18446744073709551615 : BoundedNat (2^64)).val := by
    rw [BoundedNat.val_u64_max]
    omega
  rw [BoundedNat.sub_val _ _ hamount_max, BoundedNat.val_u64_max] at hto
  have hto_amount : to.value.val + amount.val < 2^64 := by omega
  have hsub_val : (from_.value - amount).val = from_.value.val - amount.val :=
    BoundedNat.sub_val _ _ hfrom
  have hadd_val : (to.value + amount).val = to.value.val + amount.val :=
    BoundedNat.add_val _ _ hto_amount
  have hsub_cast :
      ((BoundedNat.convert (from_.value - amount) : BoundedNat (2^128))).val =
        (from_.value - amount).val :=
    BoundedNat.convert_val_of_lt _ (by have := (from_.value - amount).property; omega)
  have hadd_cast :
      ((BoundedNat.convert (to.value + amount) : BoundedNat (2^128))).val =
        (to.value + amount).val :=
    BoundedNat.convert_val_of_lt _ (by have := (to.value + amount).property; omega)
  have hfrom_cast :
      ((BoundedNat.convert from_.value : BoundedNat (2^128))).val = from_.value.val :=
    BoundedNat.convert_val_of_lt _ (by omega)
  have hto_cast :
      ((BoundedNat.convert to.value : BoundedNat (2^128))).val = to.value.val :=
    BoundedNat.convert_val_of_lt _ (by omega)
  have hpair_bound : (2^64 : Nat) + 2^64 < 2^128 := by decide
  have hleft_bound :
      (BoundedNat.convert (from_.value - amount) : BoundedNat (2^128)).val +
        (BoundedNat.convert (to.value + amount) : BoundedNat (2^128)).val < 2^128 := by
    rw [hsub_cast, hadd_cast, hsub_val, hadd_val]
    omega
  have hright_bound :
      (BoundedNat.convert from_.value : BoundedNat (2^128)).val +
        (BoundedNat.convert to.value : BoundedNat (2^128)).val < 2^128 := by
    rw [hfrom_cast, hto_cast]
    omega
  rw [BoundedNat.add_val _ _ hleft_bound, BoundedNat.add_val _ _ hright_bound,
    hsub_cast, hadd_cast, hfrom_cast, hto_cast, hsub_val, hadd_val]
  auto

end Math_proofs
