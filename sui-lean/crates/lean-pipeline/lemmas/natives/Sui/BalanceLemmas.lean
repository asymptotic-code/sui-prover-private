-- These lemmas reference framework `.aborts` companions (e.g.
-- `Balance.split.aborts`) that per-package pruning drops unless an importing
-- package actually uses those functions. The file is copied into every output
-- tree but imported by nobody, so `sui-lean --test` does not build it as a
-- standalone lake target. To import it from a client package, that package
-- must exercise the referenced `.aborts` functions (or a future force-retain
-- must keep them through pruning). See catalog item c1.
import Sui.Balance
import MoveStdlib.IntegerNatives

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem balance_split_aborts_no_abort_of_ge
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (balance : _root_.Prover.Mutation.Mutation K (_root_.Balance.Balance t))
    (amount : BoundedNat (2^64))
    (h_ge : BoundedNat.ge balance.val.value amount = true) :
    _root_.Balance.split.aborts t balance amount =
      _root_.Abort.AbortResult.NoAbort := by
  have h_ge_prop : amount.val ≤ balance.val.value.val := by
    unfold BoundedNat.ge at h_ge
    exact nat_le_of_bnot_blt_eq_true h_ge
  have h_sub_no_abort :
      BoundedNat.sub_aborts balance.val.value amount = false := by
    unfold BoundedNat.sub_aborts BoundedNat.sub_underflows
    exact nat_blt_eq_false (Nat.not_lt_of_ge h_ge_prop)
  simp [_root_.Balance.split.aborts,
    _root_.Prover.Mutation.Mutation.borrowField,
    _root_.Prover.Mutation.Mutation.set,
    _root_.Prover.Mutation.Mutation.updateValue,
    h_ge, h_sub_no_abort]

theorem balance_split_aborts_no_abort_of_ge_early
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (balance : _root_.Prover.Mutation.Mutation K (_root_.Balance.Balance t))
    (amount : BoundedNat (2^64))
    (h_ge : BoundedNat.ge balance.val.value amount = true) :
    _root_.Balance.split.aborts t balance amount =
      _root_.Abort.AbortResult.NoAbort :=
  balance_split_aborts_no_abort_of_ge t balance amount h_ge

theorem balance_split_ge_of_aborts_no_abort
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (balance : _root_.Prover.Mutation.Mutation K (_root_.Balance.Balance t))
    (amount : BoundedNat (2^64))
    (h_no_abort :
      _root_.Balance.split.aborts t balance amount =
        _root_.Abort.AbortResult.NoAbort) :
    BoundedNat.ge balance.val.value amount = true := by
  cases h_ge : BoundedNat.ge balance.val.value amount
  · simp [_root_.Balance.split.aborts, h_ge] at h_no_abort
  · rfl

theorem balance_split_taken_value_of_ge
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (balance : _root_.Prover.Mutation.Mutation K (_root_.Balance.Balance t))
    (amount : BoundedNat (2^64))
    (h_ge : BoundedNat.ge balance.val.value amount = true) :
    (_root_.Balance.split t balance amount).1.value = amount := by
  simp [_root_.Balance.split, h_ge]

theorem balance_split_remainder_value_val_of_ge
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (balance : _root_.Prover.Mutation.Mutation K (_root_.Balance.Balance t))
    (amount : BoundedNat (2^64))
    (h_ge : BoundedNat.ge balance.val.value amount = true) :
    (((_root_.Balance.split t balance amount).2.val.value.val : Nat) : Int) =
      _root_.Integer.sub
        (_root_.Integer.from_u64 balance.val.value)
        (_root_.Integer.from_u64 amount) := by
  have h_le : amount.val ≤ balance.val.value.val := by
    unfold BoundedNat.ge at h_ge
    exact nat_le_of_bnot_blt_eq_true h_ge
  simp [_root_.Balance.split,
    _root_.Prover.Mutation.Mutation.borrowField,
    _root_.Prover.Mutation.Mutation.set,
    _root_.Prover.Mutation.Mutation.updateValue,
    _root_.Integer.sub,
    _root_.Integer.from_u64,
    BoundedNat.sub,
    h_ge]
  omega

/- Supply operations are generated only for packages that exercise them.
Keep their lemmas in `Sui.BalanceSupplyLemmas` so importing the split/join
lemmas does not require supply declarations to survive package pruning.

theorem balance_decrease_supply_aborts_no_abort_of_ge
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (supply : _root_.Prover.Mutation.Mutation K (_root_.Balance.Supply t))
    (balance : _root_.Balance.Balance t)
    (h_ge : BoundedNat.ge supply.val.value balance.value = true) :
    _root_.Balance.decrease_supply.aborts t supply balance =
      _root_.Abort.AbortResult.NoAbort := by
  have h_ge_prop : balance.value.val ≤ supply.val.value.val := by
    unfold BoundedNat.ge at h_ge
    exact nat_le_of_bnot_blt_eq_true h_ge
  have h_le : BoundedNat.le balance.value supply.val.value = true := by
    unfold BoundedNat.le
    exact nat_ble_eq_true h_ge_prop
  have h_sub := boundedNat_sub_no_abort_of_le supply.val.value balance.value h_le
  simp [_root_.Balance.decrease_supply.aborts, h_ge, h_sub]
-/

@[simp]
theorem balance_join_snd_path
    {K T : Type} [DecidableEq T] [Inhabited T]
    (self : _root_.Prover.Mutation.Mutation K (_root_.Balance.Balance T))
    (balance : _root_.Balance.Balance T) :
    (_root_.Balance.join T self balance).2.path = self.path := by
  simp [_root_.Balance.join, _root_.Prover.Mutation.Mutation.borrowField,
    _root_.Prover.Mutation.Mutation.set,
    _root_.Prover.Mutation.Mutation.updateValue]

@[simp]
theorem balance_join_snd_loc
    {K T : Type} [DecidableEq T] [Inhabited T]
    (self : _root_.Prover.Mutation.Mutation K (_root_.Balance.Balance T))
    (balance : _root_.Balance.Balance T) :
    (_root_.Balance.join T self balance).2.loc = self.loc := by
  simp [_root_.Balance.join, _root_.Prover.Mutation.Mutation.borrowField,
    _root_.Prover.Mutation.Mutation.set,
    _root_.Prover.Mutation.Mutation.updateValue]

@[simp]
theorem balance_join_snd_value
    {K T : Type} [DecidableEq T] [Inhabited T]
    (self : _root_.Prover.Mutation.Mutation K (_root_.Balance.Balance T))
    (balance : _root_.Balance.Balance T) :
    (_root_.Balance.join T self balance).2.val.value =
      BoundedNat.add self.val.value balance.value := by
  simp [_root_.Balance.join, _root_.Prover.Mutation.Mutation.borrowField,
    _root_.Prover.Mutation.Mutation.set,
    _root_.Prover.Mutation.Mutation.updateValue]

theorem balance_join_aborts_no_abort_of_lte_max
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (balance : _root_.Prover.Mutation.Mutation K (_root_.Balance.Balance t))
    (added : _root_.Balance.Balance t)
    (h_lte :
      _root_.Integer.lte
        (_root_.Integer.add
          (_root_.Integer.from_u64 balance.val.value)
          (_root_.Integer.from_u64 added.value))
        (_root_.Integer.from_u64
          (18446744073709551615 : BoundedNat (2^64))) = true) :
    _root_.Balance.join.aborts t balance added =
      _root_.Abort.AbortResult.NoAbort := by
  have h_add_no_abort :
      BoundedNat.add_aborts balance.val.value added.value = false := by
    rw [boundedNat_u64_add_aborts_eq_not_integer_lte_max]
    simpa using h_lte
  simp [_root_.Balance.join.aborts,
    _root_.Prover.Mutation.Mutation.borrowField,
    _root_.Prover.Mutation.Mutation.set,
    _root_.Prover.Mutation.Mutation.updateValue,
    h_add_no_abort]

theorem balance_join_snd_value_val_of_lte_max
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (balance : _root_.Prover.Mutation.Mutation K (_root_.Balance.Balance t))
    (added : _root_.Balance.Balance t)
    (h_lte :
      _root_.Integer.lte
        (_root_.Integer.add
          (_root_.Integer.from_u64 balance.val.value)
          (_root_.Integer.from_u64 added.value))
        (_root_.Integer.from_u64
          (18446744073709551615 : BoundedNat (2^64))) = true) :
    (((_root_.Balance.join t balance added).2.val.value.val : Nat) : Int) =
      _root_.Integer.add
        (_root_.Integer.from_u64 balance.val.value)
        (_root_.Integer.from_u64 added.value) := by
  have h_add :=
    boundedNat_u64_add_val_int_of_integer_lte_max
      balance.val.value added.value (by simpa using h_lte)
  simpa [balance_join_snd_value] using h_add

theorem balance_join_lte_of_aborts_no_abort
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (balance : _root_.Prover.Mutation.Mutation K (_root_.Balance.Balance t))
    (added : _root_.Balance.Balance t)
    (h_no_abort :
      _root_.Balance.join.aborts t balance added =
        _root_.Abort.AbortResult.NoAbort) :
    _root_.Integer.lte
      (_root_.Integer.add
        (_root_.Integer.from_u64 balance.val.value)
        (_root_.Integer.from_u64 added.value))
      (_root_.Integer.from_u64
        (18446744073709551615 : BoundedNat (2^64))) := by
  have h_add_no_abort :
      BoundedNat.add_aborts balance.val.value added.value = false := by
    cases h_add : BoundedNat.add_aborts balance.val.value added.value
    · rfl
    · simp [_root_.Balance.join.aborts, h_add] at h_no_abort
  have h_lt :
      balance.val.value.val + added.value.val < 18446744073709551616 := by
    simpa [boundedNat_u64_add_aborts_eq_not_integer_lte_max]
      using h_add_no_abort
  have h_max :
      (18446744073709551615 : BoundedNat (2^64)).val =
        18446744073709551615 := by
    rfl
  have h_lte_nat :
      balance.val.value.val + added.value.val ≤ 18446744073709551615 := by
    omega
  have h_lte_int :
      (balance.val.value.val : Int) + (added.value.val : Int) ≤
        (18446744073709551615 : Int) := by
    rw [← Int.natCast_add]
    exact Int.ofNat_le.mpr h_lte_nat
  change (balance.val.value.val : Int) + (added.value.val : Int) ≤
    ((18446744073709551615 : BoundedNat (2^64)).val : Int)
  rw [h_max]
  exact h_lte_int

/- See `Sui.BalanceSupplyLemmas`.

theorem balance_increase_supply_aborts_no_abort_of_lte_max
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (self : _root_.Prover.Mutation.Mutation K (_root_.Balance.Supply t))
    (value : BoundedNat (2^64))
    (h_lte :
      _root_.Integer.lte
        (_root_.Integer.add
          (_root_.Integer.from_u64 self.val.value)
          (_root_.Integer.from_u64 value))
        (_root_.Integer.from_u64
          (18446744073709551615 : BoundedNat (2^64))) = true) :
    _root_.Balance.increase_supply.aborts t self value =
      _root_.Abort.AbortResult.NoAbort := by
  let max : BoundedNat (2^64) :=
    _root_.Balance.large_uint_u64_18446744073709551615
  have h_lte_int :
      (self.val.value.val : Int) + (value.val : Int) ≤ (max.val : Int) := by
    have h_raw_max :
        (18446744073709551615 : BoundedNat (2^64)).val =
          18446744073709551615 := by
      rfl
    have h_lte_raw :
        (self.val.value.val : Int) + (value.val : Int) ≤
          (18446744073709551615 : Int) := by
      simpa [_root_.Integer.lte, _root_.Integer.add,
        _root_.Integer.from_u64, h_raw_max] using h_lte
    simpa [max, _root_.Balance.large_uint_u64_18446744073709551615_val]
      using h_lte_raw
  have h_self_le_max : self.val.value.val ≤ max.val := by
    have h_value_nonneg : (0 : Int) ≤ value.val := Int.natCast_nonneg _
    exact Int.ofNat_le.mp (by omega)
  have h_sub_no_abort :
      BoundedNat.sub_aborts max self.val.value = false := by
    unfold BoundedNat.sub_aborts BoundedNat.sub_underflows
    exact nat_blt_eq_false (Nat.not_lt_of_ge h_self_le_max)
  have h_le_sub :
      BoundedNat.le value (BoundedNat.sub max self.val.value) = true := by
    unfold BoundedNat.le
    apply nat_ble_eq_true
    simp [BoundedNat.sub]
    omega
  have h_add_no_abort :
      BoundedNat.add_aborts self.val.value value = false := by
    rw [boundedNat_u64_add_aborts_eq_not_integer_lte_max]
    simpa [max] using h_lte
  simp [_root_.Balance.increase_supply.aborts,
    _root_.Prover.Mutation.Mutation.borrowField,
    _root_.Prover.Mutation.Mutation.set,
    _root_.Prover.Mutation.Mutation.updateValue,
    max, h_sub_no_abort, h_le_sub, h_add_no_abort]

theorem balance_increase_supply_lte_of_aborts_no_abort
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (self : _root_.Prover.Mutation.Mutation K (_root_.Balance.Supply t))
    (value : BoundedNat (2^64))
    (h_no_abort :
      _root_.Balance.increase_supply.aborts t self value =
        _root_.Abort.AbortResult.NoAbort) :
    _root_.Integer.lte
      (_root_.Integer.add
        (_root_.Integer.from_u64 self.val.value)
        (_root_.Integer.from_u64 value))
      (_root_.Integer.from_u64
        (18446744073709551615 : BoundedNat (2^64))) := by
  let max : BoundedNat (2^64) :=
    _root_.Balance.large_uint_u64_18446744073709551615
  have h_sub_no_abort :
      BoundedNat.sub_aborts max self.val.value = false := by
    cases h_sub : BoundedNat.sub_aborts max self.val.value
    · rfl
    · simp [_root_.Balance.increase_supply.aborts, max, h_sub]
        at h_no_abort
  have h_le :
      BoundedNat.le value (BoundedNat.sub max self.val.value) = true := by
    cases h_le : BoundedNat.le value (BoundedNat.sub max self.val.value)
    · simp [_root_.Balance.increase_supply.aborts, max, h_sub_no_abort,
        h_le] at h_no_abort
    · rfl
  have h_add_no_abort :
      BoundedNat.add_aborts self.val.value value = false := by
    cases h_add : BoundedNat.add_aborts self.val.value value
    · rfl
    · simp [_root_.Balance.increase_supply.aborts, max, h_sub_no_abort,
        h_le, h_add] at h_no_abort
  have h_lt :
      self.val.value.val + value.val < 18446744073709551616 := by
    simpa [boundedNat_u64_add_aborts_eq_not_integer_lte_max, max]
      using h_add_no_abort
  have h_lte_nat :
      self.val.value.val + value.val ≤ 18446744073709551615 := by
    omega
  have h_lte_int :
      (self.val.value.val : Int) + (value.val : Int) ≤
        (18446744073709551615 : Int) := by
    rw [← Int.natCast_add]
    exact Int.ofNat_le.mpr h_lte_nat
  have h_raw_max :
      (18446744073709551615 : BoundedNat (2^64)).val =
        18446744073709551615 := by
    rfl
  change (self.val.value.val : Int) + (value.val : Int) ≤
    ((18446744073709551615 : BoundedNat (2^64)).val : Int)
  rw [h_raw_max]
  exact h_lte_int

theorem balance_increase_supply_balance_value_of_lte_max
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (self : _root_.Prover.Mutation.Mutation K (_root_.Balance.Supply t))
    (value : BoundedNat (2^64))
    (h_lte :
      _root_.Integer.lte
        (_root_.Integer.add
          (_root_.Integer.from_u64 self.val.value)
          (_root_.Integer.from_u64 value))
        (_root_.Integer.from_u64
          (18446744073709551615 : BoundedNat (2^64))) = true) :
    (_root_.Balance.increase_supply t self value).1.value = value := by
  let max : BoundedNat (2^64) :=
    _root_.Balance.large_uint_u64_18446744073709551615
  have h_lte_int :
      (self.val.value.val : Int) + (value.val : Int) ≤ (max.val : Int) := by
    have h_raw_max :
        (18446744073709551615 : BoundedNat (2^64)).val =
          18446744073709551615 := by
      rfl
    have h_lte_raw :
        (self.val.value.val : Int) + (value.val : Int) ≤
          (18446744073709551615 : Int) := by
      simpa [_root_.Integer.lte, _root_.Integer.add,
        _root_.Integer.from_u64, h_raw_max] using h_lte
    simpa [max, _root_.Balance.large_uint_u64_18446744073709551615_val]
      using h_lte_raw
  have h_le_sub :
      BoundedNat.le value (BoundedNat.sub max self.val.value) = true := by
    unfold BoundedNat.le
    apply nat_ble_eq_true
    simp [BoundedNat.sub]
    omega
  simp [_root_.Balance.increase_supply, max, h_le_sub]

theorem balance_increase_supply_value_val_of_lte_max
    {K : Type} (t : Type) [DecidableEq t] [Inhabited t]
    (self : _root_.Prover.Mutation.Mutation K (_root_.Balance.Supply t))
    (value : BoundedNat (2^64))
    (h_lte :
      _root_.Integer.lte
        (_root_.Integer.add
          (_root_.Integer.from_u64 self.val.value)
          (_root_.Integer.from_u64 value))
        (_root_.Integer.from_u64
          (18446744073709551615 : BoundedNat (2^64))) = true) :
    ((_root_.Balance.increase_supply t self value).2.val.value.val : Int) =
      _root_.Integer.add
        (_root_.Integer.from_u64 self.val.value)
        (_root_.Integer.from_u64 value) := by
  let max : BoundedNat (2^64) :=
    _root_.Balance.large_uint_u64_18446744073709551615
  have h_lte_int :
      (self.val.value.val : Int) + (value.val : Int) ≤ (max.val : Int) := by
    have h_raw_max :
        (18446744073709551615 : BoundedNat (2^64)).val =
          18446744073709551615 := by
      rfl
    have h_lte_raw :
        (self.val.value.val : Int) + (value.val : Int) ≤
          (18446744073709551615 : Int) := by
      simpa [_root_.Integer.lte, _root_.Integer.add,
        _root_.Integer.from_u64, h_raw_max] using h_lte
    simpa [max, _root_.Balance.large_uint_u64_18446744073709551615_val]
      using h_lte_raw
  have h_self_le_max : self.val.value.val ≤ max.val := by
    have h_value_nonneg : (0 : Int) ≤ value.val := Int.natCast_nonneg _
    exact Int.ofNat_le.mp (by omega)
  have h_sub_no_abort :
      BoundedNat.sub_aborts max self.val.value = false := by
    unfold BoundedNat.sub_aborts BoundedNat.sub_underflows
    exact nat_blt_eq_false (Nat.not_lt_of_ge h_self_le_max)
  have h_le_sub :
      BoundedNat.le value (BoundedNat.sub max self.val.value) = true := by
    unfold BoundedNat.le
    apply nat_ble_eq_true
    simp [BoundedNat.sub]
    omega
  have h_add_val :=
    have h_lte_prop :
        _root_.Integer.lte
          (_root_.Integer.add
            (_root_.Integer.from_u64 self.val.value)
            (_root_.Integer.from_u64 value))
          (_root_.Integer.from_u64
            (18446744073709551615 : BoundedNat (2^64))) := by
      simpa using h_lte
    boundedNat_u64_add_val_int_of_integer_lte_max
      self.val.value value h_lte_prop
  simp [_root_.Balance.increase_supply,
    _root_.Prover.Mutation.Mutation.borrowField,
    _root_.Prover.Mutation.Mutation.set,
    _root_.Prover.Mutation.Mutation.updateValue,
    max, h_le_sub, h_add_val]
-/

/-! ## Shared `Balance.join` characterization

`balance_join_aborts_no_abort_of_lte_max` and `balance_join_lte_of_aborts_no_abort`
are the two halves; the iff is what obligations actually consume. Namespaced
per the standing rule in `plans/lean-pipeline/shared-proof-infra.md`. -/

namespace BalanceEffects

theorem join_aborts_no_abort_iff_lte_max {K : Type} (t : Type)
    [DecidableEq t] [Inhabited t]
    (balance : _root_.Prover.Mutation.Mutation K (_root_.Balance.Balance t))
    (added : _root_.Balance.Balance t) :
    _root_.Balance.join.aborts t balance added =
        _root_.Abort.AbortResult.NoAbort ↔
      _root_.Integer.lte
        (_root_.Integer.add
          (_root_.Integer.from_u64 balance.val.value)
          (_root_.Integer.from_u64 added.value))
        (_root_.Integer.from_u64
          (18446744073709551615 : BoundedNat (2^64))) := by
  constructor
  · intro h_no_abort
    have h_add_no_abort :
        BoundedNat.add_aborts balance.val.value added.value = false := by
      cases h_add : BoundedNat.add_aborts balance.val.value added.value
      · rfl
      · simp [_root_.Balance.join.aborts, h_add] at h_no_abort
    rw [boundedNat_u64_add_aborts_eq_not_integer_lte_max] at h_add_no_abort
    simpa using h_add_no_abort
  · intro h_lte
    exact balance_join_aborts_no_abort_of_lte_max t balance added
      (by simpa using h_lte)

end BalanceEffects
