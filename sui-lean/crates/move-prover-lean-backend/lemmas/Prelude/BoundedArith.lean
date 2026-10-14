import Prelude.BoundedNat

/-
# BoundedArith

Abstract bridge lemmas + the `bounded_arith` tactic for discharging the
no-overflow / no-underflow / narrowing-cast guards that pepper `.aborts` proofs.

Each bridge lemma is stated over ABSTRACT `BoundedNat` vars plus a `Nat` bound
hypothesis and closed by the `BoundedNat.*` value lemmas + `omega`, per the
"prove over abstract vars, never whole-term simp/rw over heavy bodies" discipline.
The `bounded_arith` tactic selects the right bridge and discharges the operand-bound
side goal with `omega` against the hypotheses already in context.
-/

namespace BoundedNat

variable {bound : Nat}

/-- `add a b` does not overflow when the operand values sum below the bound. -/
@[simp] theorem add_overflows_false_of_bounds (a b : BoundedNat bound)
    (h : a.val + b.val < bound) : add_overflows a b = false := by
  simp only [add_overflows, decide_eq_false_iff_not]; omega

/-- `sub a b` does not underflow when `b ≤ a`. -/
@[simp] theorem sub_underflows_false_of_le (a b : BoundedNat bound)
    (h : b.val ≤ a.val) : sub_underflows a b = false := by
  simp only [sub_underflows, decide_eq_false_iff_not]; omega

/-- `mul a b` does not overflow when the operand product is below the bound. -/
@[simp] theorem mul_overflows_false_of_bounds (a b : BoundedNat bound)
    (h : a.val * b.val < bound) : mul_overflows a b = false := by
  simp only [mul_overflows, decide_eq_false_iff_not]; omega

/-- Narrowing-cast guard: a value below the target bound does not trip the
`x ≥ bound` overflow test. -/
theorem decide_ge_eq_false_of_lt {x b : Nat} (h : x < b) :
    decide (x ≥ b) = false := by
  rw [decide_eq_false_iff_not]; omega

/-- `convert a : BoundedNat bound_to` does not truncate when the value fits. -/
@[simp] theorem convert_overflows_false_of_lt {bound_from : Nat} (bound_to : Nat)
    (a : BoundedNat bound_from) (h : a.val < bound_to) :
    convert_overflows bound_to a = false := by
  simp only [convert_overflows, decide_eq_false_iff_not]; omega

end BoundedNat

/-- `bounded_arith` discharges a bounded-arithmetic guard goal of the form
`add_overflows/sub_underflows/mul_overflows _ _ = false` or a narrowing-cast
`decide (_ ≥ _) = false`, by selecting the matching bridge lemma and closing the
operand-bound side condition with `omega` against the hypotheses in context.
Leaf-targeted: it never reduces a heavy body, only the guard term.

Note on `mul_overflows`: the side goal `a.val * b.val < bound` is nonlinear, so
`omega` only closes it when a hypothesis already bounds the product (or an operand
is a literal). For the general product-of-bounded-operands case, supply the
product bound explicitly to `BoundedNat.mul_overflows_false_of_bounds`. -/
syntax (name := boundedArith) "bounded_arith" : tactic

macro_rules
  | `(tactic| bounded_arith) =>
    `(tactic|
      first
        | exact BoundedNat.add_overflows_false_of_bounds _ _ (by omega)
        | exact BoundedNat.sub_underflows_false_of_le _ _ (by omega)
        | exact BoundedNat.mul_overflows_false_of_bounds _ _ (by omega)
        | exact BoundedNat.decide_ge_eq_false_of_lt (by omega)
        | exact BoundedNat.convert_overflows_false_of_lt _ _ (by omega)
        | (simp only [BoundedNat.add_overflows, BoundedNat.sub_underflows,
              BoundedNat.convert_overflows,
              BoundedNat.lt_def, ge_iff_le, decide_eq_false_iff_not]; omega))

/-- `.val` of a numeral literal that fits its bound reduces to the numeral. The
`n < bound` side condition is discharged by `Nat.reduceLT` for concrete literals,
so `simp` normalizes e.g. `(18446744073709551615 : BoundedNat (2^64)).val` to the
bare `Nat` — letting `omega` see literal bounds in `.aborts` guards. -/
@[simp] theorem BoundedNat.val_ofNat_lt {bound n : Nat} [BoundedNat.BoundPos bound]
    [Decidable (n < bound)] (h : n < bound) :
    (OfNat.ofNat n : BoundedNat bound).val = n := by
  show (if h' : n < bound then (⟨n, h'⟩ : BoundedNat bound)
        else BoundedNat.ofNatJunk n BoundedNat.BoundPos.pos).val = n
  rw [dif_pos h]

/-- `.val` of the unsigned-max literals reduces to the numeral (by `rfl`/defeq).
`simp` won't perform this on its own — `OfNat.ofNat` stays folded so the instance
`if` is never exposed — so these are the explicit normal forms for the overflow
bounds that arithmetic `.aborts` guards compare against. -/
@[simp] theorem BoundedNat.val_u8_max : (255 : BoundedNat (2^8)).val = 255 := rfl
@[simp] theorem BoundedNat.val_u16_max : (65535 : BoundedNat (2^16)).val = 65535 := rfl
@[simp] theorem BoundedNat.val_u32_max : (4294967295 : BoundedNat (2^32)).val = 4294967295 := rfl
@[simp] theorem BoundedNat.val_u64_max :
    (18446744073709551615 : BoundedNat (2^64)).val = 18446744073709551615 := rfl
@[simp] theorem BoundedNat.val_u128_max :
    (340282366920938463463374607431768211455 : BoundedNat (2^128)).val
      = 340282366920938463463374607431768211455 := rfl

/-! Reward-split style division bounds over widened `u64 -> u128` operands, and
Int-cast value bridges. Extracted from the sui-staking suite (proven there per
client); stated over abstract `BoundedNat (2^64)` vars so the kernel never
reduces concrete arithmetic. -/

/-- `(a * b / c).val <= b.val` when `a <= c` (a proportional share of `b` never
exceeds `b`). Operands widened to `2^128`, so the product cannot overflow. -/
theorem BoundedNat.mul_div_le_right (a b c : BoundedNat (2^64))
    (hac : a.val ≤ c.val) (hc : c.val ≠ 0) :
    ((BoundedNat.convert a : BoundedNat (2^128)) * (BoundedNat.convert b : BoundedNat (2^128))
      / (BoundedNat.convert c : BoundedNat (2^128))).val ≤ b.val := by
  have hav : (BoundedNat.convert a : BoundedNat (2^128)).val = a.val :=
    BoundedNat.convert_val_of_lt _ (by have := a.property; omega)
  have hbv : (BoundedNat.convert b : BoundedNat (2^128)).val = b.val :=
    BoundedNat.convert_val_of_lt _ (by have := b.property; omega)
  have hcv : (BoundedNat.convert c : BoundedNat (2^128)).val = c.val :=
    BoundedNat.convert_val_of_lt _ (by have := c.property; omega)
  have hno : a.val * b.val < 2 ^ 128 := by
    have h1 : a.val ≤ 2^64 - 1 := by have := a.property; omega
    have h2 : b.val ≤ 2^64 - 1 := by have := b.property; omega
    have := Nat.mul_le_mul h1 h2
    have hlt : (2^64 - 1) * (2^64 - 1) < 2^128 := by decide
    omega
  rw [BoundedNat.div_val,
    BoundedNat.mul_val_of_no_overflow _ _ (by rw [hav, hbv]; exact hno), hav, hbv, hcv]
  calc a.val * b.val / c.val ≤ c.val * b.val / c.val :=
        Nat.div_le_div_right (Nat.mul_le_mul_right _ hac)
    _ = b.val := by rw [Nat.mul_comm, Nat.mul_div_cancel _ (by omega)]

/-- `(a * b / d).val <= a.val` when `b <= d` (a basis-point fraction of `a`
never exceeds `a`). Operands widened to `2^128`. -/
theorem BoundedNat.mul_div_le_left (a b d : BoundedNat (2^64))
    (hbd : b.val ≤ d.val) (hd : d.val ≠ 0) :
    ((BoundedNat.convert a : BoundedNat (2^128)) * (BoundedNat.convert b : BoundedNat (2^128))
      / (BoundedNat.convert d : BoundedNat (2^128))).val ≤ a.val := by
  have hav : (BoundedNat.convert a : BoundedNat (2^128)).val = a.val :=
    BoundedNat.convert_val_of_lt _ (by have := a.property; omega)
  have hbv : (BoundedNat.convert b : BoundedNat (2^128)).val = b.val :=
    BoundedNat.convert_val_of_lt _ (by have := b.property; omega)
  have hdv : (BoundedNat.convert d : BoundedNat (2^128)).val = d.val :=
    BoundedNat.convert_val_of_lt _ (by have := d.property; omega)
  have hno : a.val * b.val < 2 ^ 128 := by
    have h1 : a.val ≤ 2^64 - 1 := by have := a.property; omega
    have h2 : b.val ≤ 2^64 - 1 := by have := b.property; omega
    have := Nat.mul_le_mul h1 h2
    have hlt : (2^64 - 1) * (2^64 - 1) < 2^128 := by decide
    omega
  rw [BoundedNat.div_val,
    BoundedNat.mul_val_of_no_overflow _ _ (by rw [hav, hbv]; exact hno), hav, hbv, hdv]
  calc a.val * b.val / d.val ≤ a.val * d.val / d.val :=
        Nat.div_le_div_right (Nat.mul_le_mul_left _ hbd)
    _ = a.val := by rw [Nat.mul_div_cancel _ (by omega)]

/-- Int-cast value of a non-overflowing `u64` addition. -/
theorem BoundedNat.add_val_int (a b : BoundedNat (2^64))
    (h : a.val + b.val ≤ 18446744073709551615) :
    ((a + b).val : Int) = (a.val : Int) + (b.val : Int) := by
  have hlt : a.val + b.val < 2^64 := by
    have : (18446744073709551615 : Nat) < 2^64 := by decide
    omega
  rw [BoundedNat.add_val a b hlt]; omega

/-- Int-cast value of a non-underflowing `u64` subtraction. -/
theorem BoundedNat.sub_val_int (a b : BoundedNat (2^64)) (h : b.val ≤ a.val) :
    ((a - b).val : Int) = (a.val : Int) - (b.val : Int) := by
  rw [BoundedNat.sub_val a b h]; omega

/-- `bounded_omega` — one-call replacement for the ubiquitous
`simp only [BoundedNat.lt_def, decide_eq_true_eq, ...] at *; omega` dance:
normalizes `BoundedNat` comparisons, `decide` wrappers, and the overflow /
underflow guard predicates (goal and hypotheses) down to `Nat` facts on `.val`,
then closes with `omega`. Use for any goal that is pure bounded arithmetic once
projected to values. -/
macro "bounded_omega" : tactic =>
  `(tactic|
    (simp only [BoundedNat.lt_def, BoundedNat.le_def, BoundedNat.add_overflows,
       BoundedNat.sub_underflows, BoundedNat.mul_overflows,
       BoundedNat.convert_overflows, decide_eq_true_eq,
       decide_eq_false_iff_not, gt_iff_lt, ge_iff_le, Bool.not_eq_true,
       Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false] at *
     omega))
