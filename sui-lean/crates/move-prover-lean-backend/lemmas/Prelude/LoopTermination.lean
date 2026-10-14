import Prelude.BoundedNat

/-!
Reusable `decreasing_by` tactics for the common counter-loop shapes.

The generator never guesses a measure: every loop helper emits
`termination_by <name>.termination …` / `decreasing_by <macro>`, and the measure
+ decreasing proof are specified in Lean (in `Termination/<module>.lean`). For
the trivial counter loops the measure is a one-liner and the decreasing proof is
one of these combinators, so a per-loop Termination entry stays:

  def foo.while_0.termination (n i : BoundedNat (2^64)) (…) : Nat := n.val - i.val
  set_option hygiene false in
  macro "Module_foo_while_0_decreasing" : tactic =>
    `(tactic| bounded_forward foo.while_0.termination n)

Each tactic takes the measure def (to unfold) and, where a `+1` step can wrap,
the bound variable (its `.property` gives `< 2^64`). Both are named in Lean, so
the tactic stays shape-generic and nothing is guessed.

With honest arithmetic the `add_val_u64`/`sub_val` value lemmas are conditional
(no-overflow / no-underflow side conditions), so the second `simp_all` pass
discharges them with `omega` against the loop-guard facts normalized by the
first pass.
-/

-- Forward counter: guard `i < n`, step `i + 1`, measure `n.val - i.val`.
-- `n.property` rules out the `i + 1` wrap so the distance strictly drops.
syntax "bounded_forward " ident ppSpace term : tactic
macro_rules
  | `(tactic| bounded_forward $m $n) => `(tactic|
      all_goals (
        simp only [$m:ident]
        have _hb : ($n).val < 2 ^ 64 := ($n).property
        try simp_all (config := { zetaDelta := true }) only
          [id_eq, Bool.and_eq_true, BoundedNat.lt_def, BoundedNat.le_def,
           decide_eq_true_eq, gt_iff_lt, BoundedNat.val_one_u64]
        try simp (config := { zetaDelta := true })
          (disch := (try simp only [BoundedNat.val_one_u64]); omega) only
          [BoundedNat.add_val_u64, BoundedNat.sub_val, BoundedNat.val_one_u64] at *
        omega))

-- Backward counter: guard `i > 0`, step `i - 1`, measure `i.val`. The guard
-- rules out the `i - 1` underflow.
syntax "bounded_backward " ident : tactic
macro_rules
  | `(tactic| bounded_backward $m) => `(tactic|
      all_goals (
        simp only [$m:ident]
        try simp_all (config := { zetaDelta := true }) only
          [id_eq, Bool.and_eq_true, BoundedNat.lt_def, BoundedNat.le_def,
           decide_eq_true_eq, gt_iff_lt, BoundedNat.val_one_u64,
           show (0 : BoundedNat (2 ^ 64)).val = 0 from rfl]
        try simp (config := { zetaDelta := true })
          (disch := (try simp only [BoundedNat.val_one_u64,
             show (0 : BoundedNat (2 ^ 64)).val = 0 from rfl]); omega) only
          [BoundedNat.sub_val, BoundedNat.val_one_u64] at *
        omega))

-- Two-pointer convergence: guard `front < back`, steps `front + 1` / `back - 1`,
-- measure `back.val - front.val`. `back.property` rules out the `front + 1`
-- wrap; the guard rules out the `back - 1` underflow.
syntax "bounded_two_pointer " ident ppSpace term : tactic
macro_rules
  | `(tactic| bounded_two_pointer $m $back) => `(tactic|
      all_goals (
        simp only [$m:ident]
        have _hb : ($back).val < 2 ^ 64 := ($back).property
        try simp_all (config := { zetaDelta := true }) only
          [id_eq, Bool.and_eq_true, BoundedNat.lt_def, BoundedNat.le_def,
           decide_eq_true_eq, gt_iff_lt, BoundedNat.val_one_u64]
        try simp (config := { zetaDelta := true })
          (disch := (try simp only [BoundedNat.val_one_u64]); omega) only
          [BoundedNat.add_val_u64, BoundedNat.sub_val, BoundedNat.val_one_u64] at *
        omega))
