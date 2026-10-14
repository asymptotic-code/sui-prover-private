-- Loop summaries for the GENERATED `std::u64::pow` (`MoveStdlib/U64.lean`).
--
-- `U64.pow.while_0` and `U64.pow.aborts.while_0` are `partial_fixpoint`
-- definitions: their bodies reach `Lean.Order.fix`, so `move_auto`'s discovery
-- ladder SEALS them out of the unfold channel (unfolding reintroduces the
-- recursive occurrence and burns the whole heartbeat budget). A leaf touching a
-- power can therefore only close from facts ABOUT the loop. This file is those
-- facts.
--
-- `U64.pow.while_0 base exp acc` is Move's square-and-multiply loop: while
-- `exp >= 1`, either square the base and halve the exponent (even `exp`) or fold
-- the base into the accumulator and decrement (odd `exp`). Because
-- `BoundedNat.mul` is `(a * b) % bound` and `%` is a ring homomorphism, the
-- loop's VALUE is unconditional modular exponentiation -- no abort hypothesis is
-- needed:
--
--     (U64.pow.while_0 base exp acc).val = acc.val * base.val ^ exp.val % 2^64
--
-- The abort twin is what carries the u64 overflow condition. Every intermediate
-- square / multiply is dominated by the final `acc * base ^ exp` (for a nonzero
-- accumulator), so the loop aborts on exactly the mathematical overflow:
--
--     U64.pow.aborts base exp = NoAbort  <->  base.val ^ exp.val < 2^64
--
-- Naming (load-bearing): `move_auto`'s carrier-fact harvest indexes theorems by
-- the loop helpers in their statement but SKIPS any theorem having the carrier as
-- a name prefix. Everything public here lives in `U64Pow`, never under
-- `U64.pow.while_0` / `U64.pow.aborts.while_0`, so the harvest can see it.
--
-- No `sorry`, no `native_decide`, no new axioms -- kernel-checked throughout.
-- (The pre-existing `native_decide` oracles in client overlays, e.g. ember's
-- `oracle_pow10_no_abort_of_le_19`, are exactly what these replace.)
--
-- WIRING. `<Lib>/<Module>Lemmas.lean` under `lemmas/natives/` is the lemma
-- COMPANION of the module `<Lib>.<Module>`: this file's subject is
-- `MoveStdlib.U64`, derivable from its name alone. `render`
-- (`render/lemma_companions.rs`) copies it to `<output>/MoveStdlib/` and emits
-- `import MoveStdlib.U64Lemmas` into every generated module that imports
-- `MoveStdlib.U64` -- but ONLY where the constants it needs (`U64.pow` and its
-- loop helpers) survive tree-shaking. A corpus whose `std::u64` is shaken down
-- to `min`/`max` (bluefin, cetus) gets neither the copy nor the import, so the
-- blanket import that would fail elaboration there never happens.
-- `move_auto`'s harvest folds over `env.constants` -- i.e. imported modules
-- only -- which is what the emitted import buys.
--
-- MEASURED (round 8, ember Vault_specs_Proofs.Calculations, budget-fixed
-- move_auto ladder). Same ladder, summary present vs absent, on the four
-- pow-shaped leaf goals:
--   * `(U64.pow b e).val = b.val ^ e.val` given no-abort:  FAIL 8.1s -> CLOSED
--     44ms, replay `move_auto (solver := simp) (rung := all) only []` -- i.e.
--     through the ambient `move_effect` registry.
--   * `(U64.pow.while_0 b e a).val = a.val * b.val ^ e.val % 2^64`: FAIL 10.3s
--     -> CLOSED 83s, replay `... only [U64Pow.pow_while_val] ...` -- the
--     carrier-fact harvest citing this file by name.
--   * `U64.pow.aborts b e = NoAbort` from `e.val <= 19`, and `0 < (U64.pow b
--     e).val`: still refused BOTH ways. The loop is no longer the blocker; the
--     residual one is the monotone bound `10 ^ n < 2^64` from `n <= 19`, which
--     no rung on the ladder (omega/grind/Z3) can produce. `pow_no_abort_of_lt`
--     / `pow_no_abort_of_le_of_le` below are the hand-off for that: instantiate
--     the numerals and the leaf closes without `native_decide`.
import MoveStdlib.U64
import Prover.MoveAutoAttr

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace U64Pow

/-! ## Nat-level modular-arithmetic plumbing -/

private theorem mod_mod_eq (x m : Nat) (hm : 0 < m) : x % m % m = x % m :=
  Nat.mod_eq_of_lt (Nat.mod_lt x hm)

private theorem mul_congr_mod (a y z m : Nat) (h : y % m = z % m) :
    a * y % m = a * z % m := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod]

private theorem mul_left_congr_mod (y z c m : Nat) (h : y % m = z % m) :
    y * c % m = z * c % m := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod]

private theorem pow_mod_inner (x k m : Nat) (hm : 0 < m) :
    (x % m) ^ k % m = x ^ k % m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod ((x % m) ^ k) (x % m) m, ih,
      mod_mod_eq x m hm, Nat.mul_mod (x ^ k) x m]

private theorem sq_eq (b : Nat) : b * b = b ^ 2 := by
  rw [Nat.pow_succ, Nat.pow_one]

private theorem even_pow_regroup (b k e : Nat) (he : 2 * k = e) : (b * b) ^ k = b ^ e := by
  rw [sq_eq, ← Nat.pow_mul, he]

private theorem odd_pow_regroup (a b k : Nat) : a * b * b ^ k = a * b ^ (k + 1) := by
  rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm b (b ^ k)]

private theorem even_step (a b m k e : Nat) (hm : 0 < m) (he : 2 * k = e) :
    a * (b * b % m) ^ k % m = a * b ^ e % m := by
  rw [mul_congr_mod a _ _ m (pow_mod_inner (b * b) k m hm), even_pow_regroup b k e he]

private theorem odd_step (a b m k : Nat) (hm : 0 < m) :
    a * b % m * b ^ k % m = a * b ^ (k + 1) % m := by
  rw [mul_left_congr_mod _ _ _ m (mod_mod_eq (a * b) m hm), odd_pow_regroup]

private theorem nat_strong_ind {P : Nat → Prop}
    (step : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  have aux : ∀ b n, n < b → P n := by
    intro b
    induction b with
    | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
    | succ b ihb => intro n _; exact step n (fun m hm => ihb m (by omega))
  intro n
  exact aux (n + 1) n (Nat.lt_succ_self n)

/-! ## `BoundedNat` projections at the literals the loop uses -/

private theorem u8_one_val : (1 : BoundedNat (2^8)).val = 1 := rfl
private theorem u8_two_val : (2 : BoundedNat (2^8)).val = 2 := rfl
private theorem u8_zero_val : (0 : BoundedNat (2^8)).val = 0 := rfl
private theorem u64_one_val : (1 : BoundedNat (2^64)).val = 1 := rfl

private theorem bound64_pos : 0 < 2^64 := BoundedNat.bound_pos_64

private theorem mul_val (a b : BoundedNat (2^64)) :
    (BoundedNat.mul a b).val = a.val * b.val % 2^64 := by
  simp only [BoundedNat.mul, bound64_pos, ↓reduceDIte]

private theorem mod_two_val (e : BoundedNat (2^8)) :
    (BoundedNat.mod e (2 : BoundedNat (2^8))).val = e.val % 2 := rfl

private theorem div_two_val (e : BoundedNat (2^8)) :
    (BoundedNat.div e (2 : BoundedNat (2^8))).val = e.val / 2 := rfl

private theorem sub_one_val (e : BoundedNat (2^8)) :
    (BoundedNat.sub e (1 : BoundedNat (2^8))).val = e.val - 1 := rfl

private theorem ge_one_true {e : BoundedNat (2^8)} (h : 1 ≤ e.val) :
    BoundedNat.ge e (1 : BoundedNat (2^8)) = true :=
  nat_bnot_blt_eq_true_of_le (by rw [u8_one_val]; exact h)

private theorem ge_one_false {e : BoundedNat (2^8)} (h : e.val = 0) :
    BoundedNat.ge e (1 : BoundedNat (2^8)) = false :=
  not_blt_eq_false_of_lt (by rw [u8_one_val]; omega)

private theorem even_true {e : BoundedNat (2^8)} (h : e.val % 2 = 0) :
    BoundedNat.eq (BoundedNat.mod e (2 : BoundedNat (2^8))) (0 : BoundedNat (2^8)) = true :=
  nat_beq_eq_true_of_eq (by rw [mod_two_val, u8_zero_val]; exact h)

private theorem even_false {e : BoundedNat (2^8)} (h : e.val % 2 ≠ 0) :
    BoundedNat.eq (BoundedNat.mod e (2 : BoundedNat (2^8))) (0 : BoundedNat (2^8)) = false :=
  nat_beq_eq_false_of_ne (by rw [mod_two_val, u8_zero_val]; exact h)

private theorem mod_two_no_abort (e : BoundedNat (2^8)) :
    BoundedNat.mod_aborts e (2 : BoundedNat (2^8)) = false := rfl

private theorem div_two_no_abort (e : BoundedNat (2^8)) :
    BoundedNat.div_aborts e (2 : BoundedNat (2^8)) = false := rfl

private theorem sub_one_no_abort {e : BoundedNat (2^8)} (h : 1 ≤ e.val) :
    BoundedNat.sub_aborts e (1 : BoundedNat (2^8)) = false :=
  nat_blt_eq_false (by rw [u8_one_val]; omega)

/-! ## Unfolding the two `partial_fixpoint` loops one step

`partial_fixpoint` supplies `.eq_def` (the fixpoint equation, proven from
monotonicity); these three shapes turn it into Nat-conditioned steps. -/

private theorem while_step_zero (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (acc : BoundedNat (2^64)) (h : e.val = 0) :
    U64.pow.while_0 base e acc = acc := by
  rw [U64.pow.while_0.eq_def]
  simp only [ge_one_false h, Bool.false_eq_true, if_false, U64.pow.while_0.after]

private theorem while_step_even (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (acc : BoundedNat (2^64)) (hge : 1 ≤ e.val) (hev : e.val % 2 = 0) :
    U64.pow.while_0 base e acc =
      U64.pow.while_0 (BoundedNat.mul base base)
        (BoundedNat.div e (2 : BoundedNat (2^8))) acc := by
  rw [U64.pow.while_0.eq_def]
  simp only [ge_one_true hge, even_true hev, if_true]

private theorem while_step_odd (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (acc : BoundedNat (2^64)) (hge : 1 ≤ e.val) (hod : e.val % 2 ≠ 0) :
    U64.pow.while_0 base e acc =
      U64.pow.while_0 base (BoundedNat.sub e (1 : BoundedNat (2^8)))
        (BoundedNat.mul acc base) := by
  rw [U64.pow.while_0.eq_def]
  simp only [ge_one_true hge, even_false hod, Bool.false_eq_true, if_false, if_true]

private theorem aborts_step_zero (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (acc : BoundedNat (2^64)) (h : e.val = 0) :
    U64.pow.aborts.while_0 base e acc = Abort.AbortResult.NoAbort := by
  rw [U64.pow.aborts.while_0.eq_def]
  simp only [ge_one_false h, Bool.false_eq_true, if_false, U64.pow.aborts.while_0.after]

private theorem aborts_step_even (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (acc : BoundedNat (2^64)) (hge : 1 ≤ e.val) (hev : e.val % 2 = 0) :
    U64.pow.aborts.while_0 base e acc =
      if BoundedNat.mul_aborts base base = true then
        Abort.AbortResult.Aborted { code := (0 : BoundedNat (2^64)) }
      else
        U64.pow.aborts.while_0 (BoundedNat.mul base base)
          (BoundedNat.div e (2 : BoundedNat (2^8))) acc := by
  rw [U64.pow.aborts.while_0.eq_def]
  simp only [ge_one_true hge, even_true hev, mod_two_no_abort,
    Bool.false_eq_true, if_false, if_true]

private theorem aborts_step_odd (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (acc : BoundedNat (2^64)) (hge : 1 ≤ e.val) (hod : e.val % 2 ≠ 0) :
    U64.pow.aborts.while_0 base e acc =
      if BoundedNat.mul_aborts acc base = true then
        Abort.AbortResult.Aborted { code := (0 : BoundedNat (2^64)) }
      else
        U64.pow.aborts.while_0 base (BoundedNat.sub e (1 : BoundedNat (2^8)))
          (BoundedNat.mul acc base) := by
  rw [U64.pow.aborts.while_0.eq_def]
  simp only [ge_one_true hge, even_false hod, mod_two_no_abort, sub_one_no_abort hge,
    Bool.false_eq_true, if_false, if_true]

/-! ## The value summary

Unconditional: `BoundedNat.mul` wraps, and wrapping at every step agrees with
wrapping once at the end. -/

private theorem while_val_aux : ∀ (n : Nat) (base : BoundedNat (2^64))
    (e : BoundedNat (2^8)) (acc : BoundedNat (2^64)), e.val = n →
    (U64.pow.while_0 base e acc).val = acc.val * base.val ^ e.val % 2^64 := by
  refine nat_strong_ind (P := fun n => ∀ (base : BoundedNat (2^64))
    (e : BoundedNat (2^8)) (acc : BoundedNat (2^64)), e.val = n →
    (U64.pow.while_0 base e acc).val = acc.val * base.val ^ e.val % 2^64) ?_
  intro n ih base e acc hn
  by_cases hge : 1 ≤ e.val
  · by_cases hev : e.val % 2 = 0
    · rw [while_step_even base e acc hge hev,
        ih (e.val / 2) (by omega) (BoundedNat.mul base base)
          (BoundedNat.div e (2 : BoundedNat (2^8))) acc (by rw [div_two_val]),
        div_two_val, mul_val]
      exact even_step acc.val base.val (2^64) (e.val / 2) e.val bound64_pos (by omega)
    · rw [while_step_odd base e acc hge hev,
        ih (e.val - 1) (by omega) base
          (BoundedNat.sub e (1 : BoundedNat (2^8))) (BoundedNat.mul acc base)
          (by rw [sub_one_val]),
        sub_one_val, mul_val]
      have hk : e.val - 1 + 1 = e.val := by omega
      rw [← hk]
      exact odd_step acc.val base.val (2^64) (e.val - 1) bound64_pos
  · have h0 : e.val = 0 := by omega
    rw [while_step_zero base e acc h0, h0, Nat.pow_zero, Nat.mul_one,
      Nat.mod_eq_of_lt acc.property]

/-- The loop's value is modular exponentiation: `acc * base ^ exp` mod `2^64`.
Unconditional -- no no-abort hypothesis. -/
theorem pow_while_val (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (acc : BoundedNat (2^64)) :
    (U64.pow.while_0 base e acc).val = acc.val * base.val ^ e.val % 2^64 :=
  while_val_aux e.val base e acc rfl

/-- `U64.pow` is the loop started at `acc = 1`. -/
theorem pow_unfold (base : BoundedNat (2^64)) (e : BoundedNat (2^8)) :
    U64.pow base e = U64.pow.while_0 base e (1 : BoundedNat (2^64)) := rfl

/-- `U64.pow.aborts` is the abort loop started at `acc = 1`. -/
theorem pow_aborts_unfold (base : BoundedNat (2^64)) (e : BoundedNat (2^8)) :
    U64.pow.aborts base e = U64.pow.aborts.while_0 base e (1 : BoundedNat (2^64)) := rfl

/-- The `acc = 1` specialization of `pow_while_val`, hypothesis-free, so the
harvest can apply it as a plain rewrite after `pow_unfold`. -/
theorem pow_while_one_val (base : BoundedNat (2^64)) (e : BoundedNat (2^8)) :
    (U64.pow.while_0 base e (1 : BoundedNat (2^64))).val = base.val ^ e.val % 2^64 := by
  rw [pow_while_val, u64_one_val, Nat.one_mul]

/-- Value of `U64.pow`: modular exponentiation. -/
@[move_effect] theorem pow_val (base : BoundedNat (2^64)) (e : BoundedNat (2^8)) :
    (U64.pow base e).val = base.val ^ e.val % 2^64 := by
  rw [pow_unfold, pow_while_one_val]

/-! ## The abort summary -/

private theorem aborts_of_base_zero : ∀ (n : Nat) (base : BoundedNat (2^64))
    (e : BoundedNat (2^8)) (acc : BoundedNat (2^64)), e.val = n → base.val = 0 →
    U64.pow.aborts.while_0 base e acc = Abort.AbortResult.NoAbort := by
  refine nat_strong_ind (P := fun n => ∀ (base : BoundedNat (2^64))
    (e : BoundedNat (2^8)) (acc : BoundedNat (2^64)), e.val = n → base.val = 0 →
    U64.pow.aborts.while_0 base e acc = Abort.AbortResult.NoAbort) ?_
  intro n ih base e acc hn hb
  by_cases hge : 1 ≤ e.val
  · by_cases hev : e.val % 2 = 0
    · rw [aborts_step_even base e acc hge hev,
        if_neg (by
          rw [BoundedNat.mul_aborts_eq_false_of_lt base base
            (by rw [hb, Nat.zero_mul]; exact bound64_pos)]
          simp)]
      exact ih (e.val / 2) (by omega) (BoundedNat.mul base base)
        (BoundedNat.div e (2 : BoundedNat (2^8))) acc (by rw [div_two_val])
        (by rw [mul_val, hb])
    · rw [aborts_step_odd base e acc hge hev,
        if_neg (by
          rw [BoundedNat.mul_aborts_eq_false_of_lt acc base
            (by rw [hb, Nat.mul_zero]; exact bound64_pos)]
          simp)]
      exact ih (e.val - 1) (by omega) base
        (BoundedNat.sub e (1 : BoundedNat (2^8))) (BoundedNat.mul acc base)
        (by rw [sub_one_val]) hb
  · exact aborts_step_zero base e acc (by omega)

private theorem aborts_aux : ∀ (n : Nat) (base : BoundedNat (2^64))
    (e : BoundedNat (2^8)) (acc : BoundedNat (2^64)), e.val = n → 0 < acc.val →
    U64.pow.aborts.while_0 base e acc =
      if acc.val * base.val ^ e.val < 2^64 then Abort.AbortResult.NoAbort
      else Abort.AbortResult.Aborted { code := (0 : BoundedNat (2^64)) } := by
  refine nat_strong_ind (P := fun n => ∀ (base : BoundedNat (2^64))
    (e : BoundedNat (2^8)) (acc : BoundedNat (2^64)), e.val = n → 0 < acc.val →
    U64.pow.aborts.while_0 base e acc =
      if acc.val * base.val ^ e.val < 2^64 then Abort.AbortResult.NoAbort
      else Abort.AbortResult.Aborted { code := (0 : BoundedNat (2^64)) }) ?_
  intro n ih base e acc hn ha
  by_cases hb : 0 < base.val
  case neg =>
    have hb0 : base.val = 0 := by omega
    rw [aborts_of_base_zero e.val base e acc rfl hb0, if_pos]
    by_cases he0 : e.val = 0
    · rw [he0, Nat.pow_zero, Nat.mul_one]; exact acc.property
    · rw [hb0, Nat.zero_pow (show 0 < e.val by omega), Nat.mul_zero]; exact bound64_pos
  case pos =>
  by_cases hge : 1 ≤ e.val
  · by_cases hev : e.val % 2 = 0
    · have h2 : 2 ≤ e.val := by omega
      by_cases hsq : base.val * base.val < 2^64
      · rw [aborts_step_even base e acc hge hev,
          if_neg (by rw [BoundedNat.mul_aborts_eq_false_of_lt base base hsq]; simp),
          ih (e.val / 2) (by omega) (BoundedNat.mul base base)
            (BoundedNat.div e (2 : BoundedNat (2^8))) acc (by rw [div_two_val]) ha,
          div_two_val, mul_val, Nat.mod_eq_of_lt hsq,
          even_pow_regroup base.val (e.val / 2) e.val (by omega)]
      · rw [aborts_step_even base e acc hge hev,
          if_pos (by
            rw [BoundedNat.mul_aborts_eq_true_of_le base base (by omega)]),
          if_neg]
        have hle : base.val * base.val ≤ base.val ^ e.val := by
          rw [sq_eq]
          exact Nat.pow_le_pow_right hb h2
        have hacc : base.val ^ e.val ≤ acc.val * base.val ^ e.val :=
          Nat.le_mul_of_pos_left _ ha
        omega
    · by_cases hml : acc.val * base.val < 2^64
      · rw [aborts_step_odd base e acc hge hev,
          if_neg (by rw [BoundedNat.mul_aborts_eq_false_of_lt acc base hml]; simp),
          ih (e.val - 1) (by omega) base
            (BoundedNat.sub e (1 : BoundedNat (2^8))) (BoundedNat.mul acc base)
            (by rw [sub_one_val])
            (by rw [mul_val, Nat.mod_eq_of_lt hml]; exact Nat.mul_pos ha hb),
          sub_one_val, mul_val, Nat.mod_eq_of_lt hml]
        have hpow : acc.val * base.val * base.val ^ (e.val - 1)
            = acc.val * base.val ^ e.val := by
          rw [odd_pow_regroup acc.val base.val (e.val - 1), show e.val - 1 + 1 = e.val by omega]
        rw [hpow]
      · rw [aborts_step_odd base e acc hge hev,
          if_pos (by rw [BoundedNat.mul_aborts_eq_true_of_le acc base (by omega)]),
          if_neg]
        have hle : base.val ≤ base.val ^ e.val := by
          have := Nat.pow_le_pow_right hb hge
          rwa [Nat.pow_one] at this
        have hmul : acc.val * base.val ≤ acc.val * base.val ^ e.val :=
          Nat.mul_le_mul_left _ hle
        omega
  · have h0 : e.val = 0 := by omega
    rw [aborts_step_zero base e acc h0, if_pos]
    rw [h0, Nat.pow_zero, Nat.mul_one]
    exact acc.property

/-- Abort summary for the loop with an arbitrary nonzero accumulator: the loop
aborts on exactly the mathematical overflow of `acc * base ^ exp`. -/
theorem pow_aborts_while (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (acc : BoundedNat (2^64)) (ha : 0 < acc.val) :
    U64.pow.aborts.while_0 base e acc =
      if acc.val * base.val ^ e.val < 2^64 then Abort.AbortResult.NoAbort
      else Abort.AbortResult.Aborted { code := (0 : BoundedNat (2^64)) } :=
  aborts_aux e.val base e acc rfl ha

/-- The `acc = 1` specialization, hypothesis-free. -/
theorem pow_aborts_while_one (base : BoundedNat (2^64)) (e : BoundedNat (2^8)) :
    U64.pow.aborts.while_0 base e (1 : BoundedNat (2^64)) =
      if base.val ^ e.val < 2^64 then Abort.AbortResult.NoAbort
      else Abort.AbortResult.Aborted { code := (0 : BoundedNat (2^64)) } := by
  rw [pow_aborts_while base e (1 : BoundedNat (2^64)) (by rw [u64_one_val]; omega),
    u64_one_val, Nat.one_mul]

/-- `U64.pow.aborts` in closed form. -/
theorem pow_aborts (base : BoundedNat (2^64)) (e : BoundedNat (2^8)) :
    U64.pow.aborts base e =
      if base.val ^ e.val < 2^64 then Abort.AbortResult.NoAbort
      else Abort.AbortResult.Aborted { code := (0 : BoundedNat (2^64)) } := by
  rw [pow_aborts_unfold, pow_aborts_while_one]

/-! ## Consumer-facing corollaries -/

/-- No overflow implies no abort. -/
theorem pow_no_abort_of_lt (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (h : base.val ^ e.val < 2^64) :
    U64.pow.aborts base e = Abort.AbortResult.NoAbort := by
  rw [pow_aborts, if_pos h]

/-- Overflow implies abort (with Move's `0` abort code). -/
theorem pow_aborts_of_le (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (h : 2^64 ≤ base.val ^ e.val) :
    U64.pow.aborts base e =
      Abort.AbortResult.Aborted { code := (0 : BoundedNat (2^64)) } := by
  rw [pow_aborts, if_neg (by omega)]

/-- ... and the converse: a non-aborting `pow` witnesses that the exact power
fits in `u64`. -/
theorem pow_lt_of_no_abort (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (h : U64.pow.aborts base e = Abort.AbortResult.NoAbort) :
    base.val ^ e.val < 2^64 := by
  by_cases hc : base.val ^ e.val < 2^64
  · exact hc
  · rw [pow_aborts_of_le base e (by omega)] at h
    exact absurd h (by simp)

/-- `move_effect`-tagged Prop form: an abort goal about `pow` becomes a pure Nat
inequality. Terminating (removes `U64.pow.aborts`; the RHS has no Move op). -/
@[move_effect] theorem pow_no_abort_iff (base : BoundedNat (2^64)) (e : BoundedNat (2^8)) :
    (U64.pow.aborts base e = Abort.AbortResult.NoAbort) ↔ base.val ^ e.val < 2^64 :=
  ⟨pow_lt_of_no_abort base e, pow_no_abort_of_lt base e⟩

/-- Exact (non-modular) value whenever the power fits. -/
theorem pow_val_of_lt (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (h : base.val ^ e.val < 2^64) :
    (U64.pow base e).val = base.val ^ e.val := by
  rw [pow_val, Nat.mod_eq_of_lt h]

/-- Exact value from the no-abort side condition the leaves actually carry. -/
theorem pow_val_of_no_abort (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (h : U64.pow.aborts base e = Abort.AbortResult.NoAbort) :
    (U64.pow base e).val = base.val ^ e.val :=
  pow_val_of_lt base e (pow_lt_of_no_abort base e h)

/-- Cross-carrier form: mentions BOTH loop helpers, so the harvest indexes it
under either carrier. -/
theorem pow_while_val_of_aborts_while (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (acc : BoundedNat (2^64)) (ha : 0 < acc.val)
    (h : U64.pow.aborts.while_0 base e acc = Abort.AbortResult.NoAbort) :
    (U64.pow.while_0 base e acc).val = acc.val * base.val ^ e.val := by
  rw [pow_aborts_while base e acc ha] at h
  by_cases hlt : acc.val * base.val ^ e.val < 2^64
  · rw [pow_while_val, Nat.mod_eq_of_lt hlt]
  · rw [if_neg hlt] at h
    exact absurd h (by simp)

/-- A nonzero base gives a nonzero power. -/
theorem pow_pos (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (hb : 0 < base.val) (h : U64.pow.aborts base e = Abort.AbortResult.NoAbort) :
    0 < (U64.pow base e).val := by
  rw [pow_val_of_no_abort base e h]
  exact Nat.pow_pos hb

/-- Monotone bound: the usual way a leaf discharges the no-abort side condition
from an exponent bound (e.g. `base ≤ 10`, `exp ≤ 19`). -/
theorem pow_no_abort_of_le_of_le (base : BoundedNat (2^64)) (e : BoundedNat (2^8))
    (b n : Nat) (hbpos : 0 < b) (hb : base.val ≤ b) (hn : e.val ≤ n)
    (hbn : b ^ n < 2^64) :
    U64.pow.aborts base e = Abort.AbortResult.NoAbort := by
  refine pow_no_abort_of_lt base e (Nat.lt_of_le_of_lt ?_ hbn)
  exact Nat.le_trans (Nat.pow_le_pow_left hb e.val) (Nat.pow_le_pow_right hbpos hn)

end U64Pow
