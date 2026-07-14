import Lean
import Prelude.BoundedArith
import Prelude.MoveAbort

/-
# AbortsTactics

`discharge_aborts [lemmas]` proves a `<fn>.aborts = none` goal. With the backend
emitting the `.aborts` spine as `MoveAbort.orElse` chains, the proof is now
structural:

1. `intro` the `asserts_cond*` precondition hypotheses,
2. `simp only [orElse_eq_none_iff, ite_some_none_eq_none, …]` peels the whole
   spine into one goal per abort check — a `<guard> = false` (Bool) for arithmetic
   / assert guards, or a callee `<callee>.aborts = none` — WITHOUT the kernel
   reducing the nested body,
3. discharge each guard from the normalized bounds (`bounded_arith` / `omega`)
   or from the passed callee `.aborts` lemmas.

The function-specific simp lemmas — the `<fn>.aborts` name, its callees'
`.aborts`, the `asserts_cond*` names, the field accessors, and `MoveStdlib`
lemmas (`MoveOption.is_none`, `Integer.gte`, …) — are passed in the bracket
(a `Prelude` tactic file can't import `MoveStdlib`). The structural + `BoundedNat`
bridges are built in.
-/

/-- An `if guard then some _ else none` abort check is `none` exactly when the
guard is `false`. Lets the spine decompose to plain `<guard> = false` goals that
`bounded_arith` closes. -/
@[simp] theorem ite_some_none_eq_none {α : Type _} {b : Bool} {x : α} :
    (if b then Option.some x else Option.none) = Option.none ↔ b = false := by
  cases b <;> simp

open Lean Meta in
/-- Reduce `BoundedNat.val (n : BoundedNat bound)` for a NUMERAL `n` to the bare
numeral (definitional — `whnf` unfolds the `OfNat` instance, which `simp` won't).
Guarded to numeral args so it never touches `a.val` for a variable `a` (no loop).
This is what lets `omega` use literal bounds in assert/`.aborts` guards such as
`(1000000000 : BoundedNat (2^64)).val`, which it otherwise treats as an opaque
atom ("no usable constraints"). `_decl` so it's NOT globally active — only
`discharge_aborts` opts in via its `simp only` set. -/
dsimproc_decl reduceBoundedNatVal (BoundedNat.val _) := fun e => do
  let_expr BoundedNat.val _ arg := e | return .continue
  let_expr OfNat.ofNat _ _ _ := arg | return .continue
  return .done (← whnfD e)


/-- Package-curated simp set for `discharge_aborts`. Tag proven abort facts once
(`@[aborts_simp] theorem foo_aborts_none : ...`, accessor equations, `asserts_cond`
unfoldings) instead of repeating them in every call's bracket list. The set is
included in `discharge_aborts`'s `simp only` automatically; tag LEMMAS, not
`.aborts` defs — tagging defs re-inlines callee trees and defeats the structural
peel. -/
register_simp_attr aborts_simp

/-- Callee-contract registry (unified-backend design §5.2). Tag proven callee
contract theorems — `<callee>.aborts … = none` facts, typically the
`*_aborts_none_sound` family — with `@[contract]`; `discharge_obligation` and
`discharge_aborts` consult the set first, so callee-aborts leaf obligations
(`<callee>.aborts args = none` bundle leaves) for already-proven callees close
silently and verification composes modularly through the call graph. The
generator pre-tags the `aborts_none_of` theorems it emits for LEAF-FREE (total)
callees; every other contract is registered by the human at its proof site.
Like `aborts_simp`: tag THEOREMS, never `.aborts` defs. -/
register_simp_attr contract

open Lean.Parser.Tactic in
syntax "discharge_aborts" "[" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| discharge_aborts [$ls,*]) =>
    `(tactic|
      (intros
       simp only [contract, aborts_simp, $ls,*, MoveAbort.orElse_eq_none_iff, ite_some_none_eq_none,
         eq_iff_iff, iff_true, decide_eq_true_eq, decide_eq_false_iff_not,
         BoundedNat.lt_def, BoundedNat.le_def, BoundedNat.val_ofNat_lt, reduceBoundedNatVal,
         Bool.false_eq_true, Bool.and_eq_false_imp] at *
       -- `all_goals` tolerates the case where the `simp only` already closed the
       -- goal entirely (no residual guards) — then this is a no-op success
       -- rather than a "no goals" error.
       all_goals (first
         | rfl
         | omega
         | bounded_arith
         | (-- Break the residual conjunction (orElse spine) AND any nested `if`s
            -- from the assert residue (`if cond then … else some abort`), then
            -- close each leaf: `none = none` by rfl, an arithmetic guard by
            -- bounded_arith/omega, and an unreachable `some = none` branch by the
            -- contradiction between the split condition and the assert bound.
            repeat' (first | apply And.intro | split)
            all_goals (first
               | rfl
               | bounded_arith
               | omega
               | assumption
               | (exfalso <;> omega)
               | simp_all (config := { failIfUnchanged := false })
                   [BoundedNat.add_overflows_false_of_bounds, BoundedNat.sub_underflows_false_of_le,
                    BoundedNat.mul_overflows_false_of_bounds, BoundedNat.decide_ge_eq_false_of_lt])))))

open Lean.Parser.Tactic in
/-- Close one obligation-bundle leaf (`<fn>.aborts.ob_k …`): intro the path
premises, normalize everything (obligation unfolds via the `aborts_simp` set,
guard predicates to `.val` form, structure-literal projections via `dsimp`),
split residual branches, close with `omega`/`rfl` against the facts in the
bracket. Typical use: `apply F.aborts_none_of <;> discharge_obligation [facts]`. -/
syntax "discharge_obligation" "[" simpLemma,* "]" : tactic

macro_rules
  | `(tactic| discharge_obligation [$ls,*]) =>
    `(tactic|
      (intros
       first
        | rfl
        | assumption
        | (simp only [contract, aborts_simp, $ls,*, MoveAbort.orElse_none_left,
             MoveAbort.orElse_eq_none_iff, ite_some_none_eq_none,
             BoundedNat.le_def, BoundedNat.lt_def, gt_iff_lt, ge_iff_le,
             decide_eq_true_eq, decide_eq_false_iff_not, reduceBoundedNatVal,
             BoundedNat.val_ofNat_lt, BoundedNat.add_overflows,
             BoundedNat.sub_underflows, BoundedNat.mul_overflows,
             Bool.not_eq_true, Nat.add_zero, Nat.zero_add] at *
           try dsimp only [] at *
           repeat' split
           all_goals (intros; first | rfl | omega | assumption | trivial))
        | (simp only [contract, aborts_simp, $ls,*, MoveAbort.orElse_none_left,
             MoveAbort.orElse_eq_none_iff, ite_some_none_eq_none,
             BoundedNat.le_def, BoundedNat.lt_def, gt_iff_lt, ge_iff_le,
             decide_eq_true_eq, decide_eq_false_iff_not, reduceBoundedNatVal,
             BoundedNat.val_ofNat_lt, BoundedNat.add_overflows,
             BoundedNat.sub_underflows, BoundedNat.mul_overflows,
             Bool.not_eq_true, eq_self_iff_true, if_true, if_false,
             and_true, true_and]
           try dsimp only []
           repeat' split
           all_goals (intros; first | rfl | omega | assumption | trivial))
        | (intros
           exfalso
           simp only [contract, aborts_simp, $ls,*, if_true, if_false, eq_self_iff_true,
             decide_eq_true_eq, decide_eq_false_iff_not, Bool.true_eq_false,
             Bool.false_eq_true, BoundedNat.le_def, reduceBoundedNatVal] at *)
        | omega))

-- An EMPTY bracket list makes the `$ls,*` splice above produce syntax the
-- simp elaborator rejects per-lemma (`internal exception: unsupportedSyntax`),
-- silently gutting the whole `simp only` set. `[]` is exactly the
-- contract-registry workflow (`apply F.aborts_none_of <;>
-- discharge_obligation []` with every callee leaf closing from `@[contract]`),
-- so rewrite the empty form to a harmless singleton. These rules are declared
-- AFTER the general ones — macro_rules try later rules first, so the empty
-- case is intercepted before the generic `$ls,*` match.
macro_rules
  | `(tactic| discharge_aborts []) =>
    `(tactic| discharge_aborts [eq_self_iff_true])
macro_rules
  | `(tactic| discharge_obligation []) =>
    `(tactic| discharge_obligation [eq_self_iff_true])
