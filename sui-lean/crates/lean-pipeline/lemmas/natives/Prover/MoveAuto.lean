import Prelude.Mutation
import Prover.MoveAutoAttr
import Aesop
import Auto.Tactic

/-! ## Import neutrality

`import Prover.MoveAuto` is the single overlay-facing import for this layer, so
it must not change how anything ELSE in the importing file elaborates: agents
drop `move_auto` leaves into overlays that also carry hand-written proofs, and
those proofs must keep the meaning they had before the import was added.

`Auto.Tactic` (lean-auto) breaks that by itself. It declares its own
`BEq Int` -- `Auto.instBEqInt_auto`, backed by `Auto.Int.beq` -- which, being
declared later, outranks core's `instBEqOfDecidableEq` in every downstream
module. Generated Move models define `abbrev Integer := Int`, so importing
lean-auto silently re-elaborates every `==` on `Integer` in the overlay against
a DIFFERENT instance than the generated module used. Two production failures
traced to exactly this:

* `simp [BEq.beq]` / `Eq.mp _ rfl` steps stall or mismatch, because the two
  spellings of `==` are no longer the same term (scallop `Decimal_specs`,
  `Borrow_dynamics_specs`, `Reserve_specs`).
* `spec_conjuncts` binds its patterns by `isDefEq` against the generated leaf
  conjuncts. A pattern mentioning `==` elaborates with Auto's instance while the
  leaf carries core's, so the match fails and the command reports "pattern
  matched no conjunct" (ember `Proofs/SpecNames/Vault_specs.lean`).

The fix is to DEMOTE, not erase. `attribute [-instance]` alone is not enough:
Lean does not persist an attribute erasure to importing modules, only a
(re-)application, so the shadow would return the moment an overlay imported this
file. Erasing and re-registering at `low` priority does persist, restores core's
instance for downstream elaboration, and leaves lean-auto's own already-elaborated
uses untouched -- the Z3 lane is unaffected.

The demoted set is every lean-auto instance whose type mentions no lean-auto
constant -- i.e. every one that competes with core on a purely core type -- among
the classes that can appear in a Move proof term. Enumerated from the instance
extension, not from grepping the vendored source:

* `Auto.instBEqInt_auto` / `Auto.instLawfulBEqInt_auto` on `Int`. The second
  matters on its own: left at default priority it wins `LawfulBEq Int` and drags
  the `BEq Int` shadow back in with it.
* `Auto.instBEqSumUnit_auto` / `Auto.instHashableSumUnit_auto` on `Unit ⊕ σ`, so
  neutrality does not rest on Move models happening never to use `Sum`.

Deliberately NOT demoted: lean-auto's `Auto.instToExpr*_auto` family. `ToExpr` is
a metaprogramming-only class, the proof audit already refuses metaprograms in
overlay files, and those instances are entangled with lean-auto's own erasure of
core's `ToLevel`-based `ToExpr` instances. Also not neutralizable: the three
global `@[simp]` lemmas lean-auto states about `List.getD` / its own
`Auto.List.split` -- a simp-attribute erasure is not persisted to importing
modules either, and they only add rewrites, they do not change what a term means.
lean-auto declares no `unif_hint` and no `default_instance`, and changes
reducibility only on its own declarations.

MoveAuto's interior option and channel words use Lean's non-reserving `&"..."`
tokens, so names such as `solver`, `rules`, and `cases` remain valid binders in
an importing overlay. Its optional abort `unfolding` clause uses a parser-local
delimiter for the same reason. The `spec_conjuncts` index form uses a
non-reserving leading parser and likewise keeps `as` as an `ident` parsed inside
its private syntax category, then checks the spelling during elaboration. Plain
string literals in those positions would reserve the names globally.

`lake_compile_smoke.rs::move_auto_import_is_elaboration_neutral` is the guard. It
asserts, from inside a module that imports this one, both the exact winning
instance for a matrix of core class/type pairs and that the set of
automation-dependency instances stated purely over core types still equals the
list it pins. A revendored lean-auto that adds a shadow turns that test red;
answer it by extending the demotion below, not by relaxing the test. -/
attribute [-instance] Auto.instBEqInt_auto Auto.instLawfulBEqInt_auto
  Auto.instBEqSumUnit_auto Auto.instHashableSumUnit_auto
attribute [instance low] Auto.instBEqInt_auto Auto.instLawfulBEqInt_auto
  Auto.instBEqSumUnit_auto Auto.instHashableSumUnit_auto

/-! ## The `move_effect` registry

`move_effect` collects the shipped operation/observation facts about the Move
runtime models: Table and Dynamic-Field presence and abort equations, the
`Mutation.path` / `Mutation.loc` projections, the BoundedNat no-abort value
equations, and the signed round-trips. It is an OPEN registry -- client overlays
and generated modules may tag into it -- which is the point: a corpus that
teaches the automation one new observation teaches every `move_norm` call site
at once.

Every `move_norm*` form applies it, INCLUDING the `only [...]` forms, exactly as
those forms already apply `move_auto_base`. `only` in this layer means "no
`move_summary`" (project-level summaries stay opt-in), never "no ambient sets" --
`move_auto_base` has always been ambient in the `only` forms, and `move_effect`
now sits beside it. The alternative -- folding these ~90 facts into
`move_auto_base` -- was rejected: `move_auto_base` is frozen name-for-name by
`checkMoveAutoBase`, so it cannot absorb an open registry without either
destroying the freeze or forcing every client tag through this file.

The contract a `move_effect` lemma must satisfy is TERMINATION, not confluence:
each one must move a term toward a value or an observation and must never
install a reverse rewrite. Concretely, for every tagged equation the right-hand
side must be strictly smaller than the left in the "runtime operations applied"
measure -- `Table.contains (Table.add t k v) k = true` removes an `add`,
`from_u64 x = (x.val : Int)` removes a coercion, `to_u64 (from_u64 x) = x`
removes both. A tagged fact whose right-hand side re-introduces its own
left-hand head turns every `move_norm` into a diverging rewrite, which is a
fatal failure, not a slow one. Conditional rewrites are fine (the hypothesis is
discharged by the same simp set) as long as the conclusion obeys the measure.
There is deliberately NO guard analogous to `move_auto_base_guard` here: freezing
an open registry would defeat it. -/
/-! ### The raw-`Nat` comparator decode bridges

`move_auto_base` decodes a **BoundedNat**-level comparator face
(`bn_lt_decide` ... + `decide_eq_true_eq` / `decide_eq_false_iff_not`), but it has no
rule one level down, at the raw `Nat` comparator. That level is not hypothetical: a
vector-index bound check compares `BoundedNat.val` against `MoveVector.length`, which
is a plain `Nat`, so the generated guard is `Nat.blt i len = true`; and `simp`'s own
side-goal proofs come out in exactly that normal form (see the `mkIteEq` note below,
`Nat.ble a.val b.val = true` rather than `BoundedNat.le a b = true`).

The three core equations already exist and are `@[simp]` upstream -- which is precisely
why they were unreachable: every `move_norm*` form is `only`-scoped by contract, so the
ambient simp set is invisible to it. Registering them here is what puts them in front of
`omega`/`grind` instead of behind them.

All nine obey the termination contract by construction: every left-hand side is a Bool
comparator FACE (`cmp = true`, `cmp = false`, `!cmp = true`) and every right-hand side is
a pure `Nat` order/equality Prop. No right-hand side mentions `Nat.blt`/`ble`/`beq`, so
none can re-introduce its own head, and the set is unconditional -- it puts no side goal
in front of a normalizer that runs on nearly every arithmetic goal.

The ENCODE direction (`nat_blt_eq_true : a < b -> a.blt b = true` and its kin) is
deliberately NOT registered: it re-encodes, and as a conditional rewrite it would put a
Prop side goal at every comparator occurrence. It is also unnecessary -- a goal-side
`Nat.blt a b = true` is closed by the decode rule applied to the GOAL.

The `!cmp = true` face is NOT covered, and that is a measurement rather than an omission.
Three restated iffs for it shipped with the first version of this block on the strength of
the shape existing in human proofs (14 fleet citations of the implication half). A
face-level instrument then found **zero** occurrences of it: 410 momentum leaves and 173
bluefin leaves scanned before AND after the strongest normalizer, 0 in both. Momentum
holds 10 of those 14 citations, so the corpus that cites it most never presents it -- the
citation records the route the HUMAN took, not a face the tactic meets. -/
attribute [move_effect]
  Nat.blt_eq
  Nat.ble_eq
  Nat.beq_eq
  nat_blt_eq_false_iff_le
  nat_ble_eq_false_iff_lt
  nat_beq_eq_false_iff_ne

/-! ### The fixed-width conversion faces

`BoundedNat.convert_val_of_bound_le` is registered below and is STRUCTURALLY INERT at a
concrete width pair: its side goal is `bound_from <= bound_to`, i.e. `2^64 <= 2^128`, and
an `only`-scoped simp set does not discharge ground arithmetic. The other conditional form
(`convert_val_of_lt`, side goal `a.val < bound_to`) is worse -- the fact lives in
`a.property`, which is not a hypothesis at all. That is why the corpora carry 29 private
fixed-width restatements of a lemma the framework has shipped all along. Two of the four
pairs below already existed here unregistered; `u32 -> u64` (the I32-abs oracle path) and
`u64 -> u256` (the ClmmMath widening path) are the ones the corpora re-derive.

Termination: each corollary removes a `convert` and adds nothing, and all four are
unconditional, so none puts a side goal in front of a hot-path normalizer.

**`bn_eq_iff_val_eq` is deliberately NOT here, and that is a measurement.** It is the
decode orientation of `bn_val_inj` (`a = b <-> a.val = b.val`) and it is what the tail's
182 `apply BoundedNat.ext` uses ask for; registered, it earned 12 attributed closes on a
paired momentum ladder and zero regressions on 180 closed leaves. It still cannot be
ambient: `simp_all` uses a hypothesis `h : a = b` to SUBSTITUTE `a := b` everywhere, and
rewriting that hypothesis to `a.val = b.val` first destroys the substitution and leaves the
rest of the goal facing an opaque term. Measured on the momentum overlay: two `rung := all`
replays whose context carried `have hproductZero : product = (0 : BoundedNat (2^256))` went
from closing to exhausting an 8,000,000-heartbeat budget at `whnf`, taking two modules and
two kernel-level cascades with them. An equality decode belongs to a GOAL-only rule channel,
which `move_effect` is not; the lemma is kept in `Prelude/BoundedNat.lean` for hand use. -/
attribute [move_effect]
  BoundedNatFacts.convert_val_u64_u128
  BoundedNatFacts.convert_val_u128_u256
  BoundedNatFacts.convert_val_u32_u64
  BoundedNatFacts.convert_val_u64_u256

attribute [move_effect]
  BoundedNat.convert_val_of_bound_le
  BoundedNat.convert_aborts_eq_false_of_bound_le
  BoundedNat.widen_val
  BoundedNat.add_converted_val_of_bound_le
  BoundedNat.mul_converted_val_of_bound_le
  bn_add_val_of_no_abort
  bn_mul_val_of_no_abort
  bn_convert_val_of_no_abort
  Prover.Mutation.Mutation.path_updateValue
  Prover.Mutation.Mutation.loc_updateValue
  Prover.Mutation.Mutation.path_borrowField
  Prover.Mutation.Mutation.loc_borrowField
  Prover.Mutation.Mutation.path_borrowEnumField
  Prover.Mutation.Mutation.loc_borrowEnumField
  Prover.Mutation.Mutation.path_borrowVecIndex
  Prover.Mutation.Mutation.loc_borrowVecIndex
  Prover.Mutation.Mutation.path_borrowMapKey
  Prover.Mutation.Mutation.loc_borrowMapKey

open Lean Meta in
dsimproc_decl Prover.MoveAuto.reduceBoundedNatVal (BoundedNat.val _) := fun e => do
  let_expr BoundedNat.val _ arg := e | return .continue
  let_expr OfNat.ofNat _ _ _ := arg | return .continue
  return .done (← whnfD e)

open Prover.Mutation

namespace Prover.MoveAuto

variable {Key : Type} {S T V : Type}

theorem boundedAdd_val {bound : Nat} (a b : BoundedNat bound) :
    (BoundedNat.add a b).val = (a.val + b.val) % bound := by
  have h : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  simp only [BoundedNat.add, h, ↓reduceDIte]

theorem boundedAdd_val_of_lt {bound : Nat} (a b : BoundedNat bound)
    (h : a.val + b.val < bound) :
    (BoundedNat.add a b).val = a.val + b.val := by
  rw [boundedAdd_val, Nat.mod_eq_of_lt h]

theorem boundedMul_val {bound : Nat} (a b : BoundedNat bound) :
    (BoundedNat.mul a b).val = (a.val * b.val) % bound := by
  have h : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  simp only [BoundedNat.mul, h, ↓reduceDIte]

theorem boundedMul_val_of_lt {bound : Nat} (a b : BoundedNat bound)
    (h : a.val * b.val < bound) :
    (BoundedNat.mul a b).val = a.val * b.val := by
  rw [boundedMul_val, Nat.mod_eq_of_lt h]

theorem boundedSub_val {bound : Nat} (a b : BoundedNat bound) :
    (BoundedNat.sub a b).val = a.val - b.val := rfl

theorem boundedDiv_val {bound : Nat} (a b : BoundedNat bound) :
    (BoundedNat.div a b).val = a.val / b.val := rfl

theorem boundedMod_val {bound : Nat} (a b : BoundedNat bound) :
    (BoundedNat.mod a b).val = a.val % b.val := rfl

theorem borrowField_mk
    (m : Mutation Key S) (sid offset : Nat) (sel : S → T) :
    Mutation.borrowField m sid offset sel =
      { loc := m.loc, path := m.path ++ [Edge.structField sid offset],
        val := sel m.val } := rfl

theorem borrowEnumField_mk
    (m : Mutation Key S) (sid variant offset : Nat) (sel : S → T) :
    Mutation.borrowEnumField m sid variant offset sel =
      { loc := m.loc, path := m.path ++ [Edge.enumField sid variant offset],
        val := sel m.val } := rfl

theorem borrowMapKey_mk
    (m : Mutation Key S) (k : Key) (lookup : S → Key → V) :
    Mutation.borrowMapKey m k lookup =
      { loc := m.loc, path := m.path ++ [Edge.mapKey k],
        val := lookup m.val k } := rfl

theorem borrowVecIndex_mk
    (m : Mutation Key (List T)) (i : Nat) [Inhabited T] :
    Mutation.borrowVecIndex m i =
      { loc := m.loc, path := m.path ++ [Edge.vecIndex i],
        val := m.val.getD i default } := rfl

theorem ofLocal_mk (i : Nat) (v : T) :
    Mutation.ofLocal (Key := Key) i v =
      { loc := .localRoot i, path := [], val := v } := rfl

theorem ofParam_mk (i : Nat) (v : T) :
    Mutation.ofParam (Key := Key) i v =
      { loc := .param i, path := [], val := v } := rfl

theorem path_updateValue (m : Mutation Key T) (v : T) :
    (m.updateValue v).path = m.path :=
  Prover.Mutation.Mutation.path_updateValue m v

theorem loc_updateValue (m : Mutation Key T) (v : T) :
    (m.updateValue v).loc = m.loc :=
  Prover.Mutation.Mutation.loc_updateValue m v

theorem isSameMutation_set_left [BEq Key]
    (a : Mutation Key S) (v : S) (b : Mutation Key T) :
    Mutation.isSameMutation (a.set v) b = Mutation.isSameMutation a b := rfl

theorem isSameMutation_set_right [BEq Key]
    (a : Mutation Key S) (b : Mutation Key T) (v : T) :
    Mutation.isSameMutation a (b.set v) = Mutation.isSameMutation a b := rfl

theorem isSameMutation_updateValue_left [BEq Key]
    (a : Mutation Key S) (v : S) (b : Mutation Key T) :
    Mutation.isSameMutation (a.updateValue v) b =
      Mutation.isSameMutation a b := rfl

theorem isSameMutation_updateValue_right [BEq Key]
    (a : Mutation Key S) (b : Mutation Key T) (v : T) :
    Mutation.isSameMutation a (b.updateValue v) =
      Mutation.isSameMutation a b := rfl

theorem mutation_eq_iff (a b : Mutation Key T) :
    a = b ↔
      a.loc = b.loc ∧
      a.path = b.path ∧
      a.val = b.val := by
  constructor
  · intro h
    subst b
    simp
  · rintro ⟨hLoc, hPath, hVal⟩
    cases a
    cases b
    simp_all

theorem z3OracleResult {p : Prop} (h : p) : p := h

theorem explicitZ3OracleResult {p : Prop} (h : p) : p := h

/-! ### Monotone numeral power bounds

`omega` is linear and treats `b ^ x` as an opaque atom; `grind` and the Z3 lane
do not decide nonlinear exponentiation either. So a leaf that needs
`10 ^ n < 2 ^ 64` from `n ≤ 19` was unreachable for every rung of the ladder,
and the corpus discharged those side conditions with `native_decide` oracles.

The missing step is purely monotone: with a LITERAL base (or a literal
exponent) one `Nat.pow_le_pow_right` / `Nat.pow_le_pow_left` application turns
the power into a closed numeral, after which the residue is linear and omega
finishes. These are the four directions, stated so the meta layer can
instantiate them with literals only. -/

theorem pow_le_of_exponent_le {b x n L : Nat} (hb : 0 < b) (hn : x ≤ n)
    (hL : b ^ n ≤ L) : b ^ x ≤ L :=
  Nat.le_trans (Nat.pow_le_pow_right hb hn) hL

theorem pow_le_of_exponent_lt {b x n L : Nat} (hb : 0 < b) (hn : x < n)
    (hL : b ^ (n - 1) ≤ L) : b ^ x ≤ L :=
  Nat.le_trans (Nat.pow_le_pow_right hb (by omega)) hL

theorem le_pow_of_exponent_ge {b x n L : Nat} (hb : 0 < b) (hn : n ≤ x)
    (hL : L ≤ b ^ n) : L ≤ b ^ x :=
  Nat.le_trans hL (Nat.pow_le_pow_right hb hn)

theorem le_pow_of_exponent_gt {b x n L : Nat} (hb : 0 < b) (hn : n < x)
    (hL : L ≤ b ^ (n + 1)) : L ≤ b ^ x :=
  Nat.le_trans hL (Nat.pow_le_pow_right hb (by omega))

theorem pow_le_of_base_le {c x n L : Nat} (hx : x ≤ c) (hL : c ^ n ≤ L) :
    x ^ n ≤ L :=
  Nat.le_trans (Nat.pow_le_pow_left hx n) hL

theorem pow_le_of_base_lt {c x n L : Nat} (hx : x < c) (hL : (c - 1) ^ n ≤ L) :
    x ^ n ≤ L :=
  Nat.le_trans (Nat.pow_le_pow_left (by omega) n) hL

/-- The converse direction: a numeral ceiling ON a power is a linear ceiling on
its exponent. This is what turns `10 ^ e < 2 ^ 64` into `e ≤ 19`. -/
theorem exponent_le_of_pow_lt {b x m K : Nat} (hb : 0 < b) (hK : b ^ x < K)
    (hm : K ≤ b ^ (m + 1)) : x ≤ m :=
  Nat.not_lt.mp fun hgt =>
    Nat.not_lt.mpr (Nat.le_trans hm (Nat.pow_le_pow_right hb hgt)) hK

theorem exponent_le_of_pow_le {b x m K : Nat} (hb : 0 < b) (hK : b ^ x ≤ K)
    (hm : K < b ^ (m + 1)) : x ≤ m :=
  Nat.not_lt.mp fun hgt =>
    Nat.not_le.mpr (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right hb hgt)) hK

theorem pow_pos_of_base_pos {b x : Nat} (hb : 0 < b) : 0 < b ^ x := Nat.pow_pos hb

end Prover.MoveAuto

attribute [move_auto_base]
  Prover.MoveAuto.boundedAdd_val
  Prover.MoveAuto.boundedMul_val
  Prover.MoveAuto.boundedSub_val
  Prover.MoveAuto.boundedDiv_val
  Prover.MoveAuto.boundedMod_val
  Nat.mod_eq_of_lt
  Bool.and_eq_true
  Bool.or_eq_true
  decide_eq_true_eq
  decide_eq_false_iff_not
  bn_lt_decide
  bn_le_decide
  bn_gt_decide
  bn_ge_decide
  bn_eq_decide
  bn_neq_decide
  bn_sub_aborts_decide
  bn_add_aborts_decide
  bn_mul_aborts_decide
  bn_div_aborts_decide
  bn_mod_aborts_decide
  bn_shl_aborts_decide
  bn_shr_aborts_decide
  bn_shl_bounded_aborts_decide
  bn_shr_bounded_aborts_decide
  bn_convert_aborts_decide
  Prover.Mutation.Mutation.val_updateValue
  Prover.Mutation.Mutation.val_set
  Prover.Mutation.Mutation.path_set
  Prover.Mutation.Mutation.loc_set
  Prover.Mutation.Mutation.val_ofLocal
  Prover.Mutation.Mutation.path_ofLocal
  Prover.Mutation.Mutation.loc_ofLocal
  Prover.Mutation.Mutation.val_ofParam
  Prover.Mutation.Mutation.path_ofParam
  Prover.Mutation.Mutation.loc_ofParam
  Prover.Mutation.Mutation.val_borrowField
  Prover.Mutation.Mutation.val_borrowEnumField
  Prover.Mutation.Mutation.val_borrowVecIndex
  Prover.Mutation.Mutation.val_borrowMapKey
  Prover.Mutation.Mutation.val_writeBackVecIndexLast_borrowVecIndex_set
  Prover.Mutation.Mutation.path_writeBackVecIndexLast
  Prover.Mutation.Mutation.loc_writeBackVecIndexLast
  Prover.Mutation.Mutation.val_writeBackMapKeyLast_borrowMapKey_set
  Prover.Mutation.Mutation.path_writeBackMapKeyLast
  Prover.Mutation.Mutation.loc_writeBackMapKeyLast
  Prover.MoveAuto.borrowField_mk
  Prover.MoveAuto.borrowEnumField_mk
  Prover.MoveAuto.borrowMapKey_mk
  Prover.MoveAuto.borrowVecIndex_mk
  Prover.MoveAuto.ofLocal_mk
  Prover.MoveAuto.ofParam_mk
  Prover.Mutation.Mutation.path_updateValue
  Prover.Mutation.Mutation.loc_updateValue
  Prover.MoveAuto.isSameMutation_set_left
  Prover.MoveAuto.isSameMutation_set_right
  Prover.MoveAuto.isSameMutation_updateValue_left
  Prover.MoveAuto.isSameMutation_updateValue_right
  Prover.MoveAuto.mutation_eq_iff
  Bool.false_eq_true
  if_true
  if_false
  ite_true
  ite_false
  ite_self
  eq_self_iff_true
  true_and
  and_true
  ne_eq
  not_true
  not_false_eq_true

open Lean

namespace Prover.MoveAuto

open Meta

-- Must list exactly the `attribute [move_auto_base]` block above, name for name;
-- `move_auto_base_guard` enforces the match at tactic time.
private def expectedMoveAutoBaseNames : List Name := [
  ``Prover.MoveAuto.boundedAdd_val,
  ``Prover.MoveAuto.boundedMul_val,
  ``Prover.MoveAuto.boundedSub_val,
  ``Prover.MoveAuto.boundedDiv_val,
  ``Prover.MoveAuto.boundedMod_val,
  ``Nat.mod_eq_of_lt,
  ``Bool.and_eq_true,
  ``Bool.or_eq_true,
  ``decide_eq_true_eq,
  ``decide_eq_false_iff_not,
  ``bn_lt_decide,
  ``bn_le_decide,
  ``bn_gt_decide,
  ``bn_ge_decide,
  ``bn_eq_decide,
  ``bn_neq_decide,
  ``bn_sub_aborts_decide,
  ``bn_add_aborts_decide,
  ``bn_mul_aborts_decide,
  ``bn_div_aborts_decide,
  ``bn_mod_aborts_decide,
  ``bn_shl_aborts_decide,
  ``bn_shr_aborts_decide,
  ``bn_shl_bounded_aborts_decide,
  ``bn_shr_bounded_aborts_decide,
  ``bn_convert_aborts_decide,
  ``Prover.Mutation.Mutation.val_updateValue,
  ``Prover.Mutation.Mutation.val_set,
  ``Prover.Mutation.Mutation.path_set,
  ``Prover.Mutation.Mutation.loc_set,
  ``Prover.Mutation.Mutation.val_ofLocal,
  ``Prover.Mutation.Mutation.path_ofLocal,
  ``Prover.Mutation.Mutation.loc_ofLocal,
  ``Prover.Mutation.Mutation.val_ofParam,
  ``Prover.Mutation.Mutation.path_ofParam,
  ``Prover.Mutation.Mutation.loc_ofParam,
  ``Prover.Mutation.Mutation.val_borrowField,
  ``Prover.Mutation.Mutation.val_borrowEnumField,
  ``Prover.Mutation.Mutation.val_borrowVecIndex,
  ``Prover.Mutation.Mutation.val_borrowMapKey,
  ``Prover.Mutation.Mutation.val_writeBackVecIndexLast_borrowVecIndex_set,
  ``Prover.Mutation.Mutation.path_writeBackVecIndexLast,
  ``Prover.Mutation.Mutation.loc_writeBackVecIndexLast,
  ``Prover.Mutation.Mutation.val_writeBackMapKeyLast_borrowMapKey_set,
  ``Prover.Mutation.Mutation.path_writeBackMapKeyLast,
  ``Prover.Mutation.Mutation.loc_writeBackMapKeyLast,
  ``Prover.MoveAuto.borrowField_mk,
  ``Prover.MoveAuto.borrowEnumField_mk,
  ``Prover.MoveAuto.borrowMapKey_mk,
  ``Prover.MoveAuto.borrowVecIndex_mk,
  ``Prover.MoveAuto.ofLocal_mk,
  ``Prover.MoveAuto.ofParam_mk,
  ``Prover.Mutation.Mutation.path_updateValue,
  ``Prover.Mutation.Mutation.loc_updateValue,
  ``Prover.MoveAuto.isSameMutation_set_left,
  ``Prover.MoveAuto.isSameMutation_set_right,
  ``Prover.MoveAuto.isSameMutation_updateValue_left,
  ``Prover.MoveAuto.isSameMutation_updateValue_right,
  ``Prover.MoveAuto.mutation_eq_iff,
  -- ite/Bool closure. Every `move_norm*` form is `only`-scoped by contract, and
  -- `only` drops the ambient simp set the corpus's hand-written `simp [...]`
  -- proofs lean on. The measured consequence was that channel-bearing rungs
  -- normalized a goal all the way down to `if True then X else Y` and then
  -- reported "did not close the rung" -- every guard discharged, nothing left
  -- but the `ite` skeleton. Ember's `Getters_specs_Proofs` already hand-carries
  -- `only [Bool.false_eq_true, if_false, ite_self]`, which is a rediscovered
  -- fragment of exactly this set. `reduceIte` is deliberately NOT listed: it is
  -- a simproc, not a theorem, and default simprocs already run under
  -- `simp only`, which was verified to leave `if True then X else Y` standing
  -- -- the theorems below are what actually discharge it.
  ``Bool.false_eq_true,
  ``if_true,
  ``if_false,
  ``ite_true,
  ``ite_false,
  ``ite_self,
  ``eq_self_iff_true,
  ``true_and,
  ``and_true,
  ``ne_eq,
  ``not_true,
  ``not_false_eq_true
]

def checkMoveAutoBase : CoreM Unit := do
  let some extension ← getSimpExtension? `move_auto_base
    | throwError "move_auto_base is not registered"
  let theorems ← extension.getTheorems
  let mut actual : List Name := []
  for origin in theorems.lemmaNames.toList do
    let .decl name _ _ := origin
      | throwError
          "move_auto_base contains a non-declaration entry. Supply project summaries explicitly"
    actual := name :: actual
  let missing := expectedMoveAutoBaseNames.filter fun name => !actual.contains name
  let unexpected := actual.filter fun name => !expectedMoveAutoBaseNames.contains name
  unless actual.length == expectedMoveAutoBaseNames.length &&
      missing.isEmpty && unexpected.isEmpty do
    throwError
      "move_auto_base was extended or altered (missing: {missing}; unexpected: {unexpected}). \
       Supply project summaries explicitly with only [...]"

private partial def collectFVars (e : Expr) (found : Array FVarId := #[]) :
    Array FVarId :=
  match e with
  | .fvar id => if found.contains id then found else found.push id
  | .app f a => collectFVars a (collectFVars f found)
  | .lam _ type body _ | .forallE _ type body _ =>
    collectFVars body (collectFVars type found)
  | .letE _ type value body _ =>
    collectFVars body (collectFVars value (collectFVars type found))
  | .mdata _ body => collectFVars body found
  | .proj _ _ body => collectFVars body found
  | _ => found

private def mentionsAnyFVar (e : Expr) (ids : Array FVarId) : Bool :=
  ids.any e.containsFVar

private def relevantFVars (goal : MVarId) : MetaM (Array FVarId) :=
  goal.withContext do
    let mut relevant := collectFVars (← goal.getType)
    let lctx ← getLCtx
    for _ in [:lctx.decls.size + 1] do
      let before := relevant.size
      for decl in lctx do
        let mentionsRelevant :=
          relevant.contains decl.fvarId ||
            mentionsAnyFVar decl.type relevant ||
            decl.value?.any (mentionsAnyFVar · relevant)
        if mentionsRelevant then
          unless relevant.contains decl.fvarId do
            relevant := relevant.push decl.fvarId
          relevant := collectFVars decl.type relevant
          if let some value := decl.value? then
            relevant := collectFVars value relevant
      if relevant.size == before then
        break
    return relevant

def addBoundedNatProperties (goal : MVarId) (focused : Bool) : MetaM MVarId :=
  goal.withContext do
    let relevant ← if focused then relevantFVars goal else pure #[]
    let mut hypotheses := #[]
    for decl in ← getLCtx do
      if focused && !relevant.contains decl.fvarId then
        continue
      let type ← whnf decl.type
      let_expr BoundedNat _ := type | continue
      let value ← mkAppM ``BoundedNat.property #[decl.toExpr]
      hypotheses := hypotheses.push {
        userName := ← mkFreshUserName `h_bound
        type := ← inferType value
        value
      }
    let (_, goal) ← goal.assertHypotheses hypotheses
    return goal

end Prover.MoveAuto

open Lean Elab Tactic Meta in
elab "move_bn_props" : tactic => do
  let goal ← Prover.MoveAuto.addBoundedNatProperties (← getMainGoal) true
  replaceMainGoal [goal]

open Lean Elab Tactic Meta in
elab "move_bn_props_all" : tactic => do
  let goal ← Prover.MoveAuto.addBoundedNatProperties (← getMainGoal) false
  replaceMainGoal [goal]

namespace Prover.MoveAuto

open Lean Elab Tactic Meta

private partial def collectFVarsInto (e : Expr) (found : FVarIdHashSet) :
    FVarIdHashSet :=
  if !e.hasFVar then found
  else match e with
    | .fvar id => found.insert id
    | .app f a => collectFVarsInto a (collectFVarsInto f found)
    | .lam _ t b _ => collectFVarsInto b (collectFVarsInto t found)
    | .forallE _ t b _ => collectFVarsInto b (collectFVarsInto t found)
    | .letE _ t v b _ =>
      collectFVarsInto b (collectFVarsInto v (collectFVarsInto t found))
    | .mdata _ b => collectFVarsInto b found
    | .proj _ _ b => collectFVarsInto b found
    | _ => found

/-- Narrow the local context to the goal's dependency neighborhood before any
size policy or solver runs. Keeps: (1) every fvar the target mentions, (2)
every hypothesis whose type states a fact about a kept variable, (3)
transitively, everything a kept hypothesis' type or let-value mentions, so the
remaining telescope is closed under dependencies and `clear` cannot fail.
Everything else is dropped with `tryClearMany`.

A leaf inside a large structured proof inherits the entire enclosing
telescope: signature binders, every earlier `have`, and the `let` spine the
proof built on the way down. The leaf's own statement usually touches a
handful of those. Measured on ember (round 1, unpruned): 41% of probeable
leaves in >100-line proofs were refused purely for telescope size, at locals
p50 = 59 / max = 72 against the 48 limit, while leaves that fit the limit
closed at the small-body rate. Pruning makes the limit measure the leaf's own
neighborhood rather than its position in the proof, without raising the bound
itself.

A goal that mentions NO free variable is the one shape this relevance model
cannot express: `False`, or a closed numeral (in)equality. Its seed is empty,
so the fixpoint keeps nothing and the whole context goes — including the
contradictory hypothesis that is the only reason the goal is provable. That
is exactly the abort-reasoning shape "this branch is impossible", and it made
`move_auto` unable to refute a contradiction it could no longer see (pinned as
a regression in `lake_compile_smoke`'s contextNat/contextBool group between
`f2338d606` and this commit). Pruning is therefore a no-op on such goals: with
nothing to be relevant TO, "relevant" is not a question this transform gets to
answer, and the honest default is the full context.

The test is on the RAW goal expression, before relevance policy P1 below drops
Sort-typed fvars from the seed. The two conditions are about different things:
P1 asks which of the goal's variables DISCRIMINATE between hypotheses, and
presupposes the goal has variables at all. `hasFVar` is exactly
`(collectFVarsInto target {}).isEmpty = false` — the collector short-circuits
on the same flag — computed without the traversal. -/
private def pruneContextToGoalDeps : TacticM Unit := do
  let goal ← getMainGoal
  let pruned ← goal.withContext do
    let target ← goal.getType
    if !target.hasFVar then
      return goal
    let lctx ← getLCtx
    -- Relevance policy P1: type parameters are not DISCRIMINATING goal
    -- variables. Nearly every hypothesis in a generated corpus mentions the
    -- theorem's type binders (t_tv0, ...), so counting them in the relevance
    -- seed retained ~37 haves per leaf where the median proof cites one —
    -- 77.7% of all post-pruning width came from this edge (measured on
    -- ember's 212 width-refused leaves; P1 clears 62% of them at a recall
    -- cost of 83.3% -> 76.2% on cited premises). Type-param fvars still
    -- survive via the dependency closure when anything kept needs them.
    let rawGoalVars := collectFVarsInto target {}
    let mut goalVars : FVarIdHashSet := {}
    for fv in rawGoalVars.toList do
      if let some decl := lctx.find? fv then
        unless decl.type.isSort do
          goalVars := goalVars.insert fv
    let mut keep : FVarIdHashSet := goalVars
    let mut mentions : Array (FVarId × Array FVarId) := #[]
    for decl in lctx do
      if decl.isImplementationDetail then
        keep := keep.insert decl.fvarId
        continue
      let typeVars := collectFVarsInto decl.type {}
      let allVars := match decl.value? with
        | some value => collectFVarsInto value typeVars
        | none => typeVars
      mentions := mentions.push (decl.fvarId, allVars.toArray)
      if typeVars.toArray.any goalVars.contains then
        keep := keep.insert decl.fvarId
    let mut changed := true
    while changed do
      changed := false
      for (fvarId, vars) in mentions do
        if keep.contains fvarId then
          for v in vars do
            unless keep.contains v do
              keep := keep.insert v
              changed := true
    let mut toClear : Array FVarId := #[]
    for decl in lctx do
      unless keep.contains decl.fvarId do
        toClear := toClear.push decl.fvarId
    goal.tryClearMany toClear
  replaceMainGoal [pruned]

end Prover.MoveAuto

open Lean Elab Tactic in
elab "move_auto_base_guard" : tactic => do
  -- No pruning here: this guard fronts PINNED-RUNG REPLAYS, and pruning the
  -- replay context breaks durable invocations discovered before pruning
  -- existed (measured: omega-rung replays fail when move_bn_props loses
  -- context hypotheses). A replay that DOES need its discovery context says so
  -- in its own text, with the `move_auto_pruned` marker below; a replay without
  -- the marker keeps running on the full context exactly as it always has.
  Prover.MoveAuto.checkMoveAutoBase

open Lean Elab Tactic in
/-- Run a durable replay in the context its DISCOVERY saw: prune to the goal's
dependency neighborhood first, then replay.

Discovery runs behind `move_auto_leaf_guard`, which prunes; a durable replay
runs behind `move_auto_base_guard`, which does not. `ec6496601` made that split
deliberate on the stated ground that "replaying on the FULL context is monotone
for the checked solvers". That is false for the Aesop rung: its budget
(`maxRuleApplications := 64`, `maxGoals := 64`) is spent on whatever rules the
context offers, so a wider context can exhaust the search before it reaches the
step that closed the goal under pruning. Measured: 2 of 3 wide-context Aesop
conversions in the combined validation failed to replay, and the ONE adopted
round-9 Aesop leaf that broke under the campaign tip bisected to exactly that
commit -- re-discovery re-derived the byte-identical replay, so no adoption-side
fix existed.

The marker closes the loop by making the replay reproduce the discovery
environment instead of hoping the solver does not notice the difference. It is
emitted by discovery, never written by hand, and it is ABSENT from every proof
adopted before this commit -- those keep today's unpruned behaviour by
construction, which is what makes this change safe to land on a corpus of
already-verified replays. -/
elab "move_auto_pruned" ppSpace inner:tactic : tactic => do
  Prover.MoveAuto.pruneContextToGoalDeps
  evalTactic inner

macro "move_checked_arith" : tactic =>
  `(tactic| first
    | (apply Prover.MoveAuto.boundedAdd_val_of_lt <;> move_bn_props <;> omega)
    | (apply Prover.MoveAuto.boundedMul_val_of_lt <;> move_bn_props <;> omega))

macro "move_aesop_rules" "[" rules:ident,* "]" : tactic => do
  let localRules ← rules.getElems.mapM fun id =>
    `(Aesop.rule_expr| $id:ident)
  if rules.getElems.isEmpty then
    `(tactic| aesop
      (rule_sets := [-default])
      (add safe (by first
        | assumption
        | apply_assumption
        | intro _
        | apply And.intro
        | apply Iff.intro
        | exact True.intro
        | move_checked_arith
        | (move_bn_props; omega)))
      (config := {
        terminal := true
        enableSimp := false
        enableUnfold := false
        maxRuleApplicationDepth := 16
        maxRuleApplications := 64
        maxGoals := 64
        maxSafePrefixRuleApplications := 16
      }))
  else
    `(tactic| aesop
      (rule_sets := [-default])
      (add safe [$localRules:Aesop.rule_expr,*])
      (add safe (by first
        | assumption
        | apply_assumption
        | intro _
        | apply And.intro
        | apply Iff.intro
        | exact True.intro
        | move_checked_arith
        | (move_bn_props; omega)))
      (config := {
        terminal := true
        enableSimp := false
        enableUnfold := false
        maxRuleApplicationDepth := 16
        maxRuleApplications := 64
        maxGoals := 64
        maxSafePrefixRuleApplications := 16
      }))

macro "move_aesop" : tactic =>
  `(tactic| move_aesop_rules [])

macro "move_z3" "(" &"budget" ":=" selectedBudget:ident ")"
    &"facts" "[" factIds:ident,* "]"
    &"unfold" "[" unfolds:ident,* "]"
    &"defeq" "[" defeqs:ident,* "]" : tactic => do
  let allHyps ← `(Auto.hintelem| *)
  let directFacts ← factIds.getElems.mapM fun id => do
    let factTerm : Term := ⟨id.raw⟩
    `(Auto.hintelem| $factTerm:term)
  let factHints : Array (TSyntax ``Auto.hintelem) := #[allHyps] ++ directFacts
  match selectedBudget.getId.eraseMacroScopes with
  | `quick =>
      `(tactic|
        apply Prover.MoveAuto.z3OracleResult <;>
          set_option auto.tptp false in
            set_option auto.native false in
            set_option auto.smt true in
              set_option auto.smt.trust true in
                set_option auto.smt.save false in
                  set_option auto.smt.savepath "" in
                    set_option auto.smt.rconsProof false in
                      set_option auto.smt.additionalFlags "" in
                        set_option auto.mono.mode "fol" in
                          set_option auto.smt.solver.name "z3" in
                            set_option auto.smt.timeout 5 in
                              auto [$factHints,*] u[$unfolds,*] d[$defeqs,*])
  | `deep =>
      `(tactic|
        apply Prover.MoveAuto.z3OracleResult <;>
          set_option auto.tptp false in
            set_option auto.native false in
            set_option auto.smt true in
              set_option auto.smt.trust true in
                set_option auto.smt.save false in
                  set_option auto.smt.savepath "" in
                    set_option auto.smt.rconsProof false in
                      set_option auto.smt.additionalFlags "" in
                        set_option auto.mono.mode "fol" in
                          set_option auto.smt.solver.name "z3" in
                            set_option auto.smt.timeout 20 in
                              auto [$factHints,*] u[$unfolds,*] d[$defeqs,*])
  | _ => Macro.throwUnsupported

macro "move_z3" : tactic =>
  `(tactic|
    apply Prover.MoveAuto.z3OracleResult <;>
      set_option auto.tptp false in
        set_option auto.native false in
        set_option auto.smt true in
          set_option auto.smt.trust true in
            set_option auto.smt.save false in
              set_option auto.smt.savepath "" in
                set_option auto.smt.rconsProof false in
                  set_option auto.smt.additionalFlags "" in
                    set_option auto.mono.mode "fol" in
                      set_option auto.smt.solver.name "z3" in
                        set_option auto.smt.timeout 5 in
                          auto)

macro "move_norm_unguarded" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic|
    simp -zeta only
      [move_auto_base, move_effect, move_summary, Prover.MoveAuto.reduceBoundedNatVal] $[$loc]?)

macro "move_norm_unguarded" "[" hs:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic|
    simp -zeta only
      [move_auto_base, move_effect, move_summary,
        Prover.MoveAuto.reduceBoundedNatVal, $hs,*] $[$loc]?)

macro "move_norm_unguarded" &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic|
    simp -zeta only
      [move_auto_base, move_effect, Prover.MoveAuto.reduceBoundedNatVal, $hs,*] $[$loc]?)

macro "move_norm_all_unguarded" : tactic =>
  `(tactic|
    simp_all -zeta only
      [move_auto_base, move_effect, move_summary, Prover.MoveAuto.reduceBoundedNatVal])

macro "move_norm_all_unguarded" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp_all -zeta only
      [move_auto_base, move_effect, move_summary, Prover.MoveAuto.reduceBoundedNatVal, $hs,*])

macro "move_norm_all_unguarded" &"only"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp_all -zeta only
      [move_auto_base, move_effect, Prover.MoveAuto.reduceBoundedNatVal, $hs,*])

macro "move_norm_all_zeta_unguarded" : tactic =>
  `(tactic|
    simp_all (config := { zetaDelta := true }) only
      [move_auto_base, move_effect, move_summary, Prover.MoveAuto.reduceBoundedNatVal])

macro "move_norm_all_zeta_unguarded"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp_all (config := { zetaDelta := true }) only
      [move_auto_base, move_effect, move_summary, Prover.MoveAuto.reduceBoundedNatVal, $hs,*])

macro "move_norm_all_zeta_unguarded" &"only"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp_all (config := { zetaDelta := true }) only
      [move_auto_base, move_effect, Prover.MoveAuto.reduceBoundedNatVal, $hs,*])

macro "move_norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (move_auto_base_guard; move_norm_unguarded $[$loc]?))

macro "move_norm" "[" hs:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (move_auto_base_guard; move_norm_unguarded [$hs,*] $[$loc]?))

macro "move_norm" &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (move_auto_base_guard; move_norm_unguarded only [$hs,*] $[$loc]?))

macro "move_norm_all" : tactic =>
  `(tactic| (move_auto_base_guard; move_norm_all_unguarded))

macro "move_norm_all" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (move_auto_base_guard; move_norm_all_unguarded [$hs,*]))

macro "move_norm_all" &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (move_auto_base_guard; move_norm_all_unguarded only [$hs,*]))

macro "move_norm_all_zeta" : tactic =>
  `(tactic| (move_auto_base_guard; move_norm_all_zeta_unguarded))

macro "move_norm_all_zeta" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (move_auto_base_guard; move_norm_all_zeta_unguarded [$hs,*]))

macro "move_norm_all_zeta" &"only"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (move_auto_base_guard; move_norm_all_zeta_unguarded only [$hs,*]))

macro "move_norm_channels"
    &"only" "[" rewrites:Lean.Parser.Tactic.simpLemma,* "]"
    &"unfold" "[" unfolds:ident,* "]"
    &"effects" "[" effectIds:ident,* "]" : tactic => do
  let unfoldLemmas ← unfolds.getElems.mapM fun id =>
    `(Lean.Parser.Tactic.simpLemma| $id:ident)
  let effectLemmas ← effectIds.getElems.mapM fun id =>
    `(Lean.Parser.Tactic.simpLemma| $id:ident)
  let hints := rewrites.getElems ++ unfoldLemmas ++ effectLemmas
  `(tactic|
    simp -zeta only
      [move_auto_base, move_effect, Prover.MoveAuto.reduceBoundedNatVal, $hints:simpLemma,*])

macro "move_norm_all_channels"
    &"only" "[" rewrites:Lean.Parser.Tactic.simpLemma,* "]"
    &"unfold" "[" unfolds:ident,* "]"
    &"effects" "[" effectIds:ident,* "]" : tactic => do
  let unfoldLemmas ← unfolds.getElems.mapM fun id =>
    `(Lean.Parser.Tactic.simpLemma| $id:ident)
  let effectLemmas ← effectIds.getElems.mapM fun id =>
    `(Lean.Parser.Tactic.simpLemma| $id:ident)
  let hints := rewrites.getElems ++ unfoldLemmas ++ effectLemmas
  `(tactic|
    simp_all -zeta only
      [move_auto_base, move_effect, Prover.MoveAuto.reduceBoundedNatVal, $hints:simpLemma,*])

macro "move_norm_all_zeta_channels"
    &"only" "[" rewrites:Lean.Parser.Tactic.simpLemma,* "]"
    &"unfold" "[" unfolds:ident,* "]"
    &"effects" "[" effectIds:ident,* "]" : tactic => do
  let unfoldLemmas ← unfolds.getElems.mapM fun id =>
    `(Lean.Parser.Tactic.simpLemma| $id:ident)
  let effectLemmas ← effectIds.getElems.mapM fun id =>
    `(Lean.Parser.Tactic.simpLemma| $id:ident)
  let hints := rewrites.getElems ++ unfoldLemmas ++ effectLemmas
  `(tactic|
    simp_all (config := { zetaDelta := true }) only
      [move_auto_base, move_effect, Prover.MoveAuto.reduceBoundedNatVal, $hints:simpLemma,*])

macro "abort_obtain" h:ident : tactic =>
  `(tactic| try move_norm at $h:ident)

macro "abort_obtain" h:ident
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| try move_norm [$hs,*] at $h:ident)

macro "abort_obtain" h:ident &"only"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| try move_norm only [$hs,*] at $h:ident)

macro "abort_obtain" h:ident "with" p:rcasesPat : tactic =>
  `(tactic| ((try move_norm at $h:ident); rcases $h:ident with $p))

macro "abort_obtain" h:ident
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" "with" p:rcasesPat : tactic =>
  `(tactic| ((try move_norm [$hs,*] at $h:ident); rcases $h:ident with $p))

macro "abort_obtain" h:ident &"only"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" "with" p:rcasesPat : tactic =>
  `(tactic| ((try move_norm only [$hs,*] at $h:ident); rcases $h:ident with $p))

macro "mutation_obtain" h:ident "with" p:rcasesPat : tactic =>
  `(tactic|
    (rw [Prover.MoveAuto.mutation_eq_iff] at $h:ident
     rcases $h:ident with $p))

macro "move_frame" : tactic =>
  `(tactic|
    (apply (Prover.MoveAuto.mutation_eq_iff _ _).2
     refine ⟨?_, ?_, ?_⟩ <;> try move_norm <;> try assumption))

macro "move_frame" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (apply (Prover.MoveAuto.mutation_eq_iff _ _).2
     refine ⟨?_, ?_, ?_⟩ <;> try move_norm [$hs,*] <;> try assumption))

macro "move_frame" &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (apply (Prover.MoveAuto.mutation_eq_iff _ _).2
     refine ⟨?_, ?_, ?_⟩ <;> try move_norm only [$hs,*] <;> try assumption))

macro "move_mutation_ext" : tactic =>
  `(tactic| move_frame)

macro "move_mutation_ext" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| move_frame [$hs,*])

macro "move_mutation_ext" &"only"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| move_frame only [$hs,*])

namespace Prover.MoveAuto

open Lean Elab Tactic Meta

/-! ### `move_pow_bound`: the numeral power-bound rung

Derives the monotone facts that no other rung can produce, then hands the
LINEAR residue to omega. Everything it asserts is a kernel-checked application
of the `pow_le_of_*` / `exponent_le_of_*` lemmas above instantiated at
numerals, so the rung adds no trust: it is a checked rung, not an oracle.

Three fact families, all keyed on a numeral appearing where the generic
solvers see an opaque atom:

1. literal base, symbolic exponent -- an exponent bound `x ≤ n` in context
   becomes the closed bound `b ^ x ≤ b^n` (and `b^n ≤ b ^ x` from `n ≤ x`),
   plus the unconditional `0 < b ^ x`;
2. symbolic base, literal exponent -- a base bound `x ≤ c` becomes `x ^ n ≤ c^n`;
3. the converse -- a hypothesis `b ^ x < K` with numeral `b`, `K` becomes the
   linear `x ≤ m` for the largest `m` the ceiling permits.

The rung never invents a bound: every fact is derived from a hypothesis that is
already in the (pruned) context, and the numerals are computed here so omega
never has to evaluate `^` itself. -/

/-- Bit ceiling on any numeral this rung will materialize. -/
private def powBitCap : Nat := 4096

/-- Cap on asserted facts, so a context with many powers cannot blow up. -/
private def powFactCap : Nat := 12

private partial def powClosedNat? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | .mdata _ b => powClosedNat? b
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then powClosedNat? e.getAppArgs[1]!
    else if e.isAppOfArity ``HAdd.hAdd 6 then
      match powClosedNat? e.getAppArgs[4]!, powClosedNat? e.getAppArgs[5]! with
      | some a, some b => some (a + b)
      | _, _ => none
    else if e.isAppOfArity ``HMul.hMul 6 then
      match powClosedNat? e.getAppArgs[4]!, powClosedNat? e.getAppArgs[5]! with
      | some a, some b => if a * b < 2 ^ powBitCap then some (a * b) else none
      | _, _ => none
    else if e.isAppOfArity ``HSub.hSub 6 then
      match powClosedNat? e.getAppArgs[4]!, powClosedNat? e.getAppArgs[5]! with
      | some a, some b => some (a - b)
      | _, _ => none
    else if e.isAppOfArity ``HPow.hPow 6 then
      match powClosedNat? e.getAppArgs[4]!, powClosedNat? e.getAppArgs[5]! with
      | some a, some b =>
        if b ≤ powBitCap && a ^ b < 2 ^ powBitCap then some (a ^ b) else none
      | _, _ => none
    else none

/-- `(whole, base, exponent)` for every `Nat` power subterm. -/
private partial def collectPowAtoms (e : Expr) (acc : Array (Expr × Expr × Expr)) :
    Array (Expr × Expr × Expr) :=
  let acc :=
    if e.isAppOfArity ``HPow.hPow 6 then
      let a := e.getAppArgs
      if a[0]!.isConstOf ``Nat && a[1]!.isConstOf ``Nat then acc.push (e, a[4]!, a[5]!)
      else acc
    else if e.isAppOfArity ``Nat.pow 2 then
      let a := e.getAppArgs
      acc.push (e, a[0]!, a[1]!)
    else acc
  match e with
  | .app f a => collectPowAtoms a (collectPowAtoms f acc)
  | .lam _ t b _ => collectPowAtoms b (collectPowAtoms t acc)
  | .forallE _ t b _ => collectPowAtoms b (collectPowAtoms t acc)
  | .letE _ t v b _ => collectPowAtoms b (collectPowAtoms v (collectPowAtoms t acc))
  | .mdata _ b => collectPowAtoms b acc
  | .proj _ _ b => collectPowAtoms b acc
  | _ => acc

private def powNameMentions (n : Name) : Bool :=
  n == ``HPow.hPow || n == ``Nat.pow || (n.toString.splitOn "pow").length > 1

/-- Relevance = there is something the rung could ACT on. A Move-level power
(`U64.pow`, `U64.pow.aborts`, ...) counts even before normalization, because the
`move_effect` bridge turns it into a Nat power. A raw `HPow.hPow` counts only
when it is not already a closed numeral -- otherwise EVERY leaf qualifies, since
every Move scalar type is spelled `BoundedNat (2^64)`. -/
private def powMentions (e : Expr) : Bool :=
  let moveLevel := Option.isSome <| e.find? fun s =>
    match s with
    | .const n _ => n != ``HPow.hPow && n != ``Nat.pow && powNameMentions n
    | _ => false
  moveLevel ||
    (collectPowAtoms e #[]).any fun (_, base, exp) =>
      (powClosedNat? base).isNone || (powClosedNat? exp).isNone

private inductive PowCmp where
  | le | lt
  deriving BEq, Inhabited

private def powComparison? (ty : Expr) : Option (PowCmp × Expr × Expr) :=
  if ty.isAppOfArity ``LE.le 4 then
    let a := ty.getAppArgs
    if a[0]!.isConstOf ``Nat then some (.le, a[2]!, a[3]!) else none
  else if ty.isAppOfArity ``LT.lt 4 then
    let a := ty.getAppArgs
    if a[0]!.isConstOf ``Nat then some (.lt, a[2]!, a[3]!) else none
  else if ty.isAppOfArity ``Nat.le 2 then
    let a := ty.getAppArgs
    some (.le, a[0]!, a[1]!)
  else if ty.isAppOfArity ``Nat.lt 2 then
    let a := ty.getAppArgs
    some (.lt, a[0]!, a[1]!)
  else none

private def powNatLE (a b : Expr) : MetaM Expr := mkAppM ``LE.le #[a, b]
private def powNatLT (a b : Expr) : MetaM Expr := mkAppM ``LT.lt #[a, b]

/-- Smallest `m` with `K ≤ b ^ (m+1)` (`strict`, i.e. from `b ^ x < K`), resp.
`K < b ^ (m+1)` (from `b ^ x ≤ K`). -/
private def powExponentCeil (b K : Nat) (strict : Bool) : Option Nat := Id.run do
  if b < 2 then return none
  let mut p := b
  let mut m := 0
  for _ in [:powBitCap] do
    if (if strict then K ≤ p else K < p) then return some m
    if p ≥ 2 ^ powBitCap then return none
    p := p * b
    m := m + 1
  return none

def powBoundFacts : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let mut atoms := collectPowAtoms target #[]
  let mut hyps : Array (Expr × Expr) := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if ty.hasLooseBVars then continue
    hyps := hyps.push (decl.toExpr, ty)
    atoms := collectPowAtoms ty atoms
  let mut seen : Array Expr := #[]
  let mut uniq : Array (Expr × Expr × Expr) := #[]
  for (whole, base, exp) in atoms do
    unless seen.any (· == whole) do
      seen := seen.push whole
      uniq := uniq.push (whole, base, exp)
  let mut facts : Array Hypothesis := #[]
  -- (1) literal base, symbolic exponent
  for (whole, base, exp) in uniq do
    if facts.size ≥ powFactCap then break
    let some b := powClosedNat? base | continue
    if b == 0 then continue
    if (powClosedNat? exp).isSome then continue
    let bE := mkNatLit b
    let hbpos ← mkDecideProof (← powNatLT (mkNatLit 0) bE)
    let posTy ← powNatLT (mkNatLit 0) whole
    let posPr ← mkAppOptM ``pow_pos_of_base_pos #[bE, exp, hbpos]
    facts := facts.push
      { userName := ← mkFreshUserName `h_pow_pos, type := posTy,
        value := ← mkExpectedTypeHint posPr posTy }
    for (fv, ty) in hyps do
      if facts.size ≥ powFactCap then break
      let some (cmp, lhs, rhs) := powComparison? (← whnfR ty) | continue
      if lhs == exp then
        let some n := powClosedNat? rhs | continue
        if cmp == .lt && n == 0 then continue
        let k := if cmp == .lt then n - 1 else n
        if k > powBitCap || b ^ k ≥ 2 ^ powBitCap then continue
        let L := b ^ k
        let hL ← mkAppOptM ``Nat.le_refl #[mkNatLit L]
        let lemName := if cmp == .lt then ``pow_le_of_exponent_lt else ``pow_le_of_exponent_le
        let pr ← mkAppOptM lemName #[bE, exp, mkNatLit n, mkNatLit L, hbpos, fv, hL]
        let ty' ← powNatLE whole (mkNatLit L)
        facts := facts.push
          { userName := ← mkFreshUserName `h_pow_le, type := ty',
            value := ← mkExpectedTypeHint pr ty' }
      else if rhs == exp then
        let some n := powClosedNat? lhs | continue
        let k := if cmp == .lt then n + 1 else n
        if k > powBitCap || b ^ k ≥ 2 ^ powBitCap then continue
        let L := b ^ k
        let hL ← mkAppOptM ``Nat.le_refl #[mkNatLit L]
        let lemName := if cmp == .lt then ``le_pow_of_exponent_gt else ``le_pow_of_exponent_ge
        let pr ← mkAppOptM lemName #[bE, exp, mkNatLit n, mkNatLit L, hbpos, fv, hL]
        let ty' ← powNatLE (mkNatLit L) whole
        facts := facts.push
          { userName := ← mkFreshUserName `h_pow_ge, type := ty',
            value := ← mkExpectedTypeHint pr ty' }
  -- (2) symbolic base, literal exponent
  for (whole, base, exp) in uniq do
    if facts.size ≥ powFactCap then break
    if (powClosedNat? base).isSome then continue
    let some n := powClosedNat? exp | continue
    if n == 0 || n > powBitCap then continue
    for (fv, ty) in hyps do
      if facts.size ≥ powFactCap then break
      let some (cmp, lhs, rhs) := powComparison? (← whnfR ty) | continue
      unless lhs == base do continue
      let some c := powClosedNat? rhs | continue
      if cmp == .lt && c == 0 then continue
      let d := if cmp == .lt then c - 1 else c
      if d ^ n ≥ 2 ^ powBitCap then continue
      let L := d ^ n
      let hL ← mkAppOptM ``Nat.le_refl #[mkNatLit L]
      let lemName := if cmp == .lt then ``pow_le_of_base_lt else ``pow_le_of_base_le
      let pr ← mkAppOptM lemName #[mkNatLit c, base, mkNatLit n, mkNatLit L, fv, hL]
      let ty' ← powNatLE whole (mkNatLit L)
      facts := facts.push
        { userName := ← mkFreshUserName `h_pow_base, type := ty',
          value := ← mkExpectedTypeHint pr ty' }
  -- (3) converse: a numeral ceiling on a power bounds its exponent
  for (fv, ty) in hyps do
    if facts.size ≥ powFactCap then break
    let some (cmp, lhs, rhs) := powComparison? (← whnfR ty) | continue
    let some (whole, base, exp) := (collectPowAtoms lhs #[])[0]? | continue
    unless whole == lhs do continue
    let some b := powClosedNat? base | continue
    if (powClosedNat? exp).isSome then continue
    let some K := powClosedNat? rhs | continue
    let some m := powExponentCeil b K (cmp == .lt) | continue
    let bE := mkNatLit b
    let hbpos ← mkDecideProof (← powNatLT (mkNatLit 0) bE)
    let powSucc ← mkAppM ``HPow.hPow #[bE, mkNatLit (m + 1)]
    let hmTy ←
      if cmp == .lt then powNatLE (mkNatLit K) powSucc else powNatLT (mkNatLit K) powSucc
    let hm ← mkDecideProof hmTy
    let lemName := if cmp == .lt then ``exponent_le_of_pow_lt else ``exponent_le_of_pow_le
    let pr ← mkAppOptM lemName #[bE, exp, mkNatLit m, mkNatLit K, hbpos, fv, hm]
    let ty' ← powNatLE exp (mkNatLit m)
    facts := facts.push
      { userName := ← mkFreshUserName `h_exp_le, type := ty',
        value := ← mkExpectedTypeHint pr ty' }
  if facts.isEmpty then
    throwError "move_pow_bound: no numeral power bound to derive"
  let (_, goal) ← goal.assertHypotheses facts
  replaceMainGoal [goal]

/-- Microsecond relevance test, so the rung costs nothing on the (large)
majority of leaves that mention no power at all. -/
def powBoundRelevant : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let mut relevant := powMentions (← goal.getType)
  unless relevant do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      -- let-VALUES matter: a leaf whose goal is `0 < pow10.val` mentions the
      -- power only through the let spine.
      if powMentions decl.type || decl.value?.any powMentions then
        relevant := true
        break
  unless relevant do
    throwError "move_pow_bound: goal mentions no power"

end Prover.MoveAuto

open Lean Elab Tactic Meta in
elab "move_pow_facts" : tactic => Prover.MoveAuto.powBoundFacts

open Lean Elab Tactic Meta in
elab "move_pow_guard" : tactic => Prover.MoveAuto.powBoundRelevant

/-- Monotone numeral power bounds, then omega on the linear residue. The four
normalization stages mirror the generic rungs: a leaf whose power is already
exposed pays nothing, one behind a `move_effect` bridge (e.g.
`U64Pow.pow_no_abort_iff`) pays one simp, one behind a `let` spine pays the
zeta variant. -/
macro "move_pow_bound" : tactic =>
  `(tactic|
    (move_pow_guard
     first
       | (move_pow_facts; omega)
       | ((try move_norm_unguarded); move_pow_facts; omega)
       | ((try move_norm_all_unguarded); move_pow_facts; omega)
       | ((try move_norm_all_zeta_unguarded); move_pow_facts; omega)))

macro "move_auto" "(" &"solver" ":=" &"simp" ")" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 50000 in (move_norm; done))
    | (set_option maxHeartbeats 100000 in (move_norm_all; done))
    | (set_option maxHeartbeats 150000 in (move_norm_all_zeta; done))
    | fail "move_auto simp normalization did not close the goal")

macro "move_auto" "(" &"solver" ":=" &"simp" ")"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 50000 in (move_norm [$hs,*]; done))
    | (set_option maxHeartbeats 100000 in (move_norm_all [$hs,*]; done))
    | (set_option maxHeartbeats 150000 in (move_norm_all_zeta [$hs,*]; done))
    | fail "move_auto simp normalization did not close the goal")

macro "move_auto" "(" &"solver" ":=" &"simp" ")"
    &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 50000 in (move_norm only [$hs,*]; done))
    | (set_option maxHeartbeats 100000 in (move_norm_all only [$hs,*]; done))
    | (set_option maxHeartbeats 150000 in (move_norm_all_zeta only [$hs,*]; done))
    | fail "move_auto simp normalization did not close the goal")

/-! ### Rung-pinned checked solvers

`(rung := arith | target | all | zeta)` selects ONE rung of the solver's ladder,
with that rung's own heartbeat cap, and fails if it does not close the goal. The
rung names are the normalization levels the ladder already climbs (`arith` is
omega's `move_checked_arith` rung, which normalizes nothing). A rung-less pinned
form stays valid and keeps running the whole ladder, so existing durable proofs
are unaffected; a rung-pinned durable proof pays only its winning rung on every
rebuild instead of replaying every failing rung before it, which is what a
whole-corpus recheck actually costs at scale.

Each rung expands to the ladder entry `move_auto?` reports as its winning
candidate, so a discovered invocation replays the discovered work and nothing
else. The one deliberate difference: a rung whose solver step runs after
normalization applies it under `all_goals`, so a pinned rung still closes if
normalization alone later becomes strong enough to finish the goal. Without that,
a stronger summary set could break an existing pinned proof by leaving its solver
with no goals.

The rung-LESS pinned forms now carry the same `all_goals` wrapper. They did not,
and that was the one live way a strengthened `move_auto_base` could break durable
proof text: `((try move_norm); move_bn_props; omega)` fails outright the moment
normalization alone closes the goal, because `move_bn_props` needs a main goal to
read. Since `all_goals` on one goal is that goal and on zero goals is success,
the wrapper can only turn a failure into a success. -/

macro "move_auto" "(" &"solver" ":=" &"simp" ")"
    "(" &"rung" ":=" selectedRung:ident ")" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `target => `(tactic| set_option maxHeartbeats 50000 in (move_norm; done))
    | `all => `(tactic| set_option maxHeartbeats 100000 in (move_norm_all; done))
    | `zeta => `(tactic| set_option maxHeartbeats 150000 in (move_norm_all_zeta; done))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | $selected:tactic
    | fail "move_auto simp did not close the selected rung")

macro "move_auto" "(" &"solver" ":=" &"simp" ")"
    "(" &"rung" ":=" selectedRung:ident ")"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `target => `(tactic| set_option maxHeartbeats 50000 in (move_norm [$hs,*]; done))
    | `all => `(tactic| set_option maxHeartbeats 100000 in (move_norm_all [$hs,*]; done))
    | `zeta =>
        `(tactic| set_option maxHeartbeats 150000 in (move_norm_all_zeta [$hs,*]; done))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | $selected:tactic
    | fail "move_auto simp did not close the selected rung")

macro "move_auto" "(" &"solver" ":=" &"simp" ")"
    "(" &"rung" ":=" selectedRung:ident ")"
    &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `target => `(tactic| set_option maxHeartbeats 50000 in (move_norm only [$hs,*]; done))
    | `all =>
        `(tactic| set_option maxHeartbeats 100000 in (move_norm_all only [$hs,*]; done))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 150000 in (move_norm_all_zeta only [$hs,*]; done))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | $selected:tactic
    | fail "move_auto simp did not close the selected rung")

macro "move_auto" "(" &"solver" ":=" &"omega" ")" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 100000 in move_checked_arith)
    | (set_option maxHeartbeats 100000 in ((try move_norm); all_goals (move_bn_props; omega)))
    | (set_option maxHeartbeats 150000 in ((try move_norm_all); all_goals (move_bn_props; omega)))
    | (set_option maxHeartbeats 200000 in ((try move_norm_all_zeta); all_goals (move_bn_props; omega)))
    | fail "move_auto omega did not close the normalized goal")

macro "move_auto" "(" &"solver" ":=" &"omega" ")"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 100000 in move_checked_arith)
    | (set_option maxHeartbeats 100000 in ((try move_norm [$hs,*]); all_goals (move_bn_props; omega)))
    | (set_option maxHeartbeats 150000 in ((try move_norm_all [$hs,*]); all_goals (move_bn_props; omega)))
    | (set_option maxHeartbeats 200000 in ((try move_norm_all_zeta [$hs,*]); all_goals (move_bn_props; omega)))
    | fail "move_auto omega did not close the normalized goal")

macro "move_auto" "(" &"solver" ":=" &"omega" ")"
    &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 100000 in move_checked_arith)
    | (set_option maxHeartbeats 100000 in ((try move_norm only [$hs,*]); all_goals (move_bn_props; omega)))
    | (set_option maxHeartbeats 150000 in ((try move_norm_all only [$hs,*]); all_goals (move_bn_props; omega)))
    | (set_option maxHeartbeats 200000 in ((try move_norm_all_zeta only [$hs,*]); all_goals (move_bn_props; omega)))
    | fail "move_auto omega did not close the normalized goal")

macro "move_auto" "(" &"solver" ":=" &"omega" ")"
    "(" &"rung" ":=" selectedRung:ident ")" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `arith => `(tactic| set_option maxHeartbeats 100000 in move_checked_arith)
    | `target =>
        `(tactic|
          set_option maxHeartbeats 100000 in
            ((try move_norm); all_goals (move_bn_props; omega)))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 150000 in
            ((try move_norm_all); all_goals (move_bn_props; omega)))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 200000 in
            ((try move_norm_all_zeta); all_goals (move_bn_props; omega)))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | $selected:tactic
    | fail "move_auto omega did not close the selected rung")

macro "move_auto" "(" &"solver" ":=" &"omega" ")"
    "(" &"rung" ":=" selectedRung:ident ")"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `arith => `(tactic| set_option maxHeartbeats 100000 in move_checked_arith)
    | `target =>
        `(tactic|
          set_option maxHeartbeats 100000 in
            ((try move_norm [$hs,*]); all_goals (move_bn_props; omega)))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 150000 in
            ((try move_norm_all [$hs,*]); all_goals (move_bn_props; omega)))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 200000 in
            ((try move_norm_all_zeta [$hs,*]); all_goals (move_bn_props; omega)))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | $selected:tactic
    | fail "move_auto omega did not close the selected rung")

macro "move_auto" "(" &"solver" ":=" &"omega" ")"
    "(" &"rung" ":=" selectedRung:ident ")"
    &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `arith => `(tactic| set_option maxHeartbeats 100000 in move_checked_arith)
    | `target =>
        `(tactic|
          set_option maxHeartbeats 100000 in
            ((try move_norm only [$hs,*]); all_goals (move_bn_props; omega)))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 150000 in
            ((try move_norm_all only [$hs,*]); all_goals (move_bn_props; omega)))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 200000 in
            ((try move_norm_all_zeta only [$hs,*]); all_goals (move_bn_props; omega)))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | $selected:tactic
    | fail "move_auto omega did not close the selected rung")

macro "move_auto" "(" &"solver" ":=" &"grind" ")" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 150000 in ((try move_norm); all_goals grind only))
    | (set_option maxHeartbeats 200000 in ((try move_norm_all); all_goals grind only))
    | (set_option maxHeartbeats 250000 in ((try move_norm_all_zeta); all_goals grind only))
    | fail "move_auto grind did not close the normalized goal")

macro "move_auto" "(" &"solver" ":=" &"grind" ")"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 150000 in ((try move_norm [$hs,*]); all_goals grind only))
    | (set_option maxHeartbeats 200000 in ((try move_norm_all [$hs,*]); all_goals grind only))
    | (set_option maxHeartbeats 250000 in ((try move_norm_all_zeta [$hs,*]); all_goals grind only))
    | fail "move_auto grind did not close the normalized goal")

macro "move_auto" "(" &"solver" ":=" &"grind" ")"
    &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 150000 in ((try move_norm only [$hs,*]); all_goals grind only))
    | (set_option maxHeartbeats 200000 in ((try move_norm_all only [$hs,*]); all_goals grind only))
    | (set_option maxHeartbeats 250000 in ((try move_norm_all_zeta only [$hs,*]); all_goals grind only))
    | fail "move_auto grind did not close the normalized goal")

macro "move_auto" "(" &"solver" ":=" &"grind" ")"
    "(" &"rung" ":=" selectedRung:ident ")" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `target =>
        `(tactic|
          set_option maxHeartbeats 150000 in ((try move_norm); all_goals grind only))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 200000 in ((try move_norm_all); all_goals grind only))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 250000 in
            ((try move_norm_all_zeta); all_goals grind only))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | $selected:tactic
    | fail "move_auto grind did not close the selected rung")

macro "move_auto" "(" &"solver" ":=" &"grind" ")"
    "(" &"rung" ":=" selectedRung:ident ")"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `target =>
        `(tactic|
          set_option maxHeartbeats 150000 in
            ((try move_norm [$hs,*]); all_goals grind only))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 200000 in
            ((try move_norm_all [$hs,*]); all_goals grind only))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 250000 in
            ((try move_norm_all_zeta [$hs,*]); all_goals grind only))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | $selected:tactic
    | fail "move_auto grind did not close the selected rung")

macro "move_auto" "(" &"solver" ":=" &"grind" ")"
    "(" &"rung" ":=" selectedRung:ident ")"
    &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `target =>
        `(tactic|
          set_option maxHeartbeats 150000 in
            ((try move_norm only [$hs,*]); all_goals grind only))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 200000 in
            ((try move_norm_all only [$hs,*]); all_goals grind only))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 250000 in
            ((try move_norm_all_zeta only [$hs,*]); all_goals grind only))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | $selected:tactic
    | fail "move_auto grind did not close the selected rung")

macro "move_auto" "(" &"solver" ":=" &"aesop" ")" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 50000 in (move_norm; done))
    | (set_option maxHeartbeats 150000 in ((try move_norm); all_goals move_aesop))
    | (set_option maxHeartbeats 100000 in (move_norm_all; done))
    | (set_option maxHeartbeats 200000 in ((try move_norm_all); all_goals move_aesop))
    | (set_option maxHeartbeats 150000 in (move_norm_all_zeta; done))
    | (set_option maxHeartbeats 250000 in ((try move_norm_all_zeta); all_goals move_aesop))
    | fail "move_auto Aesop did not close the normalized goal")

macro "move_auto" "(" &"solver" ":=" &"aesop" ")"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 50000 in (move_norm [$hs,*]; done))
    | (set_option maxHeartbeats 150000 in ((try move_norm [$hs,*]); all_goals move_aesop))
    | (set_option maxHeartbeats 100000 in (move_norm_all [$hs,*]; done))
    | (set_option maxHeartbeats 200000 in ((try move_norm_all [$hs,*]); all_goals move_aesop))
    | (set_option maxHeartbeats 150000 in (move_norm_all_zeta [$hs,*]; done))
    | (set_option maxHeartbeats 250000 in ((try move_norm_all_zeta [$hs,*]); all_goals move_aesop))
    | fail "move_auto Aesop did not close the normalized goal")

macro "move_auto" "(" &"solver" ":=" &"aesop" ")"
    &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 50000 in (move_norm only [$hs,*]; done))
    | (set_option maxHeartbeats 150000 in ((try move_norm only [$hs,*]); all_goals move_aesop))
    | (set_option maxHeartbeats 100000 in (move_norm_all only [$hs,*]; done))
    | (set_option maxHeartbeats 200000 in ((try move_norm_all only [$hs,*]); all_goals move_aesop))
    | (set_option maxHeartbeats 150000 in (move_norm_all_zeta only [$hs,*]; done))
    | (set_option maxHeartbeats 250000 in ((try move_norm_all_zeta only [$hs,*]); all_goals move_aesop))
    | fail "move_auto Aesop did not close the normalized goal")

-- The Aesop rungs are the Aesop entries alone. The rung-less ladder interleaves
-- the three plain-simp entries as a cheap pre-check; those are exactly the
-- `(solver := simp)` rungs, so pinning them here would replay simp twice.
macro "move_auto" "(" &"solver" ":=" &"aesop" ")"
    "(" &"rung" ":=" selectedRung:ident ")" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `target =>
        `(tactic|
          set_option maxHeartbeats 150000 in ((try move_norm); all_goals move_aesop))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 200000 in ((try move_norm_all); all_goals move_aesop))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 250000 in
            ((try move_norm_all_zeta); all_goals move_aesop))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | $selected:tactic
    | fail "move_auto Aesop did not close the selected rung")

macro "move_auto" "(" &"solver" ":=" &"aesop" ")"
    "(" &"rung" ":=" selectedRung:ident ")"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `target =>
        `(tactic|
          set_option maxHeartbeats 150000 in
            ((try move_norm [$hs,*]); all_goals move_aesop))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 200000 in
            ((try move_norm_all [$hs,*]); all_goals move_aesop))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 250000 in
            ((try move_norm_all_zeta [$hs,*]); all_goals move_aesop))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | $selected:tactic
    | fail "move_auto Aesop did not close the selected rung")

macro "move_auto" "(" &"solver" ":=" &"aesop" ")"
    "(" &"rung" ":=" selectedRung:ident ")"
    &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `target =>
        `(tactic|
          set_option maxHeartbeats 150000 in
            ((try move_norm only [$hs,*]); all_goals move_aesop))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 200000 in
            ((try move_norm_all only [$hs,*]); all_goals move_aesop))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 250000 in
            ((try move_norm_all_zeta only [$hs,*]); all_goals move_aesop))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | $selected:tactic
    | fail "move_auto Aesop did not close the selected rung")

macro "move_auto_z3_unguarded"
    "(" &"profile" ":=" selectedProfile:ident ")"
    "(" &"budget" ":=" selectedBudget:ident ")"
    &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]"
    &"facts" "[" factIds:ident,* "]"
    &"unfold" "[" unfolds:ident,* "]"
    &"defeq" "[" defeqs:ident,* "]" : tactic => do
  let profileTactic ← match selectedProfile.getId.eraseMacroScopes with
    | `target =>
        `(tactic|
          (try move_norm_unguarded only [$hs,*]
           move_bn_props
           move_z3 (budget := $selectedBudget)
             facts [$factIds,*] unfold [$unfolds,*] defeq [$defeqs,*]))
    | `all =>
        `(tactic|
          (try move_norm_all_unguarded only [$hs,*]
           move_bn_props
           move_z3 (budget := $selectedBudget)
             facts [$factIds,*] unfold [$unfolds,*] defeq [$defeqs,*]))
    | `zeta =>
        `(tactic|
          (try move_norm_all_zeta_unguarded only [$hs,*]
           move_bn_props
           move_z3 (budget := $selectedBudget)
             facts [$factIds,*] unfold [$unfolds,*] defeq [$defeqs,*]))
    | _ => Macro.throwUnsupported
  `(tactic| first
    | (set_option maxHeartbeats 2000000 in
        (apply Prover.MoveAuto.explicitZ3OracleResult <;>
          $profileTactic:tactic))
    | fail "move_auto trusted Z3 did not close the selected profile")

macro "move_auto" "(" &"solver" ":=" &"z3" ")"
    "(" &"profile" ":=" selectedProfile:ident ")"
    "(" &"budget" ":=" selectedBudget:ident ")"
    &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]"
    &"facts" "[" factIds:ident,* "]"
    &"unfold" "[" unfolds:ident,* "]"
    &"defeq" "[" defeqs:ident,* "]" : tactic =>
  `(tactic|
    (move_auto_base_guard
     move_auto_z3_unguarded
       (profile := $selectedProfile)
       (budget := $selectedBudget)
       only [$hs,*]
       facts [$factIds,*]
       unfold [$unfolds,*]
       defeq [$defeqs,*]))

macro "move_auto" "(" &"solver" ":=" &"z3" ")" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 500000 in
        (apply Prover.MoveAuto.explicitZ3OracleResult <;>
          (try move_norm_all_zeta) <;> move_bn_props <;> move_z3))
    | fail "move_auto trusted Z3 did not close the normalized goal")

macro "move_auto" "(" &"solver" ":=" &"z3" ")"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 500000 in
        (apply Prover.MoveAuto.explicitZ3OracleResult <;>
          (try move_norm_all_zeta [$hs,*]) <;> move_bn_props <;> move_z3))
    | fail "move_auto trusted Z3 did not close the normalized goal")

macro "move_auto" "(" &"solver" ":=" &"z3" ")"
    &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (set_option maxHeartbeats 500000 in
        (apply Prover.MoveAuto.explicitZ3OracleResult <;>
          (try move_norm_all_zeta only [$hs,*]) <;> move_bn_props <;> move_z3))
    | fail "move_auto trusted Z3 did not close the normalized goal")

/-! ### Explicit checked hint channels

The fixed channel order is part of the durable syntax. `only` contains ordinary
rewrites, `unfold` contains definitions, `rules` contains local solver rules,
and `effects` contains explicitly selected effect theorems. None of these forms
consults `move_summary`. Rules are accepted only by Aesop and grind; using them
with simp or omega fails during macro expansion rather than being ignored.
-/

macro "move_auto" "(" &"solver" ":=" &"simp" ")"
    "(" &"rung" ":=" selectedRung:ident ")"
    &"only" "[" rewrites:Lean.Parser.Tactic.simpLemma,* "]"
    &"unfold" "[" unfolds:ident,* "]"
    &"rules" "[" ruleIds:ident,* "]"
    &"effects" "[" effectIds:ident,* "]" : tactic => do
  unless ruleIds.getElems.isEmpty do
    Macro.throwError
      "move_auto's rules channel is unsupported by the simp solver; use aesop or grind"
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `target =>
        `(tactic|
          set_option maxHeartbeats 50000 in
            (move_norm_channels only [$rewrites,*]
              unfold [$unfolds,*] effects [$effectIds,*]; done))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 100000 in
            (move_norm_all_channels only [$rewrites,*]
              unfold [$unfolds,*] effects [$effectIds,*]; done))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 150000 in
            (move_norm_all_zeta_channels only [$rewrites,*]
              unfold [$unfolds,*] effects [$effectIds,*]; done))
    | _ => Macro.throwUnsupported
  `(tactic|
    (move_auto_base_guard
     first
     | $selected:tactic
     | fail "move_auto simp did not close the selected checked-channel rung"))

macro "move_auto" "(" &"solver" ":=" &"omega" ")"
    "(" &"rung" ":=" selectedRung:ident ")"
    &"only" "[" rewrites:Lean.Parser.Tactic.simpLemma,* "]"
    &"unfold" "[" unfolds:ident,* "]"
    &"rules" "[" ruleIds:ident,* "]"
    &"effects" "[" effectIds:ident,* "]" : tactic => do
  unless ruleIds.getElems.isEmpty do
    Macro.throwError
      "move_auto's rules channel is unsupported by the omega solver; use aesop or grind"
  if selectedRung.getId.eraseMacroScopes == `arith &&
      (!rewrites.getElems.isEmpty || !unfolds.getElems.isEmpty ||
        !effectIds.getElems.isEmpty) then
    Macro.throwError
      "move_auto's arith rung does not normalize hint channels; use target, all, or zeta"
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `arith => `(tactic| set_option maxHeartbeats 100000 in move_checked_arith)
    | `target =>
        `(tactic|
          set_option maxHeartbeats 100000 in
            ((try move_norm_channels only [$rewrites,*]
              unfold [$unfolds,*] effects [$effectIds,*]);
             all_goals (move_bn_props; omega)))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 150000 in
            ((try move_norm_all_channels only [$rewrites,*]
              unfold [$unfolds,*] effects [$effectIds,*]);
             all_goals (move_bn_props; omega)))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 200000 in
            ((try move_norm_all_zeta_channels only [$rewrites,*]
              unfold [$unfolds,*] effects [$effectIds,*]);
             all_goals (move_bn_props; omega)))
    | _ => Macro.throwUnsupported
  `(tactic|
    (move_auto_base_guard
     first
     | $selected:tactic
     | fail "move_auto omega did not close the selected checked-channel rung"))

macro "move_auto" "(" &"solver" ":=" &"aesop" ")"
    "(" &"rung" ":=" selectedRung:ident ")"
    &"only" "[" rewrites:Lean.Parser.Tactic.simpLemma,* "]"
    &"unfold" "[" unfolds:ident,* "]"
    &"rules" "[" ruleIds:ident,* "]"
    &"effects" "[" effectIds:ident,* "]" : tactic => do
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `target =>
        `(tactic|
          set_option maxHeartbeats 150000 in
            ((try move_norm_channels only [$rewrites,*]
              unfold [$unfolds,*] effects [$effectIds,*]);
             all_goals move_aesop_rules [$ruleIds,*]))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 200000 in
            ((try move_norm_all_channels only [$rewrites,*]
              unfold [$unfolds,*] effects [$effectIds,*]);
             all_goals move_aesop_rules [$ruleIds,*]))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 250000 in
            ((try move_norm_all_zeta_channels only [$rewrites,*]
              unfold [$unfolds,*] effects [$effectIds,*]);
             all_goals move_aesop_rules [$ruleIds,*]))
    | _ => Macro.throwUnsupported
  `(tactic|
    (move_auto_base_guard
     first
     | $selected:tactic
     | fail "move_auto Aesop did not close the selected checked-channel rung"))

macro "move_auto" "(" &"solver" ":=" &"grind" ")"
    "(" &"rung" ":=" selectedRung:ident ")"
    &"only" "[" rewrites:Lean.Parser.Tactic.simpLemma,* "]"
    &"unfold" "[" unfolds:ident,* "]"
    &"rules" "[" ruleIds:ident,* "]"
    &"effects" "[" effectIds:ident,* "]" : tactic => do
  let grindRules ← ruleIds.getElems.mapM fun id =>
    `(Lean.Parser.Tactic.grindParam| $id:ident)
  let grindTactic ←
    if ruleIds.getElems.isEmpty then
      `(tactic| grind only)
    else
      `(tactic| grind only [$grindRules,*])
  let selected ← match selectedRung.getId.eraseMacroScopes with
    | `target =>
        `(tactic|
          set_option maxHeartbeats 150000 in
            ((try move_norm_channels only [$rewrites,*]
              unfold [$unfolds,*] effects [$effectIds,*]);
             all_goals $grindTactic:tactic))
    | `all =>
        `(tactic|
          set_option maxHeartbeats 200000 in
            ((try move_norm_all_channels only [$rewrites,*]
              unfold [$unfolds,*] effects [$effectIds,*]);
             all_goals $grindTactic:tactic))
    | `zeta =>
        `(tactic|
          set_option maxHeartbeats 250000 in
            ((try move_norm_all_zeta_channels only [$rewrites,*]
              unfold [$unfolds,*] effects [$effectIds,*]);
             all_goals $grindTactic:tactic))
    | _ => Macro.throwUnsupported
  `(tactic|
    (move_auto_base_guard
     first
     | $selected:tactic
     | fail "move_auto grind did not close the selected checked-channel rung"))

declare_syntax_cat moveAutoCaseSplit
syntax binderIdent " : " term : moveAutoCaseSplit

declare_syntax_cat moveAutoGuardSplit
syntax ident " : " term : moveAutoGuardSplit

declare_syntax_cat moveAutoCheckedSolver
syntax ident : moveAutoCheckedSolver

syntax "move_auto" &"cases" "[" moveAutoCaseSplit,* "]"
    "using" "(" &"solver" ":=" moveAutoCheckedSolver ")" "(" &"rung" ":=" ident ")"
    &"only" "[" Lean.Parser.Tactic.simpLemma,* "]"
    &"unfold" "[" ident,* "]"
    &"rules" "[" ident,* "]"
    &"effects" "[" ident,* "]" : tactic

syntax "move_auto" &"guards" "[" moveAutoGuardSplit,* "]"
    "using" "(" &"solver" ":=" moveAutoCheckedSolver ")" "(" &"rung" ":=" ident ")"
    &"only" "[" Lean.Parser.Tactic.simpLemma,* "]"
    &"unfold" "[" ident,* "]"
    &"rules" "[" ident,* "]"
    &"effects" "[" ident,* "]" : tactic

def moveAbortUnfoldingKeyword :=
  leading_parser (Lean.Parser.nonReservedSymbol "unfolding" true)

declare_syntax_cat moveAbortUnfoldingClause
syntax moveAbortUnfoldingKeyword "[" term,* "]" : moveAbortUnfoldingClause

def moveAbortTermBeforeUnfolding : Lean.Parser.Parser :=
  -- `withForbidden` only stops registered tokens, so register `unfolding`
  -- inside this parser's private context rather than in the importing module.
  Lean.Parser.withFn
    (Lean.Parser.adaptUncacheableContextFn fun c =>
      { c with
        tokens := c.tokens.insert "unfolding" "unfolding"
        forbiddenTk? := some "unfolding" })
    Lean.Parser.termParser

syntax (name := abortFrom)
  "abort_from " ident (moveAbortUnfoldingClause)? : tactic

namespace Prover.MoveAuto

open Lean Elab Tactic Meta

private partial def exprSize : Expr → Nat
  | .app f a => exprSize f + exprSize a + 1
  | .lam _ type body _ | .forallE _ type body _ =>
    exprSize type + exprSize body + 1
  | .letE _ type value body _ =>
    exprSize type + exprSize value + exprSize body + 1
  | .mdata _ body | .proj _ _ body => exprSize body + 1
  | _ => 1

private partial def collectConsts (e : Expr) (found : Array Name := #[]) :
    Array Name :=
  match e with
  | .const name _ => if found.contains name then found else found.push name
  | .app f a => collectConsts a (collectConsts f found)
  | .lam _ type body _ | .forallE _ type body _ =>
    collectConsts body (collectConsts type found)
  | .letE _ type value body _ =>
    collectConsts body (collectConsts value (collectConsts type found))
  | .mdata _ body | .proj _ _ body => collectConsts body found
  | _ => found

/-! ### `partial_fixpoint` reachability

`move_auto` refuses a leaf whose goal reaches a `partial_fixpoint` definition,
because the checked ladder cannot see through `Lean.Order.fix` and would either
diverge or leave a residual the author has to read anyway. The refusal is only
legitimate when the scan is CONCLUSIVE: an inconclusive scan reported as a
refusal turns every large-context goal into a millisecond "no" for a reason that
has nothing to do with loops.

The earlier scan was not conclusive. It walked constants to depth 12 with a
single 256-constant budget SHARED across the target and every hypothesis type
and value, kept `visited` as an `Array Name` (so membership was a linear scan),
compared `name.toString` against `"Lean.Order.fix"` once per constant, and
treated budget exhaustion as a refusal. On a generated Move corpus every goal
mentions an `.aborts` chain, so the budget was gone almost immediately: measured
on ember, 125 of 190 small-body leaves and 30 of 33 large World/Mutation leaves
were refused for exhaustion, against 8 and 2 genuine `Lean.Order.fix` findings.
The size policies below never ran at all, because exhaustion threw first.

This scan answers instead of giving up:

* one global `visited` hash set for the whole check, so the shared constant
  closure of the target and all hypotheses is walked ONCE, not once per
  hypothesis;
* an explicit worklist instead of bounded recursion, so there is no depth cap to
  mistake for an answer, and `Expr.getUsedConstants` (pointer-cached) does the
  per-value traversal, so a shared DAG is not re-walked exponentially;
* infrastructure constants are marked visited before they are classified, so the
  module-prefix test runs once per name rather than once per occurrence;
* a `Name` comparison instead of `toString` per constant.

Termination is by construction: every iteration either drops a name or expands a
not-yet-visited one, and the environment is finite. `partialFixpointConstantCeiling`
is a hard safety valve against a pathological environment, not a budget the
corpus is expected to touch, and tripping it is reported as its own refusal class
so it can never be silently confused with a real finding. Measured on ember it
fires zero times across 190 small-body leaves and 33 large World/Mutation
leaves. -/
private def partialFixpointConstantCeiling : Nat := 200000

private def partialFixpointCombinator : Name := `Lean.Order.fix

private structure PartialFixpointSearch where
  found : Bool := false
  exhausted : Bool := false
  visited : NameHashSet := {}
  remaining : Nat := partialFixpointConstantCeiling
  -- proximate carriers: definitions whose own value mentions `Lean.Order.fix`.
  -- These are the names sealing and summary harvesting key on; the scan keeps
  -- walking after a find so ALL carriers in the closure are collected.
  carriers : Array Name := #[]

private def isInfrastructureConstant (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some moduleIndex =>
      match env.header.moduleNames[moduleIndex.toNat]? with
      | none => false
      | some moduleName =>
          let moduleName := moduleName.toString
          #["Init.", "Lean.", "Std.", "Batteries.", "Aesop.", "Auto.",
            "Prelude.", "Prover."].any fun expectedPrefix =>
              moduleName.startsWith expectedPrefix

private def searchPartialFixpoint
    (env : Environment) (target : Expr)
    (state : PartialFixpointSearch) : PartialFixpointSearch := Id.run do
  if state.exhausted then
    return state
  let mut result := state
  let mut pending : Array Name := target.getUsedConstants
  while !pending.isEmpty do
    let some name := pending.back? | break
    pending := pending.pop
    if name == partialFixpointCombinator then
      -- the combinator appeared directly (no defn wrapper to attribute)
      result := { result with found := true }
      continue
    if result.visited.contains name then
      continue
    result := { result with visited := result.visited.insert name }
    if isInfrastructureConstant env name then
      continue
    if result.remaining == 0 then
      return { result with exhausted := true }
    result := { result with remaining := result.remaining - 1 }
    match env.find? name with
    | some (.defnInfo info) =>
      let used := info.value.getUsedConstants
      if used.contains partialFixpointCombinator &&
          !result.carriers.contains name then
        result := { result with
          found := true
          carriers := result.carriers.push name }
        -- Stop at the first carrier: this restores the original early-exit
        -- cost exactly (the full-closure walk per leaf burned declaration
        -- heartbeat budgets on loop-heavy theorems). Sibling carriers (e.g.
        -- an `.aborts` twin) are usually summary-equivalent; collecting ALL
        -- carriers cheaply needs a per-constant reachability memo — do that
        -- before widening this.
        return result
      pending := pending ++ used
    | some (.opaqueInfo info) => pending := pending ++ info.value.getUsedConstants
    | _ => pure ()
  return result

private def scanPartialFixpoint
    (env : Environment) (target : Expr)
    (state : PartialFixpointSearch := {}) : PartialFixpointSearch :=
  searchPartialFixpoint env target state

private def containsStateType (e : Expr) : Bool :=
  (collectConsts e).any fun name =>
    name.toString == "Prover.Mutation.Mutation" ||
      name.toString == "Prover.World.World"

private def isDiscoverySignal (env : Environment) (name : Name) : Bool :=
  !Meta.isInstanceCore env name &&
    !#[
      `Eq, `HEq, `Iff, `And, `Or, `Not, `True, `False,
      `Nat, `Int, `Bool, `List, `Option, `Prod, `Sum, `Unit, `PUnit,
      `Empty, `Subtype, `Sigma, `PSigma, `Decidable, `OfNat,
      `LT, `LE, `GT, `GE, `Add, `HAdd, `Sub, `HSub, `Mul, `HMul,
      `Div, `HDiv, `Mod, `HMod, `ite, `dite
    ].contains name.getRoot

private def simpAttributeDecls (attributeName : Name) : CoreM (Array Name) := do
  let some extension ← getSimpExtension? attributeName
    | return #[]
  let theorems ← extension.getTheorems
  let mut declarations := #[]
  for origin in theorems.lemmaNames.toList do
    if let .decl name _ _ := origin then
      unless declarations.contains name do
        declarations := declarations.push name
  return declarations

private structure RankedEffect where
  name : Name
  tier : Nat
  score : Nat

private structure EffectInfo where
  name : Name
  constants : Array Name
  targetHits : Nat
  contextHits : Nat

private def addBoundedBodyConstants
    (env : Environment) (initial : Array Name) : Array Name := Id.run do
  let mut discoveredConstants := initial
  let mut frontier := initial
  for _ in [0:2] do
    let mut next := #[]
    for name in frontier do
      if isInfrastructureConstant env name then
        continue
      let some (.defnInfo info) := env.find? name | continue
      if info.safety != .safe || (collectConsts info.value).contains name then
        continue
      for dependency in (collectConsts info.value).filter (isDiscoverySignal env) do
        unless discoveredConstants.contains dependency do
          discoveredConstants := discoveredConstants.push dependency
          next := next.push dependency
    frontier := next
  discoveredConstants

private def relevantEffectNames : TacticM (Array Name) := withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let env ← getEnv
  let mut targetConstants := (collectConsts target).filter (isDiscoverySignal env)
  let mut contextConstants := #[]
  for declaration in ← getLCtx do
    for name in (collectConsts declaration.type).filter (isDiscoverySignal env) do
      unless contextConstants.contains name do
        contextConstants := contextConstants.push name
    if let some value := declaration.value? then
      for name in (collectConsts value).filter (isDiscoverySignal env) do
        unless contextConstants.contains name do
          contextConstants := contextConstants.push name
  targetConstants := addBoundedBodyConstants env targetConstants
  contextConstants := addBoundedBodyConstants env contextConstants
  let mut candidates ← simpAttributeDecls `move_effect
  for name in ← simpAttributeDecls `move_summary do
    unless candidates.contains name do
      candidates := candidates.push name
  let mut infos : Array EffectInfo := #[]
  let mut targetTransitiveConstants := #[]
  let mut contextTransitiveConstants := #[]
  for name in candidates do
    let some info := env.find? name | continue
    let theoremConstants := (collectConsts info.type).filter (isDiscoverySignal env)
    let targetHits := theoremConstants.foldl (init := 0) fun count constant =>
      if targetConstants.contains constant then count + 1 else count
    let contextHits := theoremConstants.foldl (init := 0) fun count constant =>
      if contextConstants.contains constant then count + 1 else count
    infos := infos.push { name, constants := theoremConstants, targetHits, contextHits }
    if targetHits > 0 then
      for constant in theoremConstants do
        unless targetTransitiveConstants.contains constant do
          targetTransitiveConstants := targetTransitiveConstants.push constant
    if contextHits > 0 then
      for constant in theoremConstants do
        unless contextTransitiveConstants.contains constant do
          contextTransitiveConstants := contextTransitiveConstants.push constant
  let mut ranked : Array RankedEffect := #[]
  for info in infos do
    let targetTransitiveHits := info.constants.foldl (init := 0) fun count constant =>
      if targetTransitiveConstants.contains constant then count + 1 else count
    let contextTransitiveHits := info.constants.foldl (init := 0) fun count constant =>
      if contextTransitiveConstants.contains constant then count + 1 else count
    -- Target-direct > target one-hop > context-direct > context one-hop keeps
    -- target-derived bridges ahead of context-only facts under the 16-effect cap.
    let tier :=
      if info.targetHits > 0 then 4
      else if targetTransitiveHits > 0 then 3
      else if info.contextHits > 0 then 2
      else if contextTransitiveHits > 0 then 1
      else 0
    let score :=
      if tier == 4 then info.targetHits * 100 + info.contextHits * 10
      else if tier == 3 then targetTransitiveHits * 100 + info.contextHits
      else if tier == 2 then info.contextHits * 100 + contextTransitiveHits
      else contextTransitiveHits
    if tier > 0 then
      ranked := ranked.push { name := info.name, tier, score }
  let sorted := ranked.qsort fun (left right : RankedEffect) =>
    if left.tier != right.tier then
      left.tier > right.tier
    else if left.score == right.score then
      left.name.toString < right.name.toString
    else
      left.score > right.score
  return (sorted.toList.take 16).toArray.map (·.name)

private partial def isAbortContinuationOf (head : Name) : Name → Bool
  | name =>
    if name == head then
      true
    else
      match name with
      | .str parent suffix =>
          suffix.startsWith "cont_" && isAbortContinuationOf head parent
      | _ => false

private def unfoldableDiscoveryDef (env : Environment) (name : Name) : CoreM Bool := do
  if isInfrastructureConstant env name || Meta.isInstanceCore env name then
    return false
  match env.find? name with
  | some (.defnInfo info) =>
      if info.safety != .safe || (← isRecursiveDefinition name) then
        return false
      return !(collectConsts info.value).contains name
  | _ => return false

private structure RankedUnfold where
  name : Name
  tier : Nat

private def relevantUnfoldNames : TacticM (Array Name) := withMainContext do
  let goal ← getMainGoal
  let env ← getEnv
  let target ← instantiateMVars (← goal.getType)
  let targetConstants := collectConsts target
  let mut contextConstants := #[]
  let mut relevantContextConstants := #[]
  let relevant ← relevantFVars goal
  for declaration in ← getLCtx do
    let linked := relevant.contains declaration.fvarId
    let proposition ← Meta.isProp declaration.type
    if !linked && !proposition then
      continue
    for name in collectConsts declaration.type do
      unless contextConstants.contains name do
        contextConstants := contextConstants.push name
      if linked then
        unless relevantContextConstants.contains name do
          relevantContextConstants := relevantContextConstants.push name
    if let some value := declaration.value? then
      for name in collectConsts value do
        unless contextConstants.contains name do
          contextConstants := contextConstants.push name
        if linked then
          unless relevantContextConstants.contains name do
            relevantContextConstants := relevantContextConstants.push name
  let mut ranked : Array RankedUnfold := #[]
  let addCandidate := fun
      (ranked : Array RankedUnfold) (name : Name) (tier : Nat) =>
    match ranked.findIdx? (·.name == name) with
    | some index =>
      match ranked[index]? with
      | some previous =>
        if tier > previous.tier then
          ranked.setIfInBounds index { name, tier }
        else
          ranked
      | none => ranked
    | none => ranked.push { name, tier }
  for name in targetConstants do
    if ← unfoldableDiscoveryDef env name then
      ranked := addCandidate ranked name 4
  for name in contextConstants do
    if ← unfoldableDiscoveryDef env name then
      ranked := addCandidate ranked name
        (if relevantContextConstants.contains name then 3 else 2)
  -- Generated `.aborts.cont_*` helpers are not normally present in the goal:
  -- the generated head calls them from its body. Walk only that syntactic
  -- continuation family, for two bounded rounds, instead of recursively
  -- unfolding arbitrary dependencies.
  let direct := ranked
  for candidate in direct do
    let some (.defnInfo info) := env.find? candidate.name | continue
    let mut frontier := collectConsts info.value
    for depth in [0:2] do
      let mut next := #[]
      for name in frontier do
        if isAbortContinuationOf candidate.name name &&
            name != candidate.name &&
            (← unfoldableDiscoveryDef env name) then
          ranked := addCandidate ranked name (candidate.tier - (depth + 1))
          if let some (.defnInfo continuation) := env.find? name then
            for nested in collectConsts continuation.value do
              unless next.contains nested do
                next := next.push nested
      frontier := next
  let sorted := ranked.qsort fun (left right : RankedUnfold) =>
    if left.tier != right.tier then
      left.tier > right.tier
    else
      left.name.toString < right.name.toString
  -- Seal: never offer a definition whose closure reaches `Lean.Order.fix` to
  -- the unfold channel. Unfolding one reintroduces its recursive occurrence
  -- and the simp rungs churn their whole heartbeat budget on it; sealed, the
  -- loop application stays an uninterpreted atom that omega/grind/Z3 and
  -- harvested summaries can still reason about.
  let mut sealed : Array RankedUnfold := #[]
  for candidate in sorted do
    let scan := match env.find? candidate.name with
      | some (.defnInfo info) => scanPartialFixpoint env info.value
      | _ => ({} : PartialFixpointSearch)
    unless scan.found do
      sealed := sealed.push candidate
  return (sealed.toList.take 8).toArray.map (·.name)

/-- Tactic-position `set_option maxHeartbeats` is inert in Lean 4.32:
`CoreM.withOptions` refreshes `options`, `diag`, and `maxRecDepth` but not the
`Core.Context.maxHeartbeats` field, which is fixed once per declaration from
command-level options. Every per-rung budget in this file was therefore a
no-op, and a FAILING discovery ladder consumed whatever budget the enclosing
declaration granted (measured on the ember bomb leaf: ~1,200 individually
cheap simp attempts, wall time linear in the file budget, 13 s at 400k up to
204 s at 8M, never terminating on its own). This combinator makes a budget
real: it sets the context field and rebases the heartbeat counter. `budget`
is in option-scale units (the same numbers `set_option maxHeartbeats` takes). -/
private def withHeartbeatBudget (budget : Nat) (x : TacticM α) : TacticM α :=
  controlAt CoreM fun runInCore =>
    withReader (fun (ctx : Core.Context) => { ctx with maxHeartbeats := budget * 1000 }) <|
      Core.withCurrHeartbeats <| runInCore x

/-- `Core.tryCatch` -- and therefore EVERY `try`/`catch` written in `TacticM` --
deliberately re-throws "runtime" exceptions (`Lean.Exception.isRuntime`: the
`maxHeartbeats` timeout and `maxRecDepth`), so that a backtracking combinator
cannot silently swallow resource exhaustion. That is the right default for a
tactic that owns the whole declaration's budget, and exactly the wrong one for a
portfolio search whose rungs each run under a budget IT set: a rung that
exhausted its own sub-budget threw straight past the search's handler, past the
caller, and out of the tactic block -- so the ladder never reached its remaining
rungs and the leaf produced no verdict at all, only an elaborator error at the
tactic's position. This combinator restores the handler for the sub-budget case;
every caller must still re-throw when the ENCLOSING budget is the one that ran
out (`ambientBudgetExhausted`). Interrupts are never caught. -/
private def tryCatchRuntimeEx (x : TacticM α) (handler : Exception → TacticM α) :
    TacticM α :=
  controlAt CoreM fun runInCore =>
    Core.tryCatchRuntimeEx (runInCore x) fun error => runInCore (handler error)

/-- True when the enclosing declaration's own heartbeat budget is spent, in which
case a sub-budget handler must let the exception through: continuing would run
the rest of the ladder against a budget that is already gone. -/
private def ambientBudgetExhausted : CoreM Bool := do
  let ctx ← read
  if ctx.maxHeartbeats == 0 then
    return false
  return (← IO.getNumHeartbeats) - ctx.initHeartbeats > ctx.maxHeartbeats

/-- The two cheap rungs run under ONE budget SHARED by both, because what the guard
pays on a leaf it still refuses is their SUM: per-rung budgets of B bound that sum
at 2B, a shared budget bounds it at B.

Sized from the phase-2 census -- all 320 locals-refused leaves of cetus + scallop,
237 of which do not close. With a per-rung budget and `assumption` first, that
pair cost p50 148 ms but p90 3,269 ms and up to 5,745 ms, over the 2 s the
guard's own failure path is held to. Sharing the budget and running `rfl` first
removes most of that tail on its own; this constant removes the rest, and turns
"p90 under 1,500 ms" into "never more than about 1,500 ms".

The cap ships in HEARTBEATS, not milliseconds: a wall-clock cap would make a
proof's success depend on machine load, and a replay that passes on one box and
fails on another is not a proof.

In fleet-telemetry units 5,000 option-scale is 5,000,000 heartbeats. Measured
over the fleet's locals-refused leaves, a cheap rung burns 6,300 (p10) to 27,000
(p90) heartbeats per millisecond depending on how allocation-heavy the goal is, so
this cap is worth roughly 0.8 s on a quiet box and 1.6 s on one loaded like the
census run that measured the unbounded tail. The closes it must not lose are far
cheaper than that: the 83 the census found consume p50 62k heartbeats -- 1.2% of
the budget -- and p90 1.5M, and only 5 of them want more than the whole cap.

Deliberately NOT scaled by the file budget, unlike every other sub-budget here.
The others bound work the caller ASKED for and should grow when the author grants
more; this one bounds work done on a leaf the guard is about to REFUSE, so its
cost is a tax on every wide leaf in the corpus and must not grow with anyone's
`set_option maxHeartbeats`. -/
private def cheapPrefilterBudget : Nat := 5000

/-- Rungs whose entire cost is one pass over the goal: `rfl` tests one defeq,
`assumption` scans the telescope for the target. `rfl` goes FIRST because it is
nearly free where `assumption` is not (census, on the leaves that do not close:
`rfl` p50 6 ms / p90 95 ms, `assumption` p50 134 ms / p90 3,031 ms). Under a
shared budget the order decides who pays the tail: with `assumption` first every
`rfl`-addressable leaf buys `assumption`'s failure before its own 6 ms close, and
the cap then takes those closes away. Measured on the census: of the 52
calibration cheap closes this filter can reproduce, 47 survive the budget below in
this order and 5 fewer survive it in the other. `decide` is deliberately
absent: its failure mode is a whnf blow-up, the shape this file's sub-budget work
exists to bound, and it bought 2 closes of 54 in the calibration. -/
private def cheapPrefilterTactics : TacticM (Array (String × Syntax.Tactic)) := do
  return #[("rfl", ← `(tactic| rfl)), ("assumption", ← `(tactic| assumption))]

/-- Runs the cheap rungs on a copy of the state and reports whether one closed the
goal. The state, the goal list and the message log are restored either way -- a
close here is a REPORT, not a proof: the ordinary ladder re-proves it a moment
later through the ordinary reporting path, so the replay, its trust class and its
pruned marker are produced by the same code as every other close.

Two handlers, and the difference between them is the whole bounding argument. The
INNER one bounds a RUNG: `Core.tryCatch` re-throws resource exceptions, so without
`tryCatchRuntimeEx` a rung that spent the shared budget would kill the enclosing
declaration instead of yielding to the next rung. The OUTER one catches the same
exception once the budget is gone for good and answers "not addressable" -- the
right answer for a leaf the guard was about to refuse anyway. Both re-throw when
the DECLARATION's own budget is what ran out; that is never this filter's to
swallow. -/
private def cheapPrefilterCloses : TacticM Bool := do
  let initialGoals ← getGoals
  let initialState ← show MetaM _ from saveState
  let initialMessages ← Core.getMessageLog
  let restore : TacticM Unit := do
    initialState.restore
    setGoals initialGoals
    Core.setMessageLog initialMessages
  tryCatchRuntimeEx
    (withHeartbeatBudget cheapPrefilterBudget do
      let mut closed := false
      for (_, tactic) in ← cheapPrefilterTactics do
        let ok ← tryCatchRuntimeEx
          (do
            withoutRecover <| evalTactic tactic
            return (← getGoals).isEmpty)
          (fun error => do
            if ← ambientBudgetExhausted then throw error
            return false)
        restore
        if ok then
          closed := true
          break
      return closed)
    (fun error => do
      restore
      if ← ambientBudgetExhausted then throw error
      return false)

private def checkLeafSuitability : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let targetSize := exprSize target
  let lctx ← getLCtx
  let mut localCount : Nat := 0
  let mut totalSize := targetSize
  let mut hasState := containsStateType target
  let env ← getEnv
  for decl in lctx do
    localCount := localCount + 1
    totalSize := totalSize + exprSize decl.type
    hasState := hasState || containsStateType decl.type
    if let some value := decl.value? then
      totalSize := totalSize + exprSize value
      hasState := hasState || containsStateType value
  -- Size policies are decided from the goal alone and cost nothing, so they run
  -- FIRST. The dependency scan below reads the environment's constant closure,
  -- which is the only expensive part of this check; running it after the cheap
  -- gates means an oversized leaf never pays for it, and -- more importantly --
  -- the refusal an author sees names the property that actually disqualified
  -- the leaf. Under the previous order an exhausted scan threw before any size
  -- policy was evaluated, so on a whole corpus the size policies never once
  -- fired and their limits were, in effect, untested.
  if localCount > 48 then
    -- The width policy withholds the LADDER, not the two rungs whose whole cost is
    -- one bounded pass over the goal. A leaf whose goal is already a hypothesis, or
    -- already closed by a single defeq, is one such pass from a kernel-checked proof
    -- at any width, and refusing it buys nothing. Only a CLOSE gets through: the
    -- refusal -- including the size policies below, which a trivially closable leaf
    -- no longer needs protecting from -- stands for everything else.
    if ← cheapPrefilterCloses then
      return
    throwError
      "move_auto refused a telescope with {localCount} locals (limit: 48). Select premises or \
       use a pinned solver; use move_auto! only for an intentional bounded override"
  if targetSize > 2500 || totalSize > 12000 then
    throwError
      "move_auto refused an oversized leaf (target nodes: {targetSize}, context nodes: \
       {totalSize}; limits: 2500/12000). Write a structural proof or summary first"
  if hasState && (targetSize > 600 || totalSize > 4000) then
    throwError
      "move_auto refused a large World/Mutation leaf (target nodes: {targetSize}, context \
       nodes: {totalSize}; state limits: 600/4000). Use a frame/effect summary or pinned solver"
  -- One search state for the whole scan: the target and every local's type and
  -- value share `visited` and the ceiling, so a constant reachable from many
  -- hypotheses is expanded once instead of once per hypothesis.
  let mut scan := scanPartialFixpoint env target
  for decl in lctx do
    scan := scanPartialFixpoint env decl.type scan
    if let some value := decl.value? then
      scan := scanPartialFixpoint env value scan
  -- Only a FINDING refuses. An inconclusive scan is not evidence of a loop, and
  -- reporting it as one was the single largest source of false refusals on the
  -- corpus; the ceiling below is the pathological-term valve and is reported as
  -- its own class so the two can never be confused again.
  -- A fixpoint FINDING no longer refuses: discovery seals the carriers out of
  -- the unfold channel (they stay uninterpreted atoms; every rung is
  -- heartbeat-bounded) and injects harvested summaries about them as facts.
  -- The structured log line is the per-carrier telemetry the campaign needs.
  if scan.found then
    -- Sealed goals attempt like any other: the ablation traced the apparent
    -- "defeq bombs" on sealed leaves to unbudgeted discovery failure (inert
    -- tactic-position maxHeartbeats), which withHeartbeatBudget now bounds.
    let carriers :=
      if scan.carriers.isEmpty then #[partialFixpointCombinator]
      else scan.carriers
    let payload := Json.mkObj [
      ("version", .str "1"),
      ("carriers", .arr (carriers.map (Json.str ·.toString)))
    ]
    logInfo m!"MOVE_AUTO_FIXPOINT_V1 {payload.compress}"
  if scan.exhausted then
    throwError
      "move_auto refused a goal whose partial_fixpoint dependency scan hit its hard traversal \
       ceiling of {partialFixpointConstantCeiling} constants without deciding. This is a \
       pathological dependency closure, not a loop finding. Use a pinned solver"

private structure MoveCandidate where
  label : String
  invocation : Syntax
  tactic : Syntax
  smtTrusted : Bool := false
  trustPendingAudit : Bool := false

-- The four checked invocation builders take the rung to pin, so every candidate
-- reports the exact ladder entry it ran instead of the whole solver ladder.
private def checkedCandidates
    (norm normAll normZeta : Syntax.Tactic)
    (aesopTactic grindTactic : Syntax.Tactic)
    (simpInvocation omegaInvocation aesopInvocation grindInvocation :
      Ident → TacticM Syntax.Tactic)
    (trustPendingAudit : Bool := false) :
    TacticM (Array MoveCandidate) := do
  let arithRung := mkIdent `arith
  let targetRung := mkIdent `target
  let allRung := mkIdent `all
  let zetaRung := mkIdent `zeta
  let candidates : Array MoveCandidate := #[
    {
      label := "rfl"
      invocation := ← `(tactic| rfl)
      tactic := ← `(tactic| set_option maxHeartbeats 20000 in rfl)
    },
    {
      label := "assumption"
      invocation := ← `(tactic| assumption)
      tactic := ← `(tactic| set_option maxHeartbeats 20000 in assumption)
    },
    {
      label := "decide"
      invocation := ← `(tactic| decide)
      tactic := ← `(tactic| set_option maxHeartbeats 20000 in decide)
    },
    {
      label := "simp / target"
      invocation := ← simpInvocation targetRung
      tactic := ← `(tactic|
        set_option maxHeartbeats 50000 in ($norm:tactic; done))
    },
    {
      label := "omega / checked arithmetic"
      invocation := ← omegaInvocation arithRung
      tactic := ← `(tactic| set_option maxHeartbeats 100000 in move_checked_arith)
    },
    {
      label := "omega / target normalization"
      invocation := ← omegaInvocation targetRung
      tactic := ← `(tactic|
        set_option maxHeartbeats 100000 in
          ((try $norm:tactic); move_bn_props; omega))
    },
    {
      label := "Aesop / target normalization"
      invocation := ← aesopInvocation targetRung
      tactic := ← `(tactic|
        set_option maxHeartbeats 150000 in
          ((try $norm:tactic); $aesopTactic:tactic))
    },
    {
      label := "grind / target normalization"
      invocation := ← grindInvocation targetRung
      tactic := ← `(tactic|
        set_option maxHeartbeats 150000 in
          ((try $norm:tactic); $grindTactic:tactic))
    },
    {
      label := "simp / all hypotheses"
      invocation := ← simpInvocation allRung
      tactic := ← `(tactic|
        set_option maxHeartbeats 100000 in ($normAll:tactic; done))
    },
    {
      label := "omega / all hypotheses"
      invocation := ← omegaInvocation allRung
      tactic := ← `(tactic|
        set_option maxHeartbeats 150000 in
          ((try $normAll:tactic); move_bn_props; omega))
    },
    {
      label := "Aesop / all hypotheses"
      invocation := ← aesopInvocation allRung
      tactic := ← `(tactic|
        set_option maxHeartbeats 200000 in
          ((try $normAll:tactic); $aesopTactic:tactic))
    },
    {
      label := "grind / all hypotheses"
      invocation := ← grindInvocation allRung
      tactic := ← `(tactic|
        set_option maxHeartbeats 200000 in
          ((try $normAll:tactic); $grindTactic:tactic))
    },
    {
      label := "simp / zeta normalization"
      invocation := ← simpInvocation zetaRung
      tactic := ← `(tactic|
        set_option maxHeartbeats 150000 in ($normZeta:tactic; done))
    },
    {
      label := "omega / zeta normalization"
      invocation := ← omegaInvocation zetaRung
      tactic := ← `(tactic|
        set_option maxHeartbeats 200000 in
          ((try $normZeta:tactic); move_bn_props; omega))
    },
    {
      label := "Aesop / zeta normalization"
      invocation := ← aesopInvocation zetaRung
      tactic := ← `(tactic|
        set_option maxHeartbeats 250000 in
          ((try $normZeta:tactic); $aesopTactic:tactic))
    },
    {
      label := "grind / zeta normalization"
      invocation := ← grindInvocation zetaRung
      tactic := ← `(tactic|
        set_option maxHeartbeats 250000 in
          ((try $normZeta:tactic); $grindTactic:tactic))
    },
    {
      -- Numeral power bounds (campaign rung, 07-30). omega treats `b ^ x` as an
      -- opaque atom, grind does not decide exponentiation and the Z3 lane is
      -- nonlinear-blind, so `10 ^ n < 2 ^ 64` from `n ≤ 19` was unreachable for
      -- the whole ladder and the corpus paid for it in `native_decide` oracles.
      -- This rung supplies the one monotone step (`Nat.pow_le_pow_right` /
      -- `Nat.pow_le_pow_left` at literal bounds) and leaves the linear residue
      -- to omega. It is deliberately LAST: the guard rejects a non-power goal
      -- in microseconds, so the position costs nothing, and any leaf whose
      -- replay cites `move_pow_bound` is provably one no earlier rung could
      -- close.
      label := "numeral pow bound"
      invocation := ← `(tactic| move_pow_bound)
      tactic := ← `(tactic| move_pow_bound)
    }
  ]
  return candidates.map fun candidate => { candidate with trustPendingAudit }

private structure CandidateOutcome where
  winner : Option MoveCandidate := none
  failures : Array MessageData := #[]

private def residualClass (constants : Array Name) : String :=
  if constants.any fun name =>
      name.toString.startsWith "Prover.Mutation." ||
        name.toString.startsWith "Prover.World." then
    "state/effect"
  else if constants.any fun name =>
      let name := name.toString
      name.startsWith "Option." ||
        name.startsWith "List.find" ||
        name == "ite" || name == "dite" ||
        name.startsWith "Bool." then
    "structural/guard"
  else if constants.any fun name =>
      let name := name.toString
      name.startsWith "BoundedNat." ||
        name.startsWith "Nat." ||
        name.startsWith "Int." then
    "arithmetic"
  else
    "logical/opaque"

private def residualDiagnostics : TacticM MessageData := do
  let goals ← getGoals
  let env ← getEnv
  let mut diagnostics := #[]
  let mut index : Nat := 0
  for goal in goals.take 3 do
    let diagnostic ← goal.withContext do
      let target ← goal.getType
      let allConstants := collectConsts target
      let signalConstants := allConstants.filter (isDiscoverySignal env)
      let selectedConstants :=
        if signalConstants.isEmpty then allConstants else signalConstants
      let sortedConstants :=
        selectedConstants.qsort fun left right =>
          left.toString < right.toString
      let constants := sortedConstants.toList.take 8
      let goalNumber := index + 1
      pure m!"goal {goalNumber}: class={residualClass allConstants}; constants={constants}"
    diagnostics := diagnostics.push diagnostic
    index := index + 1
  if goals.length > 3 then
    diagnostics := diagnostics.push m!"... and {goals.length - 3} further goal(s)"
  return MessageData.joinSep diagnostics.toList "\n"

/-- True when the goal this discovery is about to search was one
`pruneContextToGoalDeps` was allowed to narrow, i.e. exactly when a replay has a
discovery context to reproduce. A goal with no free variable prunes to itself
(see `pruneContextToGoalDeps`), so marking its replay would claim an environment
that does not exist; every other goal was searched behind
`move_auto_leaf_guard`, which prunes before the ladder runs.

Read at the TOP of a discovery entry point, while the goal still exists — by the
time a winner is reported the goal is closed. -/
private def discoveryWasPruned : TacticM Bool := do
  let goal ← getMainGoal
  goal.withContext do
    return (← goal.getType).hasFVar

/-- A `private` declaration lives in the environment under a MANGLED internal
name -- `_private.<module>.0.<declared name>` -- and that is the name discovery
hands to `mkIdent` when it assembles a winning invocation. Printed verbatim the
replay is unadoptable twice over: `_private` is not a legal identifier prefix in
source, and the module component names the file DISCOVERY ran in (`_stdin` for a
generated probe), not the file the replay is pasted into. Measured on the cetus
sweep: 18 confirmed-close leaves were held out for exactly this.

The source-referenceable spelling is the declared name. Inside its own module a
private constant is reachable by precisely the name it was declared with,
namespaces included -- `resolvePrivateName` re-mangles it during resolution --
so stripping the private prefix yields what a human would write in that file.

Stripping is CONDITIONAL: the stripped name is used only when it resolves, in
the scope this replay text will be pasted into, back to the very constant it
replaced. Lean already refuses to let a second declaration take a private one's
declared name inside the same module ("a private declaration `X` has already
been declared"), so the ordinary collision cannot arise; the check is there for
the ones that can -- an alias or namespace prefix that resolves first, or a
private constant belonging to some OTHER module, which no spelling can reach.
Those keep the mangled name: visibly non-portable, and held out, which is
strictly better than a name that silently denotes something else. -/
private def portableConstantName (name : Name) : TacticM Name := do
  let some userName := privateToUserName? name | return name
  let resolutions ← Lean.resolveGlobalName userName (enableLog := false)
  match resolutions.filter (·.2.isEmpty) with
  | [(resolved, _)] => return if resolved == name then userName else name
  | _ => return name

/-- Emission-only rewrite: every identifier in the invocation that names a
private constant is respelled source-referenceably before the tree is printed.
The tree that RAN is untouched -- discovery, minimization and replay execution
all keep the resolved private name. -/
private partial def withPortableConstantNames (stx : Syntax) : TacticM Syntax := do
  match stx with
  | .ident info _ val _ =>
    let portable ← portableConstantName val
    if portable == val then
      return stx
    return (mkIdent portable).raw.setInfo info
  | .node info kind args =>
    return .node info kind (← args.mapM withPortableConstantNames)
  | _ => return stx

private def renderDurableInvocation
    (candidate : MoveCandidate) (pruned : Bool) : TacticM String := do
  let tactic : Syntax.Tactic := ⟨← withPortableConstantNames candidate.invocation⟩
  let tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $tactic:tactic)
  let invocation ← PrettyPrinter.ppCategory ``Lean.Parser.Tactic.tacticSeq tacticSeq
  let width :=
    if candidate.label.startsWith "structural/" then 240
    else Std.Format.defWidth
  let invocation := invocation.pretty (width := width) (indent := 0) (column := 0)
  let invocation := invocation
    |>.replace "move_auto(" "move_auto ("
    |>.replace "solver:=" "solver := "
    |>.replace "rung:=" "rung := "
    |>.replace "profile:=" "profile := "
    |>.replace "budget:=" "budget := "
    |>.replace ")(" ") ("
    |>.replace ")only[" ") only ["
    |>.replace "\n    cases[" " cases ["
    |>.replace "\n    guards[" " guards ["
    |>.replace "cases[" "cases ["
    |>.replace "guards[" "guards ["
    |>.replace "]using(" "] using ("
    |>.replace "using(" "using ("
    |>.replace "]facts[" "] facts ["
    |>.replace "]unfold[" "] unfold ["
    |>.replace "]rules[" "] rules ["
    |>.replace "]effects[" "] effects ["
    |>.replace "]defeq[" "] defeq ["
  -- The marker is prefixed as TEXT, not folded into the tree before printing,
  -- so it cannot consume the inner invocation's line budget: a marked replay
  -- wraps at exactly the columns the same replay wrapped at before, and the
  -- only textual difference is this prefix. `move_auto_pruned` re-parses the
  -- result as one tactic (pinned in lake_compile_smoke).
  return if pruned then "move_auto_pruned " ++ invocation else invocation

private def reportDurableProof (pruned : Bool) (candidate : MoveCandidate) :
    TacticM Unit := do
  let invocation ← renderDurableInvocation candidate pruned
  if candidate.smtTrusted then
    logInfo m!"[smt_trusted] Try this durable proof: {invocation}"
  else if candidate.trustPendingAudit then
    logInfo m!"[trust_pending_audit] Try this durable proof: {invocation}"
  else
    logInfo m!"Try this durable proof: {invocation}"

private def reportProbeResult
    (candidateId token : String) (pruned : Bool) (candidate : MoveCandidate) :
    TacticM Unit := do
  let invocation ← renderDurableInvocation candidate pruned
  let trust :=
    if candidate.smtTrusted then "smt_trusted"
    else if candidate.trustPendingAudit then "trust_pending_audit"
    else "checked"
  let payload := Json.mkObj [
    ("version", .str "1"),
    ("candidate_id", .str candidateId),
    ("token", .str token),
    ("trust", .str trust),
    ("replay", .str invocation)
  ]
  logInfo m!"MOVE_AUTO_PROBE_V1 {payload.compress}"

private def throwLadderExhausted (failures : Array MessageData) : TacticM Unit := do
  let residual ← residualDiagnostics
  throwError
    "move_auto exhausted its checked leaf ladder. Per-rung diagnostics:\
     {indentD (MessageData.joinSep failures.toList "\n")}\
     \nResidual goal fingerprint:{indentD residual}\
     \nUse move_auto? to test and emit an explicit SMT-trusted fallback, or write a summary"

/-- `try x catch _ => fallback` for the BEST-EFFORT probes this file is full of
(a normalization run purely to look at its residue, a `whnf` used to classify a
subterm, an instance synthesis used as a decidability test). Written with a plain
`try`, every one of them was a leaf-killer: the probe is allowed to fail, but the
resource exception it fails with is re-thrown by `Core.tryCatch` and takes the
whole tactic with it. Same rule as everywhere else here -- a limit that fired
inside the probe is the probe's failure; a limit that exhausted the DECLARATION's
budget is the end of the tactic and is passed through. -/
private def tryBestEffort (x : TacticM α) (fallback : TacticM α) : TacticM α :=
  tryCatchRuntimeEx x fun error => do
    if ← ambientBudgetExhausted then
      throw error
    fallback

/-- Every resource limit that fires INSIDE move_auto's own search is move_auto's
failure to REPORT, not the caller's to survive: re-thrown as an ordinary error it
can be handled like any other move_auto failure, by `first`/`try`/`<|>` or by a
harness around the tactic. Thrown as the runtime exception it arrives as, it
passes through every handler in the language and kills the enclosing declaration
-- which is how a leaf could produce no verdict at all rather than a failing one.
A limit that exhausted the DECLARATION's budget is passed through untouched. -/
private def withCatchableResourceFailure (x : TacticM Unit) : TacticM Unit :=
  tryCatchRuntimeEx x fun error => do
    if (← ambientBudgetExhausted) || !error.isRuntime then
      throw error
    throwError "move_auto hit a resource limit inside its own search: \
      {error.toMessageData}"

/-- A sub-budget is a FRACTION of what the caller granted, never a constant.
A hard-coded ceiling is one a leaf cannot buy its way out of: raising the file's
`maxHeartbeats` moved the declaration's budget and left every rung pinned at the
same 250k, so the sub-budget -- not the policy the author set -- decided what was
provable. Measured on the locals calibration: 58 of 193 laddered leaves (30%)
died on a 250k sub-budget under a 4M file budget. `base` is the floor, so the
default 200k file budget keeps exactly the ceilings this file shipped with, and
`share` is the fraction of a raised budget one sub-computation may take. -/
private def scaledHeartbeatBudget (base share : Nat) : CoreM Nat := do
  let ctx ← read
  if ctx.maxHeartbeats == 0 then
    return base
  return max base (ctx.maxHeartbeats / 1000 / share)

/-- Per-candidate ceiling: generous against the largest intended rung budget
(200k) at the default file budget; Z3 candidates get more head-room for the
Lean-side translation. Under a RAISED file budget it scales with it, so a rung
that needs more can be given more -- the eighth is what keeps a failing rung from
eating the declaration a later rung still has to close in.

The shares COMPOSE, which is the point of a sub-budget and worth stating: on the
discovery path the whole search already runs inside `discoveryHeartbeatBudget`
(half the file budget), so a rung sees an eighth of THAT -- a sixteenth of the
file budget, floored at 250k. A 4M probe file therefore lands a rung on exactly
the 250k this file has always used, 16M gives it 1M, and the direct
`move_auto_core` path (no discovery wrapper) gives it an eighth throughout. -/
private def candidateHeartbeatBudget (candidate : MoveCandidate) : CoreM Nat :=
  scaledHeartbeatBudget (if candidate.smtTrusted then 1000000 else 250000) 8

/-- Whole-discovery ceiling: bounds the FAILURE path of `move_auto?` /
`move_auto_probe`, which previously ran to the declaration's limit. -/
private def discoveryHeartbeatBudget : CoreM Nat :=
  scaledHeartbeatBudget 1500000 2

-- Runs each candidate at most once and records one diagnostic per failing rung.
-- `keepWinner` decides what a caller gets back: an execution (`true`) leaves the
-- winning tactic state and its messages in place, a probe (`false`) restores both
-- so the caller can keep searching. Either way an exhausted ladder restores the
-- entry state and returns the collected diagnostics instead of re-running
-- anything to regenerate them.
private def searchCandidates
    (candidates : Array MoveCandidate) (keepWinner : Bool) :
    TacticM CandidateOutcome := do
  checkMoveAutoBase
  let initialGoals ← getGoals
  let initialState ← show MetaM _ from saveState
  let initialMessages ← Core.getMessageLog
  let mut failures : Array MessageData := #[]
  for candidate in candidates do
    initialState.restore
    setGoals initialGoals
    Core.setMessageLog initialMessages
    let failure : Option MessageData ← tryCatchRuntimeEx
      (do
        withHeartbeatBudget (← candidateHeartbeatBudget candidate) <|
          withoutRecover <| evalTactic candidate.tactic
        pruneSolvedGoals
        let remaining ← getGoals
        if remaining.isEmpty then
          -- A candidate that closed the goal but LOGGED an error (recoverable
          -- elaboration failures do not throw) is poisoned: keeping it as the
          -- winner would keep its error in the message log and fail the whole
          -- module long after this tactic reported success.
          let currentMessages ← Core.getMessageLog
          if currentMessages.hasErrors && !initialMessages.hasErrors then
            pure (some m!"[failed] {candidate.label}: closed but logged errors")
          else
            pure none
        else
          pure (some m!"[failed] {candidate.label}: left {remaining.length} goal(s)"))
      (fun error => do
        -- A rung that spent ITS budget is a failing rung; a rung that spent the
        -- DECLARATION's is the end of the search, and swallowing that would run
        -- every remaining rung against a budget that is already gone.
        if ← ambientBudgetExhausted then
          throw error
        pure (some m!"[failed] {candidate.label}: {error.toMessageData}"))
    match failure with
    | none =>
      unless keepWinner do
        Core.setMessageLog initialMessages
        initialState.restore
        setGoals initialGoals
      return { winner := some candidate, failures }
    | some diagnostic => failures := failures.push diagnostic
  Core.setMessageLog initialMessages
  initialState.restore
  setGoals initialGoals
  return { failures }

private def runCandidates (candidates : Array MoveCandidate) (discovery : Bool) :
    TacticM Unit := do
  let pruned ← if discovery then discoveryWasPruned else pure false
  let outcome ← searchCandidates candidates true
  match outcome.winner with
  | some candidate => if discovery then reportDurableProof pruned candidate
  | none => throwLadderExhausted outcome.failures

private def appendZ3Candidate
    (candidates : Array MoveCandidate) (label : String)
    (profileId budgetId : Ident)
    (hints : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (factIds unfoldIds defeqIds : Array Ident) :
    TacticM (Array MoveCandidate) := do
  let invocation ← `(tactic|
    move_auto
      (solver := z3)
      (profile := $profileId)
      (budget := $budgetId)
      only [$[$hints:simpLemma],*]
      facts [$[$factIds:ident],*]
      unfold [$[$unfoldIds:ident],*]
      defeq [$[$defeqIds:ident],*])
  let tactic ← `(tactic|
    set_option maxHeartbeats 1000000 in
    move_auto_z3_unguarded
      (profile := $profileId)
      (budget := $budgetId)
      only [$[$hints:simpLemma],*]
      facts [$[$factIds:ident],*]
      unfold [$[$unfoldIds:ident],*]
      defeq [$[$defeqIds:ident],*])
  return candidates.push {
    label
    invocation
    tactic
    smtTrusted := true
  }

private def appendZ3Portfolio
    (candidates : Array MoveCandidate)
    (hints : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (factIds unfoldIds defeqIds : Array Ident) :
    TacticM (Array MoveCandidate) := do
  let targetProfile := mkIdent `target
  let allProfile := mkIdent `all
  let zetaProfile := mkIdent `zeta
  let quickBudget := mkIdent `quick
  let deepBudget := mkIdent `deep
  let candidates ← appendZ3Candidate candidates "Z3 / target / quick"
    targetProfile quickBudget hints factIds unfoldIds defeqIds
  let candidates ← appendZ3Candidate candidates "Z3 / all / quick"
    allProfile quickBudget hints factIds unfoldIds defeqIds
  let candidates ← appendZ3Candidate candidates "Z3 / zeta / quick"
    zetaProfile quickBudget hints factIds unfoldIds defeqIds
  let candidates ← appendZ3Candidate candidates "Z3 / target / deep"
    targetProfile deepBudget hints factIds unfoldIds defeqIds
  let candidates ← appendZ3Candidate candidates "Z3 / all / deep"
    allProfile deepBudget hints factIds unfoldIds defeqIds
  appendZ3Candidate candidates "Z3 / zeta / deep"
    zetaProfile deepBudget hints factIds unfoldIds defeqIds

private def checkedCandidatesForOnly
    (hints : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :
    TacticM (Array MoveCandidate) := do
  checkedCandidates
    (← `(tactic| move_norm_unguarded only [$[$hints:simpLemma],*]))
    (← `(tactic| move_norm_all_unguarded only [$[$hints:simpLemma],*]))
    (← `(tactic| move_norm_all_zeta_unguarded only [$[$hints:simpLemma],*]))
    (← `(tactic| move_aesop))
    (← `(tactic| grind only))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := simp) (rung := $pinnedRung) only [$[$hints:simpLemma],*]))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := omega) (rung := $pinnedRung) only [$[$hints:simpLemma],*]))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := aesop) (rung := $pinnedRung) only [$[$hints:simpLemma],*]))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := grind) (rung := $pinnedRung) only [$[$hints:simpLemma],*]))
    (!hints.isEmpty)

private def checkedCandidatesForChannels
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (unfoldIds ruleIds effectIds : Array Ident) :
    TacticM (Array MoveCandidate) := do
  let grindRules ← ruleIds.mapM fun id =>
    `(Lean.Parser.Tactic.grindParam| $id:ident)
  let grindTactic ←
    if grindRules.isEmpty then
      `(tactic| grind only)
    else
      `(tactic| grind only [$grindRules,*])
  let candidates ← checkedCandidates
    (← `(tactic|
      move_norm_channels only [$[$rewrites:simpLemma],*]
        unfold [$[$unfoldIds:ident],*] effects [$[$effectIds:ident],*]))
    (← `(tactic|
      move_norm_all_channels only [$[$rewrites:simpLemma],*]
        unfold [$[$unfoldIds:ident],*] effects [$[$effectIds:ident],*]))
    (← `(tactic|
      move_norm_all_zeta_channels only [$[$rewrites:simpLemma],*]
        unfold [$[$unfoldIds:ident],*] effects [$[$effectIds:ident],*]))
    (← `(tactic| move_aesop_rules [$[$ruleIds:ident],*]))
    grindTactic
    (fun pinnedRung =>
      `(tactic|
        move_auto (solver := simp) (rung := $pinnedRung)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*]
          rules [$[$ruleIds:ident],*]
          effects [$[$effectIds:ident],*]))
    (fun pinnedRung =>
      `(tactic|
        move_auto (solver := omega) (rung := $pinnedRung)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*]
          rules [$[$ruleIds:ident],*]
          effects [$[$effectIds:ident],*]))
    (fun pinnedRung =>
      `(tactic|
        move_auto (solver := aesop) (rung := $pinnedRung)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*]
          rules [$[$ruleIds:ident],*]
          effects [$[$effectIds:ident],*]))
    (fun pinnedRung =>
      `(tactic|
        move_auto (solver := grind) (rung := $pinnedRung)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*]
          rules [$[$ruleIds:ident],*]
          effects [$[$effectIds:ident],*]))
    (!rewrites.isEmpty || !unfoldIds.isEmpty ||
      !ruleIds.isEmpty || !effectIds.isEmpty)
  let hasChannels :=
    !rewrites.isEmpty || !unfoldIds.isEmpty ||
      !ruleIds.isEmpty || !effectIds.isEmpty
  return candidates.filter fun candidate =>
    (!hasChannels || candidate.label != "omega / checked arithmetic") &&
      (ruleIds.isEmpty ||
        candidate.label == "rfl" ||
        candidate.label == "assumption" ||
        candidate.label == "decide" ||
        candidate.label.startsWith "Aesop" ||
        candidate.label.startsWith "grind")

private def z3CandidatesForOnly
    (hints : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :
    TacticM (Array MoveCandidate) :=
  appendZ3Portfolio #[] hints #[] #[] #[]

private def candidateWithLabel
    (candidates : Array MoveCandidate) (label : String) : TacticM MoveCandidate := do
  for candidate in candidates do
    if candidate.label == label then
      return candidate
  throwError "move_auto could not rebuild the winning candidate '{label}'"

private def minimizeHints
    (hints : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (winner : MoveCandidate)
    (buildCandidates :
      Array (TSyntax ``Lean.Parser.Tactic.simpLemma) →
        TacticM (Array MoveCandidate)) :
    TacticM MoveCandidate := do
  let mut kept := hints
  let mut keptWinner := winner
  let mut index := 0
  while index < kept.size do
    let trial := kept.eraseIdxIfInBounds index
    let trialCandidate ←
      candidateWithLabel (← buildCandidates trial) winner.label
    match (← searchCandidates #[trialCandidate] false).winner with
    | some successful =>
      kept := trial
      keptWinner := successful
    | none =>
      index := index + 1
  return keptWinner

private def checkedCandidatesForUnfoldEffects
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (unfoldIds : Array Ident)
    (effectIds : Array Ident) : TacticM (Array MoveCandidate) :=
  checkedCandidatesForChannels rewrites unfoldIds #[] effectIds

private def z3CandidatesForUnfoldEffects
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (unfoldIds : Array Ident)
    (effectIds : Array Ident) : TacticM (Array MoveCandidate) := do
  let effectHints ← effectIds.mapM fun id =>
    `(Lean.Parser.Tactic.simpLemma| $id:ident)
  let unfoldHints ← unfoldIds.mapM fun id =>
    `(Lean.Parser.Tactic.simpLemma| $id:ident)
  appendZ3Portfolio #[] (rewrites ++ unfoldHints ++ effectHints)
    effectIds unfoldIds #[]

private def minimizeUnfoldEffects
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (unfoldIds : Array Ident)
    (effectIds : Array Ident)
    (winner : MoveCandidate)
    (buildCandidates :
      Array (TSyntax ``Lean.Parser.Tactic.simpLemma) →
        Array Ident → Array Ident → TacticM (Array MoveCandidate)) :
    TacticM MoveCandidate := do
  let mut keptRewrites := rewrites
  let mut keptUnfolds := unfoldIds
  let mut keptWinner := winner
  let mut index := 0
  while index < keptUnfolds.size do
    let trial := keptUnfolds.eraseIdxIfInBounds index
    let trialCandidate ←
      candidateWithLabel
        (← buildCandidates keptRewrites trial effectIds) winner.label
    match (← searchCandidates #[trialCandidate] false).winner with
    | some successful =>
      keptUnfolds := trial
      keptWinner := successful
    | none =>
      index := index + 1
  let mut keptEffects := effectIds
  index := 0
  while index < keptEffects.size do
    let trial := keptEffects.eraseIdxIfInBounds index
    let trialCandidate ←
      candidateWithLabel
        (← buildCandidates keptRewrites keptUnfolds trial) winner.label
    match (← searchCandidates #[trialCandidate] false).winner with
    | some successful =>
      keptEffects := trial
      keptWinner := successful
    | none =>
      index := index + 1
  index := 0
  while index < keptRewrites.size do
    let trial := keptRewrites.eraseIdxIfInBounds index
    let trialCandidate ←
      candidateWithLabel
        (← buildCandidates trial keptUnfolds keptEffects) winner.label
    match (← searchCandidates #[trialCandidate] false).winner with
    | some successful =>
      keptRewrites := trial
      keptWinner := successful
    | none =>
      index := index + 1
  return keptWinner

private def checkedCandidatesForRewriteEffects
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (effectIds : Array Ident) : TacticM (Array MoveCandidate) :=
  checkedCandidatesForUnfoldEffects rewrites #[] effectIds

private def z3CandidatesForRewriteEffects
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (effectIds : Array Ident) : TacticM (Array MoveCandidate) :=
  z3CandidatesForUnfoldEffects rewrites #[] effectIds

private def minimizeRewriteEffects
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (effectIds : Array Ident)
    (winner : MoveCandidate)
    (buildCandidates :
      Array (TSyntax ``Lean.Parser.Tactic.simpLemma) →
        Array Ident → TacticM (Array MoveCandidate)) :
    TacticM MoveCandidate :=
  minimizeUnfoldEffects rewrites #[] effectIds winner fun rewriteSet _ effectSet =>
    buildCandidates rewriteSet effectSet

private partial def collectClosedSubterms
    (expression : Expr) (found : Array Expr := #[]) : Array Expr :=
  let found :=
    if expression.hasLooseBVars || expression.hasMVar ||
        found.any (Expr.equal expression) then
      found
    else
      found.push expression
  match expression with
  | .app function argument =>
      collectClosedSubterms argument (collectClosedSubterms function found)
  | .lam _ type body _ | .forallE _ type body _ =>
      collectClosedSubterms body (collectClosedSubterms type found)
  | .letE _ type value body _ =>
      collectClosedSubterms body
        (collectClosedSubterms value (collectClosedSubterms type found))
  | .mdata _ body | .proj _ _ body => collectClosedSubterms body found
  | _ => found

private def isSafeTwoConstructorCaseType
    (env : Environment) (type : Expr) : Bool :=
  match type.getAppFn with
  | .const inductiveName _ =>
    match env.find? inductiveName with
    | some (.inductInfo info) =>
      if info.ctors.length != 2 then
        false
      else
        let constructorNames := info.ctors.map (·.toString)
        let abortShape :=
          (constructorNames.any fun name =>
            name.endsWith ".NoAbort" || name.endsWith ".noAbort") &&
          (constructorNames.any fun name =>
            name.endsWith ".Aborted" || name.endsWith ".aborted")
        let finiteShape := info.ctors.all fun constructorName =>
          match env.find? constructorName with
          | some (.ctorInfo constructor) => constructor.numFields == 0
          | _ => false
        abortShape || finiteShape
    | _ => false
  | _ => false

private def isConstructorApplication (env : Environment) (expression : Expr) : Bool :=
  match expression.getAppFn with
  | .const name _ =>
    match env.find? name with
    | some (.ctorInfo _) => true
    | _ => false
  | _ => false

private def structuralResidualTargets
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (unfoldIds effectIds : Array Ident) : TacticM (Array Expr) := do
  let initialGoals ← getGoals
  let initialState ← show MetaM _ from saveState
  let initialMessages ← Core.getMessageLog
  tryBestEffort
    (withoutRecover <| evalTactic (← `(tactic|
      try move_norm_all_channels only [$[$rewrites:simpLemma],*]
        unfold [$[$unfoldIds:ident],*] effects [$[$effectIds:ident],*])))
    (pure ())
  pruneSolvedGoals
  let residualGoals ← getGoals
  let mut targets := #[]
  for goal in residualGoals.take 3 do
    targets := targets.push (← goal.withContext do instantiateMVars (← goal.getType))
  Core.setMessageLog initialMessages
  initialState.restore
  setGoals initialGoals
  if targets.isEmpty then
    let target ← withMainContext do
      instantiateMVars (← (← getMainGoal).getType)
    return #[target]
  return targets

private def structuralDiscriminants
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (unfoldIds effectIds : Array Ident) :
    TacticM (Array Term × Array Term) := withMainContext do
  let env ← getEnv
  let mut caseTerms := #[]
  let mut guardTerms := #[]
  for target in ← structuralResidualTargets rewrites unfoldIds effectIds do
    for expression in collectClosedSubterms target do
      if Expr.equal expression target then
        continue
      if isConstructorApplication env expression then
        continue
      let some type ←
          tryBestEffort (do return some (← whnf (← inferType expression))) (pure none)
        | continue
      let isCase :=
        type.isConstOf ``Bool ||
          type.getAppFn.isConstOf ``Option ||
          isSafeTwoConstructorCaseType env type
      if isCase && caseTerms.size < 4 then
        -- Ascribe the delaborated term with its type: the surface syntax can
        -- contain structure-instance notation (e.g. `{ code := 0 }` inside an
        -- AbortResult), which fails or postpones without an expected type when
        -- the plan tactic re-elaborates it — and postponed failures surface as
        -- spurious errors at declaration end, immune to message-log restores.
        let termStx ← PrettyPrinter.delab expression
        let typeStx ← PrettyPrinter.delab type
        caseTerms := caseTerms.push (← `(($termStx : $typeStx)))
      if type.isProp && guardTerms.size < 4 then
        let root := expression.getAppFn.constName?
        if root == some ``True || root == some ``False ||
            root == some ``And || root == some ``Or || root == some ``Iff ||
            root == some ``Not then
          continue
        let decidable ←
          tryBestEffort
            (do
              discard <| synthInstance (← mkAppM ``Decidable #[expression])
              pure true)
            (pure false)
        if decidable then
          let termStx ← PrettyPrinter.delab expression
          guardTerms := guardTerms.push (← `(($termStx : Prop)))
  return (caseTerms, guardTerms)

private inductive StructuralKind where
  | cases
  | guards

private def checkedSolverRung (candidate : MoveCandidate) : Option (Name × Name) :=
  let label := candidate.label
  let solverName :=
    if label.startsWith "simp /" then some `simp
    else if label.startsWith "omega /" then some `omega
    else if label.startsWith "Aesop /" then some `aesop
    else if label.startsWith "grind /" then some `grind
    else none
  let rungName :=
    if (label.splitOn "checked arithmetic").length > 1 then some `arith
    else if (label.splitOn "target").length > 1 then some `target
    else if (label.splitOn "all hypotheses").length > 1 then some `all
    else if (label.splitOn "zeta").length > 1 then some `zeta
    else none
  match solverName, rungName with
  | some solverName, some rungName => some (solverName, rungName)
  | _, _ => none

private def structuralCandidate
    (kind : StructuralKind) (terms : Array Term)
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (unfoldIds effectIds : Array Ident)
    (leaf : MoveCandidate) : TacticM MoveCandidate := do
  let some (solverName, rungName) := checkedSolverRung leaf
    | throwError "move_auto structural discovery received a non-checked leaf"
  if rungName == `arith then
    throwError "move_auto structural discovery does not use the arith-only rung"
  let solverId := mkIdent solverName
  let solverSyntax ← `(moveAutoCheckedSolver| $solverId:ident)
  let rungId := mkIdent rungName
  let mkName := fun index =>
    mkIdent <| Name.mkSimple <|
      if kind matches .cases then
        s!"h_move_auto_case_{index + 1}"
      else
        s!"h_move_auto_guard_{index + 1}"
  let invocation ← match kind, solverName, terms.toList with
    | .cases, `simp, [term] =>
      let name := mkName 0
      `(tactic|
        move_auto cases [$name:ident : $term:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .cases, `simp, [first, second] =>
      let firstName := mkName 0
      let secondName := mkName 1
      `(tactic|
        move_auto cases [$firstName:ident : $first:term, $secondName:ident : $second:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .cases, `omega, [term] =>
      let name := mkName 0
      `(tactic|
        move_auto cases [$name:ident : $term:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .cases, `omega, [first, second] =>
      let firstName := mkName 0
      let secondName := mkName 1
      `(tactic|
        move_auto cases [$firstName:ident : $first:term, $secondName:ident : $second:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .cases, `aesop, [term] =>
      let name := mkName 0
      `(tactic|
        move_auto cases [$name:ident : $term:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .cases, `aesop, [first, second] =>
      let firstName := mkName 0
      let secondName := mkName 1
      `(tactic|
        move_auto cases [$firstName:ident : $first:term, $secondName:ident : $second:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .cases, `grind, [term] =>
      let name := mkName 0
      `(tactic|
        move_auto cases [$name:ident : $term:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .cases, `grind, [first, second] =>
      let firstName := mkName 0
      let secondName := mkName 1
      `(tactic|
        move_auto cases [$firstName:ident : $first:term, $secondName:ident : $second:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .guards, `simp, [term] =>
      let name := mkName 0
      `(tactic|
        move_auto guards [$name:ident : $term:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .guards, `simp, [first, second] =>
      let firstName := mkName 0
      let secondName := mkName 1
      `(tactic|
        move_auto guards [$firstName:ident : $first:term, $secondName:ident : $second:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .guards, `omega, [term] =>
      let name := mkName 0
      `(tactic|
        move_auto guards [$name:ident : $term:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .guards, `omega, [first, second] =>
      let firstName := mkName 0
      let secondName := mkName 1
      `(tactic|
        move_auto guards [$firstName:ident : $first:term, $secondName:ident : $second:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .guards, `aesop, [term] =>
      let name := mkName 0
      `(tactic|
        move_auto guards [$name:ident : $term:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .guards, `aesop, [first, second] =>
      let firstName := mkName 0
      let secondName := mkName 1
      `(tactic|
        move_auto guards [$firstName:ident : $first:term, $secondName:ident : $second:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .guards, `grind, [term] =>
      let name := mkName 0
      `(tactic|
        move_auto guards [$name:ident : $term:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | .guards, `grind, [first, second] =>
      let firstName := mkName 0
      let secondName := mkName 1
      `(tactic|
        move_auto guards [$firstName:ident : $first:term, $secondName:ident : $second:term]
          using (solver := $solverSyntax:moveAutoCheckedSolver) (rung := $rungId)
          only [$[$rewrites:simpLemma],*]
          unfold [$[$unfoldIds:ident],*] rules [] effects [$[$effectIds:ident],*])
    | _, _, _ => throwError "move_auto structural discovery expected one or two splits"
  return {
    label :=
      s!"structural/{if kind matches .cases then "cases" else "guards"}/{leaf.label}"
    invocation
    tactic := invocation
    trustPendingAudit :=
      !rewrites.isEmpty || !unfoldIds.isEmpty || !effectIds.isEmpty
  }

private def structuralCandidates
    (kind : StructuralKind) (terms : Array Term)
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (unfoldIds effectIds : Array Ident) : TacticM (Array MoveCandidate) := do
  let leaves ← checkedCandidatesForUnfoldEffects rewrites unfoldIds effectIds
  let mut candidates := #[]
  for leaf in leaves do
    if let some (_, rungName) := checkedSolverRung leaf then
      if rungName != `arith then
        candidates := candidates.push
          (← structuralCandidate kind terms rewrites unfoldIds effectIds leaf)
  return candidates

private def tryStructuralPlan
    (kind : StructuralKind) (terms : Array Term)
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (unfoldIds effectIds : Array Ident)
    (report : MoveCandidate → TacticM Unit) : TacticM Bool := do
  let outcome ←
    searchCandidates
      (← structuralCandidates kind terms rewrites unfoldIds effectIds) false
  let some winner := outcome.winner | return false
  let minimized ←
    minimizeUnfoldEffects rewrites unfoldIds effectIds winner fun newRewrites newUnfolds newEffects =>
      structuralCandidates kind terms newRewrites newUnfolds newEffects
  runCandidates #[minimized] false
  report minimized
  return true

private def runStructuralDiscovery
    (rewrites : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (unfoldIds effectIds : Array Ident)
    (report : MoveCandidate → TacticM Unit) : TacticM Bool := do
  let (caseTerms, guardTerms) ←
    structuralDiscriminants rewrites unfoldIds effectIds
  for term in caseTerms do
    if ← tryStructuralPlan .cases #[term] rewrites unfoldIds effectIds report then
      return true
  for term in guardTerms do
    if ← tryStructuralPlan .guards #[term] rewrites unfoldIds effectIds report then
      return true
  for firstIndex in [:caseTerms.size] do
    for secondIndex in [firstIndex + 1:caseTerms.size] do
      let some first := caseTerms[firstIndex]? | continue
      let some second := caseTerms[secondIndex]? | continue
      if ←
          tryStructuralPlan
            .cases #[first, second] rewrites unfoldIds effectIds report then
        return true
  for firstIndex in [:guardTerms.size] do
    for secondIndex in [firstIndex + 1:guardTerms.size] do
      let some first := guardTerms[firstIndex]? | continue
      let some second := guardTerms[secondIndex]? | continue
      if ←
          tryStructuralPlan
            .guards #[first, second] rewrites unfoldIds effectIds report then
        return true
  return false

private def abortFromCandidates : TacticM (Array MoveCandidate) := withMainContext do
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let some (_, _, targetRhs) := target.eq? | return #[]
  let mut candidates := #[]
  for declaration in ← getLCtx do
    if candidates.size == 8 then
      break
    if declaration.isImplementationDetail || declaration.userName.isAnonymous then
      continue
    let some (_, _, hypothesisRhs) :=
        (← instantiateMVars declaration.type).eq? | continue
    let state ← saveState
    let rhsMatches ← isDefEq targetRhs hypothesisRhs
    state.restore
    if !rhsMatches then
      continue
    let hypothesis := mkIdent declaration.userName
    let invocation ← `(tactic| abort_from $hypothesis:ident)
    candidates := candidates.push {
      label := s!"abort_from/{declaration.userName}"
      invocation
      tactic := invocation
    }
  return candidates

private def runAbortFromDiscovery
    (report : MoveCandidate → TacticM Unit) : TacticM Bool := do
  let candidates ← abortFromCandidates
  if candidates.isEmpty then
    return false
  let outcome ← searchCandidates candidates false
  let some winner := outcome.winner | return false
  runCandidates #[winner] false
  report winner
  return true

/-- Loop helpers look like `f.while_N` / `f.after_N` (generated) — the names
summary harvesting keys on. -/
private def looksLikeLoopHelper (name : Name) : Bool :=
  let s := name.toString
  (s.splitOn ".while_").length > 1 || (s.splitOn ".after_").length > 1

initialize carrierFactIndex : IO.Ref (Option (NameMap (Array Name))) ←
  IO.mkRef none

/-- One pass over the environment: for every loop helper, the theorems whose
statement mentions it — these are the already-proven loop summaries
(invariant/step lemmas) the corpus carries. Built lazily once per module
elaboration; theorems declared later in the same file are not indexed (v1). -/
private def buildCarrierFactIndex (env : Environment) :
    NameMap (Array Name) :=
  env.constants.fold (init := {}) fun index name info => Id.run do
    let .thmInfo thm := info | return index
    if name.isInternal then
      return index
    let s := name.toString
    if (s.splitOn ".eq_").length > 1 || (s.splitOn ".match_").length > 1 then
      return index
    let mut index := index
    for used in thm.type.getUsedConstants do
      if looksLikeLoopHelper used && !used.isPrefixOf name then
        let entry := (index.find? used).getD #[]
        if entry.size < 8 && !entry.contains name then
          index := index.insert used (entry.push name)
    return index

private def collectFixpointCarriers : TacticM (Array Name) := withMainContext do
  let env ← getEnv
  let goal ← getMainGoal
  let mut scan := scanPartialFixpoint env (← goal.getType)
  for decl in ← getLCtx do
    scan := scanPartialFixpoint env decl.type scan
    if let some value := decl.value? then
      scan := scanPartialFixpoint env value scan
  return scan.carriers

private def harvestCarrierFacts (carriers : Array Name) :
    TacticM (Array Ident) := do
  if carriers.isEmpty then
    return #[]
  let env ← getEnv
  let index ← do
    match ← carrierFactIndex.get with
    | some index => pure index
    | none =>
      let built := buildCarrierFactIndex env
      carrierFactIndex.set (some built)
      pure built
  let mut facts : Array Name := #[]
  for carrier in carriers do
    for fact in (index.find? carrier).getD #[] do
      if facts.size < 8 && !facts.contains fact then
        facts := facts.push fact
  return facts.map mkIdent

private def runAutomaticDiscovery
    (report : MoveCandidate → TacticM Unit) : TacticM Unit := do
  let baseline ← checkedCandidatesForOnly #[]
  if let some candidate := (← searchCandidates baseline true).winner then
    report candidate
    return

  if ← runAbortFromDiscovery report then
    return

  let unfoldIds := (← relevantUnfoldNames).map mkIdent
  let effectIds := (← relevantEffectNames).map mkIdent
  let carrierFactIds ← harvestCarrierFacts (← collectFixpointCarriers)
  let carrierRewrites ← carrierFactIds.mapM fun id =>
    `(Lean.Parser.Tactic.simpLemma| $id:ident)
  if !unfoldIds.isEmpty || !effectIds.isEmpty || !carrierRewrites.isEmpty then
    let full ←
      checkedCandidatesForUnfoldEffects carrierRewrites unfoldIds effectIds
    let fullOutcome ← searchCandidates full false
    if let some winner := fullOutcome.winner then
      let minimizedWinner ←
        minimizeUnfoldEffects
          carrierRewrites unfoldIds effectIds winner
          checkedCandidatesForUnfoldEffects
      runCandidates #[minimizedWinner] false
      report minimizedWinner
      return
  if ← runStructuralDiscovery carrierRewrites unfoldIds effectIds report then
    return

  let noHintZ3 ← appendZ3Portfolio #[] #[] #[] #[] #[]
  let noHintOutcome ← searchCandidates noHintZ3 true
  if let some candidate := noHintOutcome.winner then
    report candidate
    return

  if !unfoldIds.isEmpty || !effectIds.isEmpty || !carrierRewrites.isEmpty then
    let fullEffectZ3 ←
      z3CandidatesForUnfoldEffects carrierRewrites unfoldIds effectIds
    let fullEffectOutcome ← searchCandidates fullEffectZ3 false
    if let some winner := fullEffectOutcome.winner then
      let minimizedWinner ←
        minimizeUnfoldEffects
          carrierRewrites unfoldIds effectIds winner z3CandidatesForUnfoldEffects
      runCandidates #[minimizedWinner] false
      report minimizedWinner
      return
    throwLadderExhausted fullEffectOutcome.failures

  throwLadderExhausted noHintOutcome.failures

-- A minimizing stage preserves its initial winning rung, probes only that
-- candidate shape, and replays the exact minimized winner once.
private def runDiscoveryWithHints
    (hints : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (report : MoveCandidate → TacticM Unit) : TacticM Unit := do
  if let some candidate :=
      (← searchCandidates (← checkedCandidatesForOnly #[]) true).winner then
    report candidate
    return

  let fullChecked ← checkedCandidatesForOnly hints
  let fullCheckedOutcome ← searchCandidates fullChecked false
  if let some winner := fullCheckedOutcome.winner then
    let minimizedWinner ← minimizeHints hints winner checkedCandidatesForOnly
    runCandidates #[minimizedWinner] false
    report minimizedWinner
    return

  for hint in hints do
    let single ← checkedCandidatesForOnly #[hint]
    if let some candidate := (← searchCandidates single true).winner then
      report candidate
      return

  if ← runAbortFromDiscovery report then
    return

  let unfoldIds := (← relevantUnfoldNames).map mkIdent
  let effectIds := (← relevantEffectNames).map mkIdent
  if !unfoldIds.isEmpty || !effectIds.isEmpty then
    let combinedChecked ←
      checkedCandidatesForUnfoldEffects hints unfoldIds effectIds
    let combinedCheckedOutcome ← searchCandidates combinedChecked false
    if let some winner := combinedCheckedOutcome.winner then
      let minimizedWinner ←
        minimizeUnfoldEffects
          hints unfoldIds effectIds winner checkedCandidatesForUnfoldEffects
      runCandidates #[minimizedWinner] false
      report minimizedWinner
      return
  if ← runStructuralDiscovery hints unfoldIds effectIds report then
    return

  let noHintsWithZ3 ← z3CandidatesForOnly #[]
  if let some candidate := (← searchCandidates noHintsWithZ3 true).winner then
    report candidate
    return

  let fullWithZ3 ← z3CandidatesForOnly hints
  let fullOutcome ← searchCandidates fullWithZ3 false
  if let some winner := fullOutcome.winner then
    let minimizedWinner ← minimizeHints hints winner z3CandidatesForOnly
    runCandidates #[minimizedWinner] false
    report minimizedWinner
    return

  for hint in hints do
    let single ← z3CandidatesForOnly #[hint]
    if let some candidate := (← searchCandidates single true).winner then
      report candidate
      return

  if !unfoldIds.isEmpty || !effectIds.isEmpty then
    let combinedZ3 ←
      z3CandidatesForUnfoldEffects hints unfoldIds effectIds
    let combinedOutcome ← searchCandidates combinedZ3 false
    if let some winner := combinedOutcome.winner then
      let minimizedWinner ←
        minimizeUnfoldEffects
          hints unfoldIds effectIds winner z3CandidatesForUnfoldEffects
      runCandidates #[minimizedWinner] false
      report minimizedWinner
      return
    throwLadderExhausted combinedOutcome.failures

  throwLadderExhausted fullOutcome.failures

private def runDiscoveryWithChannels
    (hints : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (factIds unfoldIds defeqIds : Array Ident) : TacticM Unit := do
  let checked ← checkedCandidatesForOnly hints
  let candidates ← appendZ3Portfolio checked hints factIds unfoldIds defeqIds
  withCatchableResourceFailure <| runCandidates candidates true

open Elab Tactic Meta

elab "move_auto_leaf_guard" : tactic => do
  pruneContextToGoalDeps
  checkLeafSuitability

elab "move_auto_unfold_telemetry" : tactic => do
  let unfoldNames ← relevantUnfoldNames
  let effectNames ← relevantEffectNames
  logInfo m!"UNFOLD_TELEMETRY unfold_count={unfoldNames.size} \
    unfold={unfoldNames} effect_count={effectNames.size} effects={effectNames}"

elab "move_auto_core" : tactic => do
  let candidates ← checkedCandidates
    (← `(tactic| move_norm_unguarded))
    (← `(tactic| move_norm_all_unguarded))
    (← `(tactic| move_norm_all_zeta_unguarded))
    (← `(tactic| move_aesop))
    (← `(tactic| grind only))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := simp) (rung := $pinnedRung)))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := omega) (rung := $pinnedRung)))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := aesop) (rung := $pinnedRung)))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := grind) (rung := $pinnedRung)))
  withCatchableResourceFailure <| runCandidates candidates false

elab "move_auto_core" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let candidates ← checkedCandidates
    (← `(tactic| move_norm_unguarded [$hs,*]))
    (← `(tactic| move_norm_all_unguarded [$hs,*]))
    (← `(tactic| move_norm_all_zeta_unguarded [$hs,*]))
    (← `(tactic| move_aesop))
    (← `(tactic| grind only))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := simp) (rung := $pinnedRung) [$hs,*]))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := omega) (rung := $pinnedRung) [$hs,*]))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := aesop) (rung := $pinnedRung) [$hs,*]))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := grind) (rung := $pinnedRung) [$hs,*]))
  withCatchableResourceFailure <| runCandidates candidates false

elab "move_auto_core" &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let candidates ← checkedCandidates
    (← `(tactic| move_norm_unguarded only [$hs,*]))
    (← `(tactic| move_norm_all_unguarded only [$hs,*]))
    (← `(tactic| move_norm_all_zeta_unguarded only [$hs,*]))
    (← `(tactic| move_aesop))
    (← `(tactic| grind only))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := simp) (rung := $pinnedRung) only [$hs,*]))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := omega) (rung := $pinnedRung) only [$hs,*]))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := aesop) (rung := $pinnedRung) only [$hs,*]))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := grind) (rung := $pinnedRung) only [$hs,*]))
  withCatchableResourceFailure <| runCandidates candidates false

-- On the failure path, everything the search logged is noise (including the
-- spurious `invalid {...} notation` errors from structural discovery's
-- re-elaboration of delaborated structure instances) and would otherwise fail
-- the surrounding module; restore the log and rethrow only the diagnostic.
private def withDiscoveryBudgetAndCleanFailure (x : TacticM Unit) : TacticM Unit := do
  let initialMessages ← Core.getMessageLog
  withCatchableResourceFailure <|
    tryCatchRuntimeEx
      (withHeartbeatBudget (← discoveryHeartbeatBudget) x)
      (fun e => do
        Core.setMessageLog initialMessages
        throw e)

elab "move_auto_discover" : tactic => do
  let pruned ← discoveryWasPruned
  withDiscoveryBudgetAndCleanFailure <|
    runAutomaticDiscovery (reportDurableProof pruned)

elab "move_auto_probe_core" candidateId:str token:str : tactic => do
  let some candidateId := candidateId.raw.isStrLit?
    | throwError "move_auto_probe requires a literal candidate id"
  let some token := token.raw.isStrLit?
    | throwError "move_auto_probe requires a literal caller token"
  let pruned ← discoveryWasPruned
  withDiscoveryBudgetAndCleanFailure <|
    runAutomaticDiscovery (reportProbeResult candidateId token pruned)

elab "move_auto_discover" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  runDiscoveryWithHints hs.getElems (reportDurableProof (← discoveryWasPruned))

elab "move_auto_discover" &"only"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let checked ← checkedCandidates
    (← `(tactic| move_norm_unguarded only [$hs,*]))
    (← `(tactic| move_norm_all_unguarded only [$hs,*]))
    (← `(tactic| move_norm_all_zeta_unguarded only [$hs,*]))
    (← `(tactic| move_aesop))
    (← `(tactic| grind only))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := simp) (rung := $pinnedRung) only [$hs,*]))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := omega) (rung := $pinnedRung) only [$hs,*]))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := aesop) (rung := $pinnedRung) only [$hs,*]))
    (fun pinnedRung =>
      `(tactic| move_auto (solver := grind) (rung := $pinnedRung) only [$hs,*]))
    (!hs.getElems.isEmpty)
  let candidates ←
    appendZ3Portfolio checked hs.getElems #[] #[] #[]
  withCatchableResourceFailure <| runCandidates candidates true

elab "move_auto_discover" &"only"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]"
    &"facts" "[" factIds:ident,* "]"
    &"unfold" "[" unfolds:ident,* "]"
    &"defeq" "[" defeqs:ident,* "]" : tactic => do
  runDiscoveryWithChannels
    hs.getElems factIds.getElems unfolds.getElems defeqs.getElems

elab "move_auto_discover"
    &"only" "[" rewrites:Lean.Parser.Tactic.simpLemma,* "]"
    &"unfold" "[" unfoldIds:ident,* "]"
    &"rules" "[" ruleIds:ident,* "]"
    &"effects" "[" effectIds:ident,* "]" : tactic => do
  runCandidates
    (← checkedCandidatesForChannels
      rewrites.getElems unfoldIds.getElems ruleIds.getElems effectIds.getElems)
    true

end Prover.MoveAuto

macro "move_auto" : tactic =>
  `(tactic| (move_auto_leaf_guard; move_auto_core))

macro "move_auto" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (move_auto_leaf_guard; move_auto_core [$hs,*]))

macro "move_auto" &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (move_auto_leaf_guard; move_auto_core only [$hs,*]))

macro "move_auto!" : tactic =>
  `(tactic| move_auto_core)

macro "move_auto!" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| move_auto_core [$hs,*])

macro "move_auto!" &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| move_auto_core only [$hs,*])

macro "move_auto?" : tactic =>
  `(tactic| (move_auto_leaf_guard; move_auto_discover))

macro "move_auto_probe" candidateId:str token:str : tactic =>
  `(tactic|
    (move_auto_leaf_guard
     move_auto_probe_core $candidateId:str $token:str))

macro "move_auto?" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (move_auto_leaf_guard; move_auto_discover [$hs,*]))

macro "move_auto?" &"only" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (move_auto_leaf_guard; move_auto_discover only [$hs,*]))

macro "move_auto?"
    &"only" "[" rewrites:Lean.Parser.Tactic.simpLemma,* "]"
    &"unfold" "[" unfoldIds:ident,* "]"
    &"rules" "[" ruleIds:ident,* "]"
    &"effects" "[" effectIds:ident,* "]" : tactic =>
  `(tactic|
    (move_auto_leaf_guard
     move_auto_discover
       only [$rewrites,*]
       unfold [$unfoldIds,*]
       rules [$ruleIds,*]
       effects [$effectIds,*]))

macro "move_auto?" &"only"
    "[" hs:Lean.Parser.Tactic.simpLemma,* "]"
    &"facts" "[" factIds:ident,* "]"
    &"unfold" "[" unfolds:ident,* "]"
    &"defeq" "[" defeqs:ident,* "]" : tactic =>
  `(tactic|
    (move_auto_leaf_guard
     move_auto_discover
       only [$hs,*]
       facts [$factIds,*]
       unfold [$unfolds,*]
       defeq [$defeqs,*]))

namespace Prover.MoveAuto

open Lean Elab Tactic Meta in
elab "move_auto_case_guard" value:term : tactic => withMainContext do
  let expression ← Term.elabTerm value none
  let type ← whnf (← inferType expression)
  let env ← getEnv
  unless type.isConstOf ``Bool || type.getAppFn.isConstOf ``Option ||
      isSafeTwoConstructorCaseType env type do
    throwError
      "move_auto cases accepts only Bool or Option discriminants, finite two-constructor \
       enums, or NoAbort/Aborted result types; got {type}"

open Lean Elab Tactic Meta in
elab "move_auto_decidable_guard" predicate:term : tactic => withMainContext do
  let proposition ← Term.elabTerm predicate none
  let propositionType ← whnf (← inferType proposition)
  unless propositionType.isProp do
    throwError
      "move_auto guards accepts only propositions; got {propositionType}"
  discard <| synthInstance (← mkAppM ``Decidable #[proposition])

end Prover.MoveAuto

macro "move_auto_structural_norm" : tactic =>
  `(tactic|
    try simp_all only
      [reduceIte,
       Bool.false_eq_true, Bool.true_eq_false,
       true_and, false_and, and_true, and_false,
       true_or, false_or, or_true, or_false,
       not_true_eq_false, not_false_eq_true])

macro_rules
  | `(tactic|
      move_auto cases [$splits:moveAutoCaseSplit,*]
        using (solver := $selectedSolver:moveAutoCheckedSolver)
          (rung := $selectedRung:ident)
        only [$rewrites:simpLemma,*]
        unfold [$unfoldIds:ident,*]
        rules [$ruleIds:ident,*]
        effects [$effectIds:ident,*]) => do
      let splits := splits.getElems
      if splits.isEmpty || splits.size > 2 then
        Macro.throwError
          "move_auto cases requires one or two explicitly named discriminants"
      let mut expansion ← match selectedSolver with
        | `(moveAutoCheckedSolver| simp) =>
            `(tactic|
              (move_auto_leaf_guard
               (move_auto_structural_norm <;>
                move_auto (solver := simp) (rung := $selectedRung)
                  only [$rewrites,*]
                  unfold [$unfoldIds,*]
                  rules [$ruleIds,*]
                  effects [$effectIds,*])))
        | `(moveAutoCheckedSolver| omega) =>
            `(tactic|
              (move_auto_leaf_guard
               (move_auto_structural_norm <;>
                move_auto (solver := omega) (rung := $selectedRung)
                  only [$rewrites,*]
                  unfold [$unfoldIds,*]
                  rules [$ruleIds,*]
                  effects [$effectIds,*])))
        | `(moveAutoCheckedSolver| aesop) =>
            `(tactic|
              (move_auto_leaf_guard
               (move_auto_structural_norm <;>
                move_auto (solver := aesop) (rung := $selectedRung)
                  only [$rewrites,*]
                  unfold [$unfoldIds,*]
                  rules [$ruleIds,*]
                  effects [$effectIds,*])))
        | `(moveAutoCheckedSolver| grind) =>
            `(tactic|
              (move_auto_leaf_guard
               (move_auto_structural_norm <;>
                move_auto (solver := grind) (rung := $selectedRung)
                  only [$rewrites,*]
                  unfold [$unfoldIds,*]
                  rules [$ruleIds,*]
                  effects [$effectIds,*])))
        | _ =>
            Macro.throwError
              "move_auto cases supports only checked simp, omega, aesop, or grind leaves"
      for split in splits.reverse do
        let `(moveAutoCaseSplit| $equation:binderIdent : $value:term) := split
          | Macro.throwUnsupported
        expansion ←
          `(tactic|
            (move_auto_case_guard $value
             cases $equation:binderIdent : $value <;> $expansion:tactic))
      return expansion
  | `(tactic|
      move_auto guards [$splits:moveAutoGuardSplit,*]
        using (solver := $selectedSolver:moveAutoCheckedSolver)
          (rung := $selectedRung:ident)
        only [$rewrites:simpLemma,*]
        unfold [$unfoldIds:ident,*]
        rules [$ruleIds:ident,*]
        effects [$effectIds:ident,*]) => do
      let splits := splits.getElems
      if splits.isEmpty || splits.size > 2 then
        Macro.throwError
          "move_auto guards requires one or two explicitly named propositions"
      let unfoldLemmas ← unfoldIds.getElems.mapM fun id =>
        `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let effectLemmas ← effectIds.getElems.mapM fun id =>
        `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let normHints := rewrites.getElems ++ unfoldLemmas ++ effectLemmas
      let mut expansion ← match selectedSolver with
        | `(moveAutoCheckedSolver| simp) =>
            `(tactic|
              (move_auto_leaf_guard
               (move_auto_structural_norm <;>
                move_auto (solver := simp) (rung := $selectedRung)
                  only [$rewrites,*]
                  unfold [$unfoldIds,*]
                  rules [$ruleIds,*]
                  effects [$effectIds,*])))
        | `(moveAutoCheckedSolver| omega) =>
            `(tactic|
              (move_auto_leaf_guard
               (move_auto_structural_norm <;>
                move_auto (solver := omega) (rung := $selectedRung)
                  only [$rewrites,*]
                  unfold [$unfoldIds,*]
                  rules [$ruleIds,*]
                  effects [$effectIds,*])))
        | `(moveAutoCheckedSolver| aesop) =>
            `(tactic|
              (move_auto_leaf_guard
               (move_auto_structural_norm <;>
                move_auto (solver := aesop) (rung := $selectedRung)
                  only [$rewrites,*]
                  unfold [$unfoldIds,*]
                  rules [$ruleIds,*]
                  effects [$effectIds,*])))
        | `(moveAutoCheckedSolver| grind) =>
            `(tactic|
              (move_auto_leaf_guard
               (move_auto_structural_norm <;>
                move_auto (solver := grind) (rung := $selectedRung)
                  only [$rewrites,*]
                  unfold [$unfoldIds,*]
                  rules [$ruleIds,*]
                  effects [$effectIds,*])))
        | _ =>
            Macro.throwError
              "move_auto guards supports only checked simp, omega, aesop, or grind leaves"
      for split in splits.reverse do
        let `(moveAutoGuardSplit| $hypothesis:ident : $predicate:term) := split
          | Macro.throwUnsupported
        let guardRewrite ←
          `(Lean.Parser.Tactic.simpLemma| $hypothesis:ident)
        expansion ←
          `(tactic|
            (move_auto_decidable_guard $predicate
             move_auto_base_guard
             by_cases $hypothesis:ident : $predicate <;>
               (try simp (discharger := assumption) only
                 [move_auto_base, move_effect, Prover.MoveAuto.reduceBoundedNatVal,
                  $normHints:simpLemma,*]) <;>
               (try simp only [$guardRewrite:simpLemma, reduceIte]) <;>
               $expansion:tactic))
      return expansion

/-!
# FvKit proof infrastructure

Corpus-agnostic proof-ceremony mechanization, absorbed verbatim from the client
overlays (`<pkg>/specs/lean/Proofs/FvKit/*.lean`) so that a single
`import Prover.MoveAuto` supplies it to every generated project.

The public surface -- `bn_val` / `bn_omega`, `mut_norm`, `peel_conj` /
`assemble_conj`, `sc_fold`, `abort_peel` / `abort_peel_all` / `abort_derive`,
and the `spec_conjuncts` command -- keeps its overlay names and semantics
exactly, so existing call sites compile after an import swap alone. The
`FvKit` namespace is kept for the same reason: overlays reference
`FvKit.<lemma>` by qualified name.

The bundles below are macro-expanded `simp only` lists rather than registered
simp-attribute sets. That is deliberate: a `register_simp_attr` set is usable
only in modules DOWNSTREAM of its registration (which is why `Prover.MoveAutoAttr`
exists at all), and -- unlike a fixed list -- a downstream overlay could tag
further lemmas into it and silently change what every call site does.

Everything here lives in `Prover/MoveAuto.lean` rather than in sibling modules
because the proof audit's generated-source scan
(`scan_generated_sources_for_z3_bypasses` in `crates/sui-lean/src/audit.rs`)
rejects proof metaprograms (`elab` / `macro` / `syntax` / `MetaM` / ...) in
every generated `.lean` file except `Prover/MoveAuto.lean`, whose bytes the
running binary pins. Splitting this content out would widen that trust-boundary
exemption for no benefit.

Compile-time tests for everything below live in the Rust harness at
`crates/lean-pipeline/tests/lake_compile_smoke.rs` (`fvkit_*` tests), not in
this file: a test shipped here would recompile inside every generated client
project.
-/

/-! ## FvKit/Bounded -- the BoundedNat `.val` ladder and `bn_omega`

Mechanizes the recurring "peel a BoundedNat operation down to its underlying
Nat and hand the residue to omega" ceremony that shows up verbatim across the
Move-derived proof corpora (ember `Process`/`Math`, scallop `Decimal`, ...).

Two pieces:

* `bn_val` -- a tactic that normalizes `.val` of BoundedNat literals and
  operations, and decodes the Bool comparators / abort predicates into Nat/Prop
  facts. Accepts an optional location (`bn_val at h`, `bn_val at *`). Every
  member lemma is rfl- or decide-provable (NEVER native_decide).

* `bn_omega` -- injects the `.property` bound (`x.val < bound`) for every
  BoundedNat hypothesis in context, normalizes goal + hyps with the `bn_val`
  bundle, then calls `omega`. Wrapping operations reduce to `(_ ) % bound`,
  which omega discharges from the injected bounds; genuine side conditions
  surface as omega-closable Nat goals.
-/

section FvKitBounded

open Lean Elab Tactic Meta

namespace FvKit

variable {bound : Nat}

/-! ### Arithmetic `.val` bridges (stated directly on `BoundedNat.*`)

The pipeline emits `BoundedNat.add`/`BoundedNat.mul` calls, not `HAdd`/`HMul`,
so the `+`-shaped Prelude lemmas (`BoundedNat.add_val`) do NOT simp-match. These
restate the same facts on the raw `BoundedNat.*` heads. `bound > 0` is recovered
from the argument's own `.property`, so the lemmas are unconditional and safe in
a simp list. -/

theorem bnadd_val (a b : BoundedNat bound) :
    (BoundedNat.add a b).val = (a.val + b.val) % bound := by
  have h : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  simp only [BoundedNat.add, h, ↓reduceDIte]

theorem bnmul_val (a b : BoundedNat bound) :
    (BoundedNat.mul a b).val = (a.val * b.val) % bound := by
  have h : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  simp only [BoundedNat.mul, h, ↓reduceDIte]

theorem bnsub_val (a b : BoundedNat bound) :
    (BoundedNat.sub a b).val = a.val - b.val := rfl

theorem bndiv_val (a b : BoundedNat bound) :
    (BoundedNat.div a b).val = a.val / b.val := rfl

theorem bnmod_val (a b : BoundedNat bound) :
    (BoundedNat.mod a b).val = a.val % b.val := rfl

/-- No-overflow specialization of `bnadd_val`, useful as an explicit `rw`/`exact`
target when the caller wants `= a.val + b.val` without going through omega. -/
theorem bnadd_val_of_lt (a b : BoundedNat bound) (h : a.val + b.val < bound) :
    (BoundedNat.add a b).val = a.val + b.val := by
  rw [bnadd_val]; exact Nat.mod_eq_of_lt h

theorem bnmul_val_of_lt (a b : BoundedNat bound) (h : a.val * b.val < bound) :
    (BoundedNat.mul a b).val = a.val * b.val := by
  rw [bnmul_val]; exact Nat.mod_eq_of_lt h

/-! ### Literal `.val` normalization (rfl-provable across the Move bounds) -/

theorem bn0_val_u8 : (0 : BoundedNat (2^8)).val = 0 := rfl
theorem bn1_val_u8 : (1 : BoundedNat (2^8)).val = 1 := rfl
theorem bn2_val_u8 : (2 : BoundedNat (2^8)).val = 2 := rfl
theorem bn0_val_u16 : (0 : BoundedNat (2^16)).val = 0 := rfl
theorem bn1_val_u16 : (1 : BoundedNat (2^16)).val = 1 := rfl
theorem bn2_val_u16 : (2 : BoundedNat (2^16)).val = 2 := rfl
theorem bn0_val_u32 : (0 : BoundedNat (2^32)).val = 0 := rfl
theorem bn1_val_u32 : (1 : BoundedNat (2^32)).val = 1 := rfl
theorem bn2_val_u32 : (2 : BoundedNat (2^32)).val = 2 := rfl
theorem bn0_val_u64 : (0 : BoundedNat (2^64)).val = 0 := rfl
theorem bn1_val_u64 : (1 : BoundedNat (2^64)).val = 1 := rfl
theorem bn2_val_u64 : (2 : BoundedNat (2^64)).val = 2 := rfl
theorem bn0_val_u128 : (0 : BoundedNat (2^128)).val = 0 := rfl
theorem bn1_val_u128 : (1 : BoundedNat (2^128)).val = 1 := rfl
theorem bn2_val_u128 : (2 : BoundedNat (2^128)).val = 2 := rfl
theorem bn0_val_u256 : (0 : BoundedNat (2^256)).val = 0 := rfl
theorem bn1_val_u256 : (1 : BoundedNat (2^256)).val = 1 := rfl
theorem bn2_val_u256 : (2 : BoundedNat (2^256)).val = 2 := rfl

end FvKit

/-! ### `bn_val` -- the normalization bundle

`simp only` over: arithmetic `.val` bridges, literal `.val` facts, the Prelude
`decide`-shaped comparator + abort decoders (`bn_lt_decide`, ...), the
`decide`-elimination lemmas, and `Nat.mod_eq_of_lt` (opportunistic mod
collapse). Accepts an optional location. -/
macro "bn_val" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only
    [ FvKit.bnadd_val, FvKit.bnmul_val, FvKit.bnsub_val, FvKit.bndiv_val,
      FvKit.bnmod_val,
      FvKit.bn0_val_u8, FvKit.bn1_val_u8, FvKit.bn2_val_u8,
      FvKit.bn0_val_u16, FvKit.bn1_val_u16, FvKit.bn2_val_u16,
      FvKit.bn0_val_u32, FvKit.bn1_val_u32, FvKit.bn2_val_u32,
      FvKit.bn0_val_u64, FvKit.bn1_val_u64, FvKit.bn2_val_u64,
      FvKit.bn0_val_u128, FvKit.bn1_val_u128, FvKit.bn2_val_u128,
      FvKit.bn0_val_u256, FvKit.bn1_val_u256, FvKit.bn2_val_u256,
      bn_lt_decide, bn_le_decide, bn_gt_decide, bn_ge_decide,
      bn_eq_decide, bn_neq_decide,
      bn_sub_aborts_decide, bn_add_aborts_decide, bn_mul_aborts_decide,
      bn_div_aborts_decide, bn_mod_aborts_decide,
      decide_eq_true_eq, decide_eq_false_iff_not,
      Nat.mod_eq_of_lt ] $[$loc]?)

/-! ### `bn_props` / `bn_omega` -/

/-- Inject `x.property : x.val < bound` as a hypothesis for every local
`BoundedNat` value in context, so omega can see the width bound that closes the
`(_ ) % bound` residues left by `bn_val`. -/
elab "bn_props" : tactic => do
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if ty.isAppOfArity ``BoundedNat 1 then
      let e := decl.toExpr
      try
        let prop ← mkAppM ``BoundedNat.property #[e]
        let pty ← inferType prop
        liftMetaTactic fun mv => do
          let mv ← mv.assert (decl.userName ++ `property) pty prop
          let (_, mv) ← mv.intro1P
          return [mv]
      catch _ => pure ()

/-- The workhorse: inject width bounds, normalize with `bn_val`, close with
omega. Wrapping arithmetic (`(a.val + b.val) % bound`) is discharged from the
injected `.property` bounds; comparators/aborts are decoded to Nat facts. -/
macro "bn_omega" : tactic =>
  `(tactic| (bn_props; (try bn_val at *); all_goals omega))

namespace FvKit

/-- Reusable Nat.blt-vs-Int-decide bridge (scallop `Decimal_specs_lt_spec`). -/
theorem nat_blt_int_decide (m n : Nat) :
    Nat.blt m n = decide ((m : Int) < (n : Int)) :=
  bool_eq_decide_of_iff ⟨fun h => by have := nat_lt_of_blt_eq_true h; omega,
    fun h => nat_blt_eq_true (by omega)⟩

end FvKit

end FvKitBounded

/-! ## FvKit/Mutation -- the `mut_norm` projection-normalization macro

NORMAL FORM (single, documented choice):
  * Borrow-projections (`borrowField` / `borrowEnumField` / `borrowMapKey`
    / `borrowVecIndex` / `ofLocal` / `ofParam`) UNFOLD to their
    `{ loc := ..., path := ..., val := ... }` record literal. This makes a
    hand-written record literal and the generated op the SAME term, which
    is exactly the manual "record-shape bridging `have`" the ember proofs
    paste in (e.g. `coin_mint_aborts_no_abort_of_lte_max`'s
    `h_supply_no_abort_norm`).
  * Value-writes (`set` / `updateValue`) stay FOLDED, but every projection
    `.val` / `.path` / `.loc` off any Mutation op or literal reduces to its
    component (`val_set`, `path_set`, `loc_set`, `val_updateValue`, ...). This
    is what actually closes the `h_vaultSeq_generated` bridge: the inner
    `(set (borrowField ...) v).val` collapses to `v` by `val_set` alone,
    without exposing `set`'s record shape.
  * `isSameMutation` drops a `set` / `updateValue` on either side (loc/path
    are invariant under a value write), keeping the predicate FOLDED so its
    boolean internals are never spilled into the goal.

`val_set` and `val_borrowField` are already global `@[simp]` in
`Prelude.Mutation`; here they are bundled explicitly into the `mut_norm`
macro (plus the missing path/loc companions and the record bridges) so that
`mut_norm` -- a `simp only` over the explicit list -- is self-sufficient and
needs none of the ambient global-simp set.

These record bridges duplicate the statements of `Prover.MoveAuto.borrowField_mk`
and friends above. Both spellings are kept: the `Prover.MoveAuto.*` copies are
pinned members of the frozen `move_auto_base` simp registry, while these carry
the `Prover.Mutation.Mutation.*` names the overlay corpora already reference.
-/

section FvKitMutation

namespace Prover.Mutation.Mutation

variable {Key : Type} {S T V : Type}

-- ---- Record bridges: borrow-op <-> `{ loc, path, val }` literal ----
-- These are the mechanized form of the manual `simpa [borrowField] using h`
-- record-shape normalization `have`s.

theorem borrowField_mk
    (m : Mutation Key S) (sid offset : Nat) (sel : S -> T) :
    borrowField m sid offset sel =
      { loc := m.loc, path := m.path ++ [Edge.structField sid offset],
        val := sel m.val } := rfl

theorem borrowEnumField_mk
    (m : Mutation Key S) (sid variant offset : Nat) (sel : S -> T) :
    borrowEnumField m sid variant offset sel =
      { loc := m.loc, path := m.path ++ [Edge.enumField sid variant offset],
        val := sel m.val } := rfl

theorem borrowMapKey_mk
    (m : Mutation Key S) (k : Key) (lookup : S -> Key -> V) :
    borrowMapKey m k lookup =
      { loc := m.loc, path := m.path ++ [Edge.mapKey k],
        val := lookup m.val k } := rfl

theorem borrowVecIndex_mk
    (m : Mutation Key (List T)) (i : Nat) [Inhabited T] :
    borrowVecIndex m i =
      { loc := m.loc, path := m.path ++ [Edge.vecIndex i],
        val := m.val.getD i default } := rfl

theorem ofLocal_mk (i : Nat) (v : T) :
    (ofLocal (Key := Key) i v) = { loc := .localRoot i, path := [], val := v } := rfl

theorem ofParam_mk (i : Nat) (v : T) :
    (ofParam (Key := Key) i v) = { loc := .param i, path := [], val := v } := rfl

-- ---- isSameMutation interaction (drop a value-write, predicate folded) ----

theorem isSameMutation_set_left [BEq Key]
    (a : Mutation Key S) (v : S) (b : Mutation Key T) :
    isSameMutation (a.set v) b = isSameMutation a b := rfl

theorem isSameMutation_set_right [BEq Key]
    (a : Mutation Key S) (b : Mutation Key T) (v : T) :
    isSameMutation a (b.set v) = isSameMutation a b := rfl

theorem isSameMutation_updateValue_left [BEq Key]
    (a : Mutation Key S) (v : S) (b : Mutation Key T) :
    isSameMutation (a.updateValue v) b = isSameMutation a b := rfl

theorem isSameMutation_updateValue_right [BEq Key]
    (a : Mutation Key S) (b : Mutation Key T) (v : T) :
    isSameMutation a (b.updateValue v) = isSameMutation a b := rfl

end Prover.Mutation.Mutation

-- ---- The one-liner idiom -------------------------------------------------
-- `mut_norm`        : normalize the goal to record/projection normal form.
-- `mut_norm at h`   : same, in hypothesis `h`.
--
-- The bundle is the record bridges above plus the prelude projection lemmas
-- (`val_set` / `val_borrowField` are already global `@[simp]`; the path/loc/val
-- companions let `mut_norm` reduce every projection off a folded value-write or
-- an unfolded borrow-record without leaning on the ambient global simp set).

macro "mut_norm" : tactic =>
  `(tactic| simp only
    [ Prover.Mutation.Mutation.borrowField_mk,
      Prover.Mutation.Mutation.borrowEnumField_mk,
      Prover.Mutation.Mutation.borrowMapKey_mk,
      Prover.Mutation.Mutation.borrowVecIndex_mk,
      Prover.Mutation.Mutation.ofLocal_mk,
      Prover.Mutation.Mutation.ofParam_mk,
      Prover.Mutation.Mutation.path_updateValue,
      Prover.Mutation.Mutation.loc_updateValue,
      Prover.Mutation.Mutation.isSameMutation_set_left,
      Prover.Mutation.Mutation.isSameMutation_set_right,
      Prover.Mutation.Mutation.isSameMutation_updateValue_left,
      Prover.Mutation.Mutation.isSameMutation_updateValue_right,
      Prover.Mutation.Mutation.val_updateValue,
      Prover.Mutation.Mutation.val_set,
      Prover.Mutation.Mutation.path_set,
      Prover.Mutation.Mutation.loc_set,
      Prover.Mutation.Mutation.val_borrowField,
      Prover.Mutation.Mutation.val_borrowEnumField,
      Prover.Mutation.Mutation.val_borrowMapKey,
      Prover.Mutation.Mutation.val_borrowVecIndex,
      Prover.Mutation.Mutation.val_ofLocal,
      Prover.Mutation.Mutation.path_ofLocal,
      Prover.Mutation.Mutation.loc_ofLocal,
      Prover.Mutation.Mutation.val_ofParam,
      Prover.Mutation.Mutation.path_ofParam,
      Prover.Mutation.Mutation.loc_ofParam ])

macro "mut_norm" "at" h:Lean.Parser.Tactic.locationHyp : tactic =>
  `(tactic| simp only
    [ Prover.Mutation.Mutation.borrowField_mk,
      Prover.Mutation.Mutation.borrowEnumField_mk,
      Prover.Mutation.Mutation.borrowMapKey_mk,
      Prover.Mutation.Mutation.borrowVecIndex_mk,
      Prover.Mutation.Mutation.ofLocal_mk,
      Prover.Mutation.Mutation.ofParam_mk,
      Prover.Mutation.Mutation.path_updateValue,
      Prover.Mutation.Mutation.loc_updateValue,
      Prover.Mutation.Mutation.isSameMutation_set_left,
      Prover.Mutation.Mutation.isSameMutation_set_right,
      Prover.Mutation.Mutation.isSameMutation_updateValue_left,
      Prover.Mutation.Mutation.isSameMutation_updateValue_right,
      Prover.Mutation.Mutation.val_updateValue,
      Prover.Mutation.Mutation.val_set,
      Prover.Mutation.Mutation.path_set,
      Prover.Mutation.Mutation.loc_set,
      Prover.Mutation.Mutation.val_borrowField,
      Prover.Mutation.Mutation.val_borrowEnumField,
      Prover.Mutation.Mutation.val_borrowMapKey,
      Prover.Mutation.Mutation.val_borrowVecIndex,
      Prover.Mutation.Mutation.val_ofLocal,
      Prover.Mutation.Mutation.path_ofLocal,
      Prover.Mutation.Mutation.loc_ofLocal,
      Prover.Mutation.Mutation.val_ofParam,
      Prover.Mutation.Mutation.path_ofParam,
      Prover.Mutation.Mutation.loc_ofParam ] at $h)

end FvKitMutation

/-! ## FvKit/Conj -- `peel_conj` / `assemble_conj`

Corpus-agnostic conjunction ceremony. The generated `spec.asserts` fields are
long `(a && b && ... ) = true` chains built with arbitrary `&&` association, and
consumers destructure them with hand-written N-deep nested `rcases` tuples (see
ember Getaway/Vault, scallop Reserve, current-lending User_oracle). These two
tactics replace that boilerplate:

  * `peel_conj h`           normalize `h` via `Bool.and_eq_true` and split the
                            whole And / Bool-&& tree into `h_1 .. h_n`
                            (left-to-right source order, any association).
  * `peel_conj h with pat`  same normalization, then destructure with an
                            explicit rcases-style pattern.
  * `assemble_conj`         close an `(a && b && ...) = true` / And goal from the
                            context via a refine-ladder + assumption search.
-/

section FvKitConj

namespace FvKit

open Lean Elab Tactic Meta

private def isAnd? (ty : Expr) : Option (Expr × Expr) :=
  if ty.isAppOfArity ``And 2 then
    some (ty.appFn!.appArg!, ty.appArg!)
  else
    none

private partial def buildPeelPat (ty : Expr) (counter : IO.Ref Nat) :
    MetaM (TSyntax `rcasesPat) := do
  match isAnd? ty with
  | some (p, q) =>
    let pp ← buildPeelPat p counter
    let pq ← buildPeelPat q counter
    `(rcasesPat| ⟨$pp, $pq⟩)
  | none =>
    let i ← counter.modifyGet (fun n => (n, n + 1))
    let id := mkIdent (Name.mkSimple s!"h_{i}")
    `(rcasesPat| $id:ident)

elab "peel_conj " h:ident : tactic => do
  evalTactic (← `(tactic| try simp only [Bool.and_eq_true] at $h:ident))
  withMainContext do
    let e ← elabTerm h none
    let ty ← whnfR (← inferType e)
    let counter ← IO.mkRef 1
    let pat ← buildPeelPat ty counter
    evalTactic (← `(tactic| obtain $pat := $h))

elab "peel_conj " h:ident " with " pat:rcasesPat : tactic => do
  evalTactic (← `(tactic| try simp only [Bool.and_eq_true] at $h:ident))
  withMainContext do
    evalTactic (← `(tactic| obtain $pat := $h))

elab "assemble_conj" : tactic => do
  evalTactic (← `(tactic| try simp only [Bool.and_eq_true]))
  evalTactic (← `(tactic| repeat' apply And.intro))
  evalTactic (← `(tactic| all_goals assumption))

end FvKit

end FvKitConj

/-! ## FvKit/ScFold -- `sc_fold`: the Move short-circuit Bool simplifications

Move compiles `&&` / `||` to short-circuiting control flow, so the renderer
emits value-level conjuncts as `ite` chains rather than fused `&&`:

  * pure-Bool short-circuit:  `if c then b else false`  (a Move `c && b`)
                              `if c then true else b`   (a Move `c || b`)
  * world-threaded pair ite:  `(if c then (a, w) else (b, w')).1`
                              `(if c then (a, w) else (b, w')).2`

`sc_fold` rewrites those value-level shapes back to their fused Bool form so the
`spec_conjuncts` projection lemmas (which name fused `&&` conjuncts) apply. Each
lemma is `cases c <;> rfl`. This is a plain lemma set threaded through a macro --
NO global simp attribute -- so nothing here changes ambient `simp` behavior.

SCOPE: value-level goals / hypotheses ONLY. Do NOT use on `.aborts` companions:
there the `ite` encodes Move abort ordering (the guard aborts the whole call),
not a Bool conjunct, and folding it discards the abort semantics. The
split-based `abort_peel` / `abort_derive` tools below are the right instruments
for `.aborts` chains.
-/

section FvKitScFold

namespace FvKit.ScFold

theorem ite_false_eq_and (c b : Bool) :
    (if c then b else false) = (c && b) := by
  cases c <;> rfl

theorem ite_true_eq_or (c b : Bool) :
    (if c then true else b) = (c || b) := by
  cases c <;> rfl

theorem ite_pair_fst {A W : Type} (c : Bool) (a b : A) (w w' : W) :
    (if c then (a, w) else (b, w')).1 = (if c then a else b) := by
  cases c <;> rfl

theorem ite_pair_snd {A W : Type} (c : Bool) (a b : A) (w w' : W) :
    (if c then (a, w) else (b, w')).2 = (if c then w else w') := by
  cases c <;> rfl

end FvKit.ScFold

macro "sc_fold" : tactic =>
  `(tactic| simp only [FvKit.ScFold.ite_false_eq_and, FvKit.ScFold.ite_true_eq_or,
      FvKit.ScFold.ite_pair_fst, FvKit.ScFold.ite_pair_snd])

macro "sc_fold" " at " h:ident : tactic =>
  `(tactic| simp only [FvKit.ScFold.ite_false_eq_and, FvKit.ScFold.ite_true_eq_or,
      FvKit.ScFold.ite_pair_fst, FvKit.ScFold.ite_pair_snd] at $h:ident)

end FvKitScFold

/-! ## FvKit/Abort -- `abort_peel` / `abort_peel_all` / `abort_derive`

The dominant ember/scallop "no-abort" ceremony is a chain of blocks that each
strip one callee off a composed `.aborts` hypothesis:

    have h_callee : callee.aborts args = NoAbort := by
      cases hc : callee.aborts args
      · rfl
      · simp [composed.aborts, <prior facts>, hc] at h_composed

Every such block re-`simp`-unfolds the *whole* outer `.aborts` definition from
scratch -- quadratic in the number of callees. `abort_peel` instead assumes the
composed `.aborts` companion has already been unfolded (once) by the caller --
via an explicit `unfold`/`simp only [<def>]` -- into a nest of
`match callee.aborts with | NoAbort => cont | Aborted c => Aborted c`,
interleaved with the abort-guard `if`s the generator emits -- and then advances
the hypothesis one layer per peel, carrying the residual continuation instead
of rebuilding it. Peeling n layers costs one unfold plus n `split`s -- linear.

Peeling is pure `split`: the caller unfolds the composed `.aborts` / `.aborts.cont_k`
defs once up front (the successful Deposit-wave cadence), then each peel just
splits the exposed head `match` / `if`.

Type-agnostic: the macros never name the abort result type, so they work on any
two-constructor `NoAbort` / `Aborted` companion (`Prover.Abort.AbortResult`, the
legacy `MoveAbort`, or a local mock) without importing it.
-/

section FvKitAbort

namespace FvKit

/-- One peel step. From `h : composed.aborts … = NoAbort` (already unfolded),
expose the head layer, prove `hn : headCallee.aborts … = NoAbort` (for a callee
`match`) or a boolean guard fact (for an abort-guard `if`), and rewrite `h` in
place to the residual continuation so the next peel does not re-unfold.

Mechanism: `split at h` exposes the head `match` / `if`; `<;>` closes the
`Aborted` branch by constructor distinctness (`reduceCtorEq`) while the surviving
branch carries the advanced `h`; `rename_i` names the discriminant equation. The
composed `.aborts` must already be unfolded by the caller.

Forms:
* `abort_peel h`               -- discriminant left inaccessible (recover via `rename_i`)
* `abort_peel h with hn`       -- name the discriminant fact `hn`
* `abort_peel h : callee`      -- `callee` is informational (documents the head)
* `abort_peel h : callee with hn` -/
syntax (name := abortPeel) "abort_peel " ident (" : " term)? (" with " ident)? : tactic

macro_rules
  | `(tactic| abort_peel $h:ident) =>
    `(tactic| (split at $h:ident <;> first | simp only [reduceCtorEq] at $h:ident | skip))
  | `(tactic| abort_peel $h:ident with $hn:ident) =>
    `(tactic| (split at $h:ident <;> first | simp only [reduceCtorEq] at $h:ident | skip
               rename_i $hn:ident))
  | `(tactic| abort_peel $h:ident : $_callee:term) =>
    `(tactic| abort_peel $h:ident)
  | `(tactic| abort_peel $h:ident : $_callee:term with $hn:ident) =>
    `(tactic| abort_peel $h:ident with $hn:ident)

/-- Peel every layer off `h` in one shot (the composed `.aborts` already
unfolded by the caller), splitting (and closing each `Aborted` branch) until the
tail leaf (no wrapping `match` / `if`) is reached; `h` ends as
`lastCallee.aborts … = NoAbort`. Intermediate facts land as inaccessible
hypotheses (recover with `rename_i`); use single `abort_peel … with hn` when you
need names as you go. -/
syntax (name := abortPeelAll) "abort_peel_all " ident : tactic

macro_rules
  | `(tactic| abort_peel_all $h:ident) =>
    `(tactic| (repeat (split at $h:ident <;> (try simp only [reduceCtorEq] at $h:ident))))

/-!
### `abort_derive` -- dialect 2 (targeted callee extraction, non-consuming)

`abort_peel` / `abort_peel_all` implement *dialect 1*: they advance a single
composed `.aborts` hypothesis down its continuation chain, consuming it layer by
layer. The corpus also contains a second, more common shape (*dialect 2*): each
callee's no-abort fact is re-derived **directly from the raw, un-advanced**
composed hypothesis, which is kept intact because later blocks still need it. The
hand-written ceremony is, for every callee:

    have h_callee : callee.aborts args = NoAbort := by
      cases hc : callee.aborts args
      · rfl
      · simp [composed.aborts, <all cont_k>, <prior facts…>, hc] at h_composed

Every block re-unfolds the whole composed `.aborts` (plus whichever `.cont_k`
continuations it reaches) and re-feeds every previously-established fact so simp
can collapse the earlier match/if layers before contradicting the current one.

`abort_derive` mechanises exactly that block:

    abort_derive h_composed : callee.aborts args with h_callee
    abort_derive h_composed : callee.aborts args unfolding [n1, n2] with h_callee

Given `h_composed : composed.aborts cargs = NoAbort` it introduces
`h_callee : callee.aborts args = NoAbort` **without touching `h_composed`** (the
`cases`/`simp` runs inside the isolated `have`, so the outer hypothesis is
preserved). Discovery is automatic and uses only environment queries -- no
attribute, no import-time registration, no global `@[simp]`:

* **Unfold closure (lazy).** The composed head constant is read off the LHS of
  `h_composed`. Its `.cont_*` continuation family (every `defnInfo` whose name
  reduces to that head by stripping `.cont_*` segments) is discovered and tagged
  with continuation depth, but **not** thrown at simp all at once: dumping the
  whole (often 8-deep) tree into one `simp only` makes simp unfold the entire
  continuation nest -- a traversal blow-up (the 285s pathology). Instead only the
  head is unfolded first, and cont layers are added by *increasing depth*, the
  tactic stopping at the shallowest prefix that closes the goal -- one layer per
  round, exactly like `abort_peel_all` advances one `split` per layer. A
  head-level callee (the common case) unfolds the head alone and never touches
  the cont family. Each too-shallow attempt is rolled back before the next, so
  the tactic state the caller sees is the successful one.
* **Guard/prior facts.** Every local hypothesis of the form `_ = <ctor …>`
  (any constructor -- `NoAbort`, `Aborted`, `true`, `false`, …), except
  `h_composed` itself, is added, so earlier match/if layers collapse exactly as
  the hand-written `simp` fed them.
* `reduceCtorEq` supplies the final `Aborted _ = NoAbort → False` contradiction,
  and `reduceIte` collapses the abort-guard `if`s the generator interleaves
  between callee matches once the guard fact (a prior) has fixed the condition.

The abort result type is never named -- the target's RHS constructor is copied
from `h_composed`'s own RHS, so the tactic stays type-agnostic like the macros.

`unfolding [n1, n2, …]` appends extra simp arguments for sites whose composed body
threads helper `.aborts` defs or normalisation lemmas that are not part of the
continuation family (e.g. the Pyth chain in `get_oracle_price`, or the u128
add-guard normalisers in `deposit_mc_asset`). It is the escape hatch when
automatic closure alone leaves a residual goal. -/
syntax (name := abortDerive)
  "abort_derive " ident " : " moveAbortTermBeforeUnfolding
    (moveAbortUnfoldingClause)? " with " ident : tactic

open Lean Elab Tactic Meta in
/-- True iff `n` reduces to `head` by stripping zero or more `.cont_*` tail
segments -- i.e. `n` is the composed head itself or one of its generated
continuation constants. -/
private partial def isContFamily (head : Name) : Name → Bool
  | n =>
    if n == head then true
    else match n with
      | .str p s => s.startsWith "cont_" && isContFamily head p
      | _ => false

open Lean Elab Tactic Meta in
/-- Continuation depth of a family member: how many `.cont_*` tail segments
separate `n` from `head`. The head itself is depth `0`; `head.cont_0` is `1`;
`head.cont_0.cont_0` is `2`; etc. Only meaningful when `isContFamily head n`. -/
private partial def contDepth (head : Name) : Name → Nat
  | n =>
    if n == head then 0
    else match n with
      | .str p s => if s.startsWith "cont_" then contDepth head p + 1 else 0
      | _ => 0

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| abort_derive $h:ident : $callee:term
        $[unfolding [$extra,*]]? with $hn:ident) => do
    withMainContext do
      let hE ← elabTerm h none
      let hFVarId := hE.fvarId!
      let hTy ← instantiateMVars (← inferType hE)
      let some (_, lhs, rhs) := hTy.eq?
        | throwError "abort_derive: `{h}` is not an equation `_ = _`"
      let headName ← match lhs.getAppFn with
        | .const n _ => pure n
        | _ => throwError
            "abort_derive: LHS of `{h}` is not a constant application"
      let rhsCtor ← match rhs.getAppFn with
        | .const c _ => pure c
        | _ => throwError
            "abort_derive: RHS of `{h}` is not a constructor application"
      let env ← getEnv
      -- Unfold closure: the composed head + its `.cont_*` continuation family,
      -- tagged with continuation depth so the layers can be added *lazily*.
      -- The naive tactic dumped the ENTIRE family into one `simp only`, forcing
      -- simp to unfold the whole (often 8-deep) continuation tree at once -- a
      -- traversal blow-up. Instead we add layers by increasing depth and stop at
      -- the shallowest set that closes the goal (mirroring `abort_peel_all`,
      -- which advances one layer per split).
      let headStx : Array (TSyntax `term) :=
        if env.contains headName then #[mkCIdent headName] else #[]
      let mut fam : Array (Name × Nat) := #[]
      for (n, ci) in env.constants.toList do
        if n == headName then continue
        match ci with
        | .defnInfo _ => if isContFamily headName n then
            fam := fam.push (n, contDepth headName n)
        | _ => pure ()
      let maxDepth := fam.foldl (init := 0) (fun m x => Nat.max m x.2)
      -- Guard/prior facts: local `_ = <ctor …>` hypotheses, minus `h` itself.
      let mut factStx : Array (TSyntax `term) := #[]
      for decl in (← getLCtx) do
        if decl.isImplementationDetail then continue
        if decl.fvarId == hFVarId then continue
        let some (_, _, frhs) := (← instantiateMVars decl.type).eq? | continue
        match frhs.getAppFn with
        | .const c _ =>
          match env.find? c with
          | some (.ctorInfo _) => factStx := factStx.push (mkIdent decl.userName)
          | _ => pure ()
        | _ => pure ()
      let extraStx : Array (TSyntax `term) :=
        match extra with
        | some elems => elems.getElems
        | none => #[]
      let rhsStx : TSyntax `term := mkCIdent rhsCtor
      -- Build the `have` for a given simp-lemma set (the fixed head/prior/extra
      -- context is spliced in; `lemmas` is the lazily-grown cont layer set).
      let buildTac := fun (lemmas : Array (TSyntax `term)) => do
        let simpLemmas ← (headStx ++ lemmas ++ factStx ++ extraStx).mapM
          fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
        `(tactic|
          have $hn:ident : $callee = $rhsStx := by
            cases __hp : $callee <;>
              simp only [$simpLemmas,*, __hp, reduceCtorEq, reduceIte] at $h:ident ⊢ <;>
              repeat
                (split at $h:ident <;>
                  try simp only [reduceCtorEq, reduceIte] at $h:ident))
      -- Attempt a set non-destructively: run it, keep the state on success,
      -- roll back on failure so the next (deeper) attempt starts clean.
      -- A too-shallow attempt leaves the residual `have` goal *unsolved*; under
      -- `errToSorry` that is *logged* (not thrown), so catching exceptions alone
      -- would miss it and wrongly accept the first attempt. We compare the error
      -- count around the run and treat any new error as failure, restoring both
      -- the tactic state and the message log so the next attempt starts clean.
      let errCount : TacticM Nat := do
        pure ((← getThe Core.State).messages.toList.filter
          (fun m => m.severity matches MessageSeverity.error)).length
      let attempt := fun (lemmas : Array (TSyntax `term)) => do
        let tac ← buildTac lemmas
        let st ← saveState
        let msgsBefore := (← getThe Core.State).messages
        let before ← errCount
        let threw ←
          try
            evalTactic tac
            pure false
          catch _ => pure true
        let after ← errCount
        if threw || after > before then
          st.restore
          modifyThe Core.State (fun s => { s with messages := msgsBefore })
          pure false
        else
          pure true
      -- Lazily grow the cont set by increasing depth; stop at the first (hence
      -- shallowest, hence smallest) prefix that closes the goal.
      let mut solved := false
      for d in [0:maxDepth + 1] do
        if !solved then
          let conts := (fam.filter (fun x => x.2 ≤ d)).map (fun x => mkCIdent x.1)
          if ← attempt conts then
            solved := true
      -- Fallback: the full family (the original, exhaustive set). Only reached
      -- when no depth prefix sufficed; runs destructively so a genuine failure
      -- surfaces its real error message.
      if !solved then
        let conts := fam.map (fun x => mkCIdent x.1)
        evalTactic (← buildTac conts)

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| abort_from $h:ident $[unfolding [$extra,*]]?) => do
    withMainContext do
      let target ← instantiateMVars (← (← getMainGoal).getType)
      let some (_, callee, targetRhs) := target.eq?
        | throwError "abort_from: target is not an equation `_ = _`"
      let hypothesis ← elabTerm h none
      let hypothesisType ← instantiateMVars (← inferType hypothesis)
      let some (_, _, composedRhs) := hypothesisType.eq?
        | throwError "abort_from: `{h}` is not an equation `_ = _`"
      unless ← isDefEq targetRhs composedRhs do
        throwError
          "abort_from: target RHS {targetRhs} does not match `{h}` RHS {composedRhs}"
      let calleeSyntax ← PrettyPrinter.delab callee
      let derivedName := mkIdent (← mkFreshUserName `h_abort_from)
      let tactic ← match extra with
        | some extra =>
          `(tactic|
            (abort_derive $h:ident : $calleeSyntax:term
               unfolding [$extra,*] with $derivedName:ident
             exact $derivedName:ident))
        | none =>
          `(tactic|
            (abort_derive $h:ident : $calleeSyntax:term
               with $derivedName:ident
             exact $derivedName:ident))
      evalTactic tactic

end FvKit

end FvKitAbort

/-! ## FvKit/SpecConj -- the `spec_conjuncts` naming command

The renderer emits, next to each conjunction-tree companion
(`<spec>.asserts` / `.ensures` / `.requires`), a family of anonymous leaf
defs `<spec>.asserts.c<k>` and ONE characterization theorem `<spec>.asserts_conj`.
For a Bool `.asserts` companion this is an equation
`<spec>.asserts <args> = (c1 <..> && (c2 <..> && ...))` proved `rfl`. For a Prop
`.requires`/`.ensures` companion (whose body is a Bool `&&`-tree lifted into Prop
by the `Bool -> Prop` coercion) it is instead an iff
`<spec>.ensures <args> <-> ((c1 <..> && (c2 <..> && ...)) = true)` proved `Iff.rfl`:
the right side is the same Bool `&&`-tree under the coercion (`b` becomes `b = true`).
Either way the tree is positional and drift-prone.

`spec_conjuncts` is the naming contract, authored once per spec by a human or
agent in the overlay. It brings the companion's binders into scope (so patterns
mention the real argument names), defeq-matches each pattern against the leaf
conjuncts (defeq sees through generated let-noise), and generates one
semantically named projection theorem per bound name:

  `<spec>.asserts.<name> <binders> (h : <spec>.asserts <args> = true)
      : c_k <args> = true`

For an iff (Prop) companion the hypothesis is instead the bare Prop
`(h : <spec>.ensures <args>)`; the conclusion keeps `c_k <args> = true` whenever
the leaves are Bool (the coerced `&&`-tree case, i.e. all real renderer output)
and drops `= true` only for a genuinely Prop-valued `∧`-tree. The proof rewrites
with the characterization theorem (`Iff.mp` in the iff case, `Eq.mp`/`Eq.trans`
otherwise) and walks the `&&` / `∧` tree by structure -- the same left-to-right
walker `peel_conj` uses -- so it is association-agnostic and never searches.

Authoring shape:

  spec_conjuncts specs.Vault_specs.mint_mc_shares_spec.asserts with
    | package_version_ok  => BoundedNat.eq (Admin.get_version config) Admin.get_package_version
    | protocol_not_paused => !(Admin.get_paused config)
    | _ => _                 -- explicit skip for one deliberately unnamed conjunct
    | 7 as sequence_in_range -- index-pinned fallback when defeq matching is pathological

Semantics: EXHAUSTIVE by default -- every conjunct must be named, index-pinned,
or absorbed by a `| _ => _` skip, else an error lists each unbound conjunct
(index + pretty body). A pattern matching zero conjuncts, or more than one, is an
error at the naming block -- never inside a downstream proof.
-/

section FvKitSpecConj

namespace FvKit.SpecConj

open Lean Meta Elab Command Term

inductive ConjMode where
  | bool
  | prop
deriving Inhabited

def modeOfType? (ty : Expr) : Option ConjMode :=
  if ty.isConstOf ``Bool then some .bool
  else if ty.isProp then some .prop
  else none

partial def treeLeaves : ConjMode → Expr → Array Expr
  | .bool, e =>
    if e.isAppOfArity ``Bool.and 2 then
      treeLeaves .bool e.appFn!.appArg! ++ treeLeaves .bool e.appArg!
    else #[e]
  | .prop, e =>
    if e.isAppOfArity ``And 2 then
      treeLeaves .prop e.appFn!.appArg! ++ treeLeaves .prop e.appArg!
    else #[e]

partial def extractLeaf (mode : ConjMode) (e h : Expr) (idx : Nat) : MetaM Expr := do
  match mode with
  | .bool =>
    if e.isAppOfArity ``Bool.and 2 then
      let a := e.appFn!.appArg!
      let b := e.appArg!
      let la := (treeLeaves .bool a).size
      let hAnd ← mkAppM ``Eq.mp #[← mkAppM ``Bool.and_eq_true #[a, b], h]
      if idx < la then extractLeaf .bool a (← mkAppM ``And.left #[hAnd]) idx
      else extractLeaf .bool b (← mkAppM ``And.right #[hAnd]) (idx - la)
    else return h
  | .prop =>
    if e.isAppOfArity ``And 2 then
      let a := e.appFn!.appArg!
      let b := e.appArg!
      let la := (treeLeaves .prop a).size
      if idx < la then extractLeaf .prop a (← mkAppM ``And.left #[h]) idx
      else extractLeaf .prop b (← mkAppM ``And.right #[h]) (idx - la)
    else return h

def defeqNoLeak (a b : Expr) : MetaM Bool := do
  let s ← saveState
  let r ← isDefEq a b
  s.restore
  return r

declare_syntax_cat specConjEntry
syntax "| " ident " => " term : specConjEntry
syntax "| " "_" " => " "_" : specConjEntry
syntax "| " num ident ident : specConjEntry

def specConjunctsKeyword :=
  leading_parser (Lean.Parser.nonReservedSymbol "spec_conjuncts" true)

syntax (name := specConjuncts)
  specConjunctsKeyword ident " with " specConjEntry+ : command

elab_rules : command | `(specConjuncts| spec_conjuncts $companion:ident with $entries:specConjEntry*) => do
  let cname ← liftCoreM <| realizeGlobalConstNoOverload companion
  liftTermElabM do
    let cinfo ← getConstInfo cname
    unless cinfo.levelParams.isEmpty do
      throwError "spec_conjuncts: universe-polymorphic companion `{cname}` not supported"
    let conjName := cname.appendAfter "_conj"
    let conjInfo ← getConstInfo conjName
    unless conjInfo.levelParams.isEmpty do
      throwError "spec_conjuncts: universe-polymorphic characterization `{conjName}` not supported"
    forallTelescope conjInfo.type fun xs body => do
      let (mode, companionApp, tree, isIff) ← do
        if let some (α, lhs, rhs) := body.eq? then
          let some m := modeOfType? α
            | throwError "spec_conjuncts: companion result type must be Bool or Prop"
          pure (m, lhs, rhs, false)
        else if body.isAppOfArity ``Iff 2 then
          let lhs := body.appFn!.appArg!
          let rhs := body.appArg!
          match rhs.eq? with
          | some (α, boolTree, boolRhs) =>
            if α.isConstOf ``Bool && boolRhs.isConstOf ``Bool.true then
              pure (ConjMode.bool, lhs, boolTree, true)
            else
              pure (ConjMode.prop, lhs, rhs, true)
          | none => pure (ConjMode.prop, lhs, rhs, true)
        else
          throwError "spec_conjuncts: `{conjName}` is neither an equation nor an iff"
      let leaves := treeLeaves mode tree
      let n := leaves.size
      let conjProof := mkAppN (mkConst conjName []) xs
      let expectedTy := match mode with
        | .bool => mkConst ``Bool
        | .prop => mkSort Level.zero
      let mut covered : Array (Nat × Name) := #[]
      let mut skipCount := 0
      for e in entries do
        match e with
        | `(specConjEntry| | _ => _) =>
          skipCount := skipCount + 1
        | `(specConjEntry| | $k:num $keyword:ident $nm:ident) =>
          unless keyword.getId == `as do
            throwError "spec_conjuncts: expected `as` before index-pinned name"
          let ki := k.getNat
          if ki < 1 || ki > n then
            throwError "spec_conjuncts: index {ki} out of range 1..{n}"
          covered := covered.push (ki - 1, cname.str nm.getId.toString)
        | `(specConjEntry| | $nm:ident => $pat:term) =>
          let patExpr ← instantiateMVars (← elabTermAndSynthesize pat (some expectedTy))
          let mut hits : Array Nat := #[]
          for i in [0:n] do
            if ← defeqNoLeak patExpr leaves[i]! then
              hits := hits.push i
          if hits.isEmpty then
            throwError "spec_conjuncts: pattern for `{nm.getId}` matched no conjunct"
          if hits.size > 1 then
            throwError "spec_conjuncts: pattern for `{nm.getId}` is ambiguous (matches conjuncts {hits.map (· + 1)})"
          covered := covered.push (hits[0]!, cname.str nm.getId.toString)
        | _ => throwError "spec_conjuncts: unrecognized entry"
      let coveredIdx := covered.map (·.1)
      let mut leftover : Array Nat := #[]
      for i in [0:n] do
        unless coveredIdx.contains i do leftover := leftover.push i
      if leftover.size != skipCount then
        if skipCount > leftover.size then
          throwError "spec_conjuncts: {skipCount} `_ => _` skip(s) but only {leftover.size} unbound conjunct(s)"
        else
          let mut msg := m!"spec_conjuncts: {leftover.size - skipCount} conjunct(s) unbound (add a naming entry or `| _ => _`):"
          for i in leftover do
            let leafBody := (← unfoldDefinition? leaves[i]!).getD leaves[i]!
            msg := msg ++ m!"\n  #{i + 1}: {leafBody}"
          throwError msg
      let companionIsBool := !isIff && (match mode with | .bool => true | .prop => false)
      let hypType ←
        if companionIsBool then mkEq companionApp (mkConst ``Bool.true)
        else pure companionApp
      withLocalDeclD `h hypType fun h => do
        let htree ←
          if isIff then mkAppM ``Iff.mp #[conjProof, h]
          else match mode with
            | .bool => mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[conjProof], h]
            | .prop => mkAppM ``Eq.mp #[conjProof, h]
        for (idx, thmName) in covered do
          let proof ← extractLeaf mode tree htree idx
          let concl ← match mode with
            | .bool => mkEq leaves[idx]! (mkConst ``Bool.true)
            | .prop => pure leaves[idx]!
          let value ← mkLambdaFVars (xs.push h) proof
          let type ← mkForallFVars (xs.push h) concl
          addDecl <| .thmDecl {
            name := thmName, levelParams := [], type := type, value := value }

end FvKit.SpecConj

end FvKitSpecConj

/-! # `abort_peel` — the abort-chain peel, automated

`abort_peel` closes goals of the shape

    <f>.aborts <args> = Abort.AbortResult.NoAbort

(and the same for any `.aborts.cont_*` helper) by walking the generated
abort tree one definition level at a time.  It is the mechanised form of
the hand-written template that closed ember's `create_multi` family.

The loop, at every step, looks at the goal's left-hand side and picks ONE
action:

1. `delta`      — unfold exactly one `.aborts`-family definition, delivered
                  as a `rw`-style `Eq.mpr (congrArg motive h)` step built
                  from the definition's `eq_def` equation.
2. `guard`      — an exposed `ite`: prove the condition (or its negation)
                  in a *small side goal* and rewrite the whole `ite` away
                  with `if_pos` / `if_neg`.  The side goal never contains
                  the megaterm, so any tactic is safe there.
3. `structural` — beta / zeta / iota / structure-eta.  Delivered by
                  `simp only []` (no lemmas), which is definitional but
                  only ever asks the kernel for a structural traversal.
4. `splitOn`    — a `match` on an irreducible callee `.aborts` call that a
                  `using` fact (or a context hypothesis) can discharge:
                  `split`, then close the abort branch by *unifying* the
                  fact's conclusion against the goal's own subterm.

## The kernel discipline this encodes

At heavy instantiations the only kernel-safe operation is syntactic
unification.  Two rules follow, and the tactic obeys both:

* Definition unfolding goes through `rw [<def>.eq_def]`, i.e.
  `Eq.mpr (congrArg motive h)`, where `h` is a constant application whose
  type is instantiated by substitution and whose motive is matched
  syntactically.  It never goes through a `simp only` whose rewrite step
  is definitional (`Simp.Result.proof? = none`), which would make the
  kernel re-derive `oldGoal =?= newGoal` with no elaborator cache.
* The terminal close never *rewrites* at a megaterm.  Every argument of a
  `using` fact is a unification hole, read off the goal by `isDefEq`, so
  the proof term is `heq.symm.trans (fact <args-from-the-goal>)` and the
  kernel only ever checks an application.

Structural steps (`simp only []`) stay definitional on purpose: the
kernel re-check there is one traversal of the expanded term, not the
reduction of a function over it.

## Usage

    abort_peel
    abort_peel using [no_abort_lemma, bridge₁, bridge₂]

Facts listed in `using` are tried, conclusion-first, at irreducible
sub-abort calls; their leftover hypotheses are discharged from the
context, by `rfl`, or recursively by another listed fact.  Local
hypotheses are used the same way without being listed.

The walk is bounded (`maxPeelSteps` actions); anything it cannot reduce
is left as a residual goal.
-/

namespace Prover.AbortPeel

open Lean Elab Tactic Meta

/-- Total number of peel actions one `abort_peel` invocation may take.
Roughly 64 levels x 8 actions per level. -/
def maxPeelSteps : Nat := 512

/-- Depth of the `using`-fact search used to discharge a fact's own
hypotheses. -/
def maxFactDepth : Nat := 3

private inductive Act where
  | structural
  | guard (cond : Expr)
  | delta (name : Name)
  | splitOn (scrut : Expr)

private def isAbortsName (n : Name) : Bool :=
  n.components.any (fun c => c == `aborts)

private def abortsDef? (e : Expr) : MetaM (Option Name) := do
  let .const c _ := e.getAppFn | return none
  unless isAbortsName c do return none
  match (← getEnv).find? c with
  | some (.defnInfo _) => return some c
  | _ => return none

private def isCtorApp (e : Expr) : MetaM Bool := do
  let .const c _ := e.getAppFn | return false
  match (← getEnv).find? c with
  | some (.ctorInfo _) => return true
  | _ => return false

/-- A discriminant whose type is a single-constructor, index-free inductive:
the matcher over it reduces by structure eta, which is what turns a
generated `let (a, b, c) := e` into projections of `e`. -/
private def isStructDiscr (d : Expr) : MetaM Bool := do
  let .const tc _ := (← whnf (← inferType d)).getAppFn | return false
  match (← getEnv).find? tc with
  | some (.inductInfo iv) =>
    return iv.ctors.length == 1 && iv.numIndices == 0 && !iv.isRec
  | _ => return false

private def conclusionOf : Expr → Expr
  | .forallE _ _ b _ => conclusionOf b
  | e => e

/-- A usable fact: the proof, abstracted over its own metavariables so a
fresh instance can be opened at every use site, plus the head constant of
its conclusion's left-hand side (a cheap pre-filter). -/
private structure Fact where
  abs : AbstractMVarsResult
  head : Option Name

private def mkFact (e : Expr) : MetaM Fact := do
  let concl := conclusionOf (← instantiateMVars (← inferType e))
  let head := match concl.eq? with
    | some (_, lhs, _) => lhs.getAppFn.constName?
    | none => none
  return { abs := ← abstractMVars e, head }

/-- Cheap syntactic probe: does one of `facts` conclude an equation whose
left-hand side has the same head constant as `d`?  Used to decide whether
an irreducible `.aborts` call should be split-and-discharged rather than
unfolded. -/
private def factCovers (facts : Array Fact) (d : Expr) : MetaM Bool := do
  let some dh := d.getAppFn.constName? | return false
  return facts.any (fun f => f.head == some dh)

private partial def findAct (facts : Array Fact) (e : Expr) :
    MetaM (Option Act) := do
  match e with
  | .mdata _ b => findAct facts b
  | .letE .. => return some .structural
  | _ =>
    let fn := e.getAppFn
    if fn.isLambda then return some .structural
    let .const c _ := fn | return none
    let args := e.getAppArgs
    if c == ``ite && args.size ≥ 5 then
      return some (.guard args[1]!)
    if let some mapp ← matchMatcherApp? e then
      for d in mapp.discrs do
        if ← isCtorApp d then return some .structural
      for d in mapp.discrs do
        if ← factCovers facts d then return some (.splitOn e)
      for d in mapp.discrs do
        if let some a ← findAct facts d then return some a
      for d in mapp.discrs do
        if ← isStructDiscr d then return some .structural
      if 0 < mapp.discrs.size then
        return some (.splitOn e)
      return none
    if let some n ← abortsDef? e then return some (.delta n)
    return none

private partial def collectAbortsConsts : Expr → NameSet → NameSet
  | .app f a, acc => collectAbortsConsts a (collectAbortsConsts f acc)
  | .lam _ t b _, acc => collectAbortsConsts b (collectAbortsConsts t acc)
  | .forallE _ t b _, acc => collectAbortsConsts b (collectAbortsConsts t acc)
  | .letE _ t v b _, acc =>
    collectAbortsConsts b (collectAbortsConsts v (collectAbortsConsts t acc))
  | .mdata _ b, acc => collectAbortsConsts b acc
  | .proj _ _ b, acc => collectAbortsConsts b acc
  | .const n _, acc => if isAbortsName n then acc.insert n else acc
  | _, acc => acc

/-- Every hypothesis of the current context that states a proposition. -/
private def localFacts : MetaM (Array Fact) := do
  let mut out : Array Fact := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← isProp decl.type then out := out.push (← mkFact decl.toExpr)
  return out

private def runOn (g : MVarId) (tac : TSyntax `tactic) :
    TacticM (Option (List MVarId)) := do
  let s ← saveState
  try
    let gs ← Lean.Elab.Tactic.run g (evalTactic tac)
    return some gs
  catch _ =>
    s.restore
    return none

private def proveByTac (ty : Expr) (tac : TSyntax `tactic) :
    TacticM (Option Expr) := do
  let s ← saveState
  try
    let mv ← mkFreshExprSyntheticOpaqueMVar ty
    -- `Tactic.run` saves and RESTORES `pendingMVars`, so synthetic
    -- metavariables the side-goal tactic creates (instance arguments inside a
    -- `simp`/`decide` proof, discharge subgoals) are dropped unsynthesized and
    -- the returned proof still mentions them.  `withSynthesize` closes them
    -- before we look; without it every guard that needs more than
    -- `assumption`/`decide` silently fails.
    let gs ← Term.withSynthesize (postpone := .no) do
      Lean.Elab.Tactic.run mv.mvarId! (evalTactic tac)
    if gs.isEmpty then
      let r ← instantiateMVars mv
      if r.hasExprMVar || r.hasSorry then
        s.restore
        return none
      return some r
    else
      s.restore
      return none
  catch _ =>
    s.restore
    return none

private abbrev SimpArg :=
  TSyntax [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma]

private def simpArgsOf (args : Array Term) (star : Bool) :
    MetaM (Array SimpArg) := do
  let mut out : Array SimpArg := #[]
  for t in args do
    out := out.push ⟨(← `(Lean.Parser.Tactic.simpLemma| $t:term)).raw⟩
  if star then
    out := out.push ⟨(← `(Lean.Parser.Tactic.simpStar| *)).raw⟩
  return out

/-- `simp_all` accepts no `*`, so its argument list has a narrower type than
`simp`'s. -/
private def simpAllArgsOf (args : Array Term) :
    MetaM (Array (TSyntax
      [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma])) := do
  let mut out : Array (TSyntax
    [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma]) := #[]
  for t in args do
    out := out.push ⟨(← `(Lean.Parser.Tactic.simpLemma| $t:term)).raw⟩
  return out

/-- The side-goal tactic used to decide an exposed `ite` condition.  The
condition is always small (it mentions the continuation's own parameters,
never the world/vault megaterm), so a full `simp` is safe here. -/
private def guardTactic (args : Array Term) : MetaM (TSyntax `tactic) := do
  let plain ← simpArgsOf args false
  let starred ← simpArgsOf args true
  let allArgs ← simpAllArgsOf args
  `(tactic|
    first
      | assumption
      | decide
      | (simp only [$[$plain],*] ; done)
      | (simp only [$[$starred],*] ; done)
      | (simp [$[$starred],*] ; done)
      -- last resort for the "decide-form massaging" case: the guard and the
      -- hypothesis that decides it were normalised differently (the spec's
      -- `asserts` was `simp`ed on the way in, the generated guard was not), so
      -- both sides have to be renormalised together before `assumption` bites.
      | (simp_all [$[$allArgs],*] ; done)
      | (simp_all ; done)
      -- The generated guard is a `BoundedNat` comparison returning `Bool`
      -- (`BoundedNat.le a b = true`); the hypothesis that decides it comes out
      -- of the spec's `asserts` already normalised to the `Nat` level
      -- (`a.val <= b.val`).  Normalise the guard the same way, then let `omega`
      -- close the arithmetic against the context.  This pair is the single
      -- most common guard shape in the corpus.
      | (simp only [$[$starred],*] <;> omega)
      | (simp [$[$starred],*] <;> omega)
      | (simp_all [$[$allArgs],*] <;> omega)
      | omega
      | rfl)

/-- Build `if_pos h` / `if_neg h` as a rewrite rule, leaving the branches
as metavariables so the rewrite is matched syntactically against whatever
`ite` carries this condition. -/
private def mkIteEq (pos : Bool) (pfTy : Expr) (pf : Expr) : MetaM (Option Expr) := do
  let lem ← mkConstWithFreshMVarLevels (if pos then ``if_pos else ``if_neg)
  let (mvs, bis, _) ← forallMetaTelescope (← inferType lem)
  -- `pfTy` is the condition AS IT APPEARS IN THE GOAL, not `inferType pf`:
  -- a side-goal proof produced by `simp` reports its type in simp-normal form
  -- (`Nat.ble a.val b.val = true` rather than `BoundedNat.le a b = true`), and
  -- instantiating `if_pos`'s `c` with that makes the rewrite pattern
  -- syntactically different from the `ite` in the goal, so `kabstract` finds
  -- no occurrence and the rewrite fails.
  for i in [0:mvs.size] do
    if bis[i]! == BinderInfo.default then
      let m := mvs[i]!
      if ← isDefEq (← inferType m) pfTy then
        m.mvarId!.assign pf
        return some (mkAppN lem mvs)
      else
        return none
  return none

private def rewriteWith (g : MVarId) (eqPf : Expr) :
    TacticM (Option (List MVarId)) := do
  let s ← saveState
  try
    let r ← g.rewrite (← g.getType) eqPf
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    return some (g' :: r.mvarIds)
  catch _ =>
    s.restore
    return none

mutual

/-- Instantiate `f`'s conclusion against `target` by unification only, then
discharge whatever hypotheses `f` still has.  Every argument of `f` is a
hole read off the goal, so nothing is ever rewritten at a megaterm. -/
private partial def tryFactOne (facts : Array Fact) (depth : Nat) (fact : Fact)
    (target : Expr) : TacticM (Option Expr) := do
  let s ← saveState
  try
    let (_, _, f) ← openAbstractMVarsResult fact.abs
    let (mvs, bis, concl) ← forallMetaTelescope (← inferType f)
    unless ← isDefEq concl target do
      s.restore
      return none
    for i in [0:mvs.size] do
      let m := mvs[i]!.mvarId!
      if ← m.isAssigned then continue
      if bis[i]! == BinderInfo.instImplicit then
        match ← trySynthInstance (← m.getType) with
        | .some inst => m.assign inst
        | _ => s.restore; return none
      else
        unless ← dischargeMVar facts depth m do
          s.restore
          return none
    let pf ← instantiateMVars (mkAppN f mvs)
    if pf.hasExprMVar then
      s.restore
      return none
    return some pf
  catch _ =>
    s.restore
    return none

private partial def tryFact (facts : Array Fact) (depth : Nat)
    (target : Expr) : TacticM (Option Expr) := do
  for f in facts do
    if let some pf ← tryFactOne facts depth f target then return some pf
  return none

/-- Discharge one leftover hypothesis of an applied `using` fact:
from the context, by `rfl`, or recursively by another fact. -/
private partial def dischargeMVar (facts : Array Fact) (depth : Nat)
    (m : MVarId) : TacticM Bool := m.withContext do
  if ← m.isAssigned then return true
  if (← instantiateMVars (← m.getType)).hasExprMVar then return false
  -- 1. straight from the context
  try
    m.assumption
    return true
  catch _ => pure ()
  -- 2. another listed fact (this is what discharges the freshness holes)
  if depth > 0 then
    if let some pf ← tryFact facts (depth - 1) (← m.getType) then
      m.assign pf
      return true
  -- 3. reflexivity (projection-of-constructor hops)
  try
    m.refl
    return true
  catch _ => pure ()
  return false

end

/-- The abort branch produced by `split`: the goal is `Aborted _ = NoAbort`
and the context carries `heq : <call> = Aborted _`.  Chase `heq.symm.trans
(fact ...)` — the fact's arguments are unified off `heq`, never rebuilt. -/
private def closeDead (facts : Array Fact) (g : MVarId) : TacticM Bool :=
  g.withContext do
    let goalTy ← instantiateMVars (← g.getType)
    let some (_, _, rhs) := goalTy.eq? | return false
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let some (_, s, r) := (← instantiateMVars decl.type).eq? | continue
      unless ← isCtorApp r do continue
      if s.getAppFn.isConst == false then continue
      let target ← mkEq s rhs
      let some pf ← tryFact facts maxFactDepth target | continue
      let full ← mkEqTrans (← mkEqSymm decl.toExpr) pf
      if ← isDefEq goalTy (← inferType full) then
        g.assign full
        return true
      let ne? ← proveByTac (mkApp (mkConst ``Not) (← inferType full))
        (← `(tactic| first | (simp ; done) | decide))
      if let some ne := ne? then
        g.assign (← mkAppOptM ``absurd #[none, some goalTy, some full, some ne])
        return true
    return false

private structure PeelCtx where
  facts : Array Fact
  simpArgs : Array Term
  budget : IO.Ref Nat
  acted : IO.Ref Nat

private def deltaStep (g : MVarId) (n : Name) :
    TacticM (Option (List MVarId)) := do
  -- Preferred delivery: `rw [n.eq_def]`, i.e. Eq.mpr/congrArg, matched
  -- syntactically and checked by the kernel without redoing any defeq.
  let eqn? ← try getUnfoldEqnFor? n (nonRec := true) catch _ => pure none
  if let some eqn := eqn? then
    if let some gs ← rewriteWith g (← mkConstWithFreshMVarLevels eqn) then
      return some gs
  -- Fallbacks, in decreasing order of kernel friendliness.  All of these
  -- address the name by `Name`, not by generated syntax, so they cannot be
  -- defeated by identifier resolution in the caller's namespace.
  let s1 ← saveState
  try
    return some [← Meta.unfoldTarget g n]
  catch _ => s1.restore
  let s2 ← saveState
  try
    return some [← g.deltaTarget (fun c => c == n)]
  catch _ => s2.restore
  let one ← simpArgsOf #[(mkIdent n : Term)] false
  runOn g (← `(tactic| simp only [$[$one],*]))

private def guardStep (ctx : PeelCtx) (g : MVarId) (cond : Expr) :
    TacticM (Option (List MVarId)) := g.withContext do
  let extra := (collectAbortsConsts cond {}).toList.toArray.map
    fun n => (mkIdent n : Term)
  let tac ← guardTactic (ctx.simpArgs ++ extra)
  for (ty, pos) in
      #[(cond, true), (mkApp (mkConst ``Not) cond, false)] do
    if let some pf ← proveByTac ty tac then
      if let some eq ← mkIteEq pos ty pf then
        if let some gs ← rewriteWith g eq then
          return some gs
  return none

/-- `Expr.eq?` is purely syntactic, but a target that has been through
`rcases` / `cases` is typically a beta-redex of the motive
(`(fun _ => lhs = rhs) h`), and `mdata` survives several tactics.  Normalise
the target so the analyser sees the equation.  Beta and mdata-stripping are
the cheapest possible definitional steps. -/
private def normalizeTarget (g : MVarId) : TacticM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  if ty.eq?.isSome then return g
  let mut ty' := ty.consumeMData.headBeta
  if ty'.eq?.isNone then
    ty' := (← whnfR ty')
  if ty'.eq?.isNone || ty' == ty then return g
  try g.replaceTargetDefEq ty' catch _ => return g

private partial def peelGoal (ctx : PeelCtx) (g0 : MVarId) :
    TacticM (List MVarId) := do
  if ← g0.isAssigned then return []
  if (← ctx.budget.get) == 0 then return [g0]
  let g ← normalizeTarget g0
  let goalTy ← g.withContext do instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := goalTy.eq? | return [g]
  if lhs == rhs then
    ctx.acted.modify (· + 1)
    g.refl
    return []
  let facts ← g.withContext do
    return ctx.facts ++ (← localFacts)
  -- terminal: the goal itself is exactly a listed/known fact
  if ← g.withContext do factCovers facts lhs then
    if let some pf ← g.withContext do tryFact facts maxFactDepth goalTy then
      ctx.acted.modify (· + 1)
      g.assign pf
      return []
  -- dead branch: `Aborted _ = NoAbort` under a contradictory `split` fact
  if (← g.withContext do isCtorApp lhs) && (← g.withContext do isCtorApp rhs)
      && lhs.getAppFn != rhs.getAppFn then
    if ← closeDead facts g then
      ctx.acted.modify (· + 1)
      return []
    return [g]
  let act? ← g.withContext do findAct facts lhs
  let some act := act? | return [g]
  ctx.budget.modify (fun n => n - 1)
  let saved ← saveState
  let gs? ← (do
    match act with
    | .structural =>
      -- The ONE definitional step in the walk, and deliberately the weakest
      -- one available: no lemmas at all, so only beta / zeta / iota /
      -- projection / structure-eta can fire.  The kernel re-check for those
      -- is a single structural traversal of the expanded term, never the
      -- reduction of a function over it.
      runOn g (← `(tactic| first | simp only [] | dsimp only []))
    | .delta n => deltaStep g n
    | .guard cond =>
      match ← guardStep ctx g cond with
      | some gs => pure (some gs)
      | none =>
        -- the condition itself may hide a reducible `.aborts` call
        match ← g.withContext do findAct facts cond with
        | some (.delta n) => deltaStep g n
        | _ => pure none
    | .splitOn m =>
      -- Targeted: `Split.splitMatch` takes the exact matcher application, so
      -- the walk never splits an unrelated `match` that happens to sit
      -- earlier in the term than the residual sub-abort call.
      let direct ← (do
        let s ← saveState
        try
          return some (← Split.splitMatch g m)
        catch _ =>
          s.restore
          return none)
      match direct with
      | some gs => pure (some gs)
      | none => runOn g (← `(tactic| split)))
  let some gs := gs? | return [g]
  -- reject no-op steps so the walk always terminates; roll the goal back so
  -- the caller gets an unassigned residual rather than a half-applied one
  if gs.length == 1 then
    let g' := gs[0]!
    if (← g'.withContext do instantiateMVars (← g'.getType)) == goalTy then
      saved.restore
      return [g]
  ctx.acted.modify (· + 1)
  let mut out : List MVarId := []
  for g' in gs do
    out := out ++ (← peelGoal ctx g')
  return out

/-- A one-line description of where the walk stopped: enough to steer the
next `using` fact without printing a megaterm goal. -/
private def residualDesc (g : MVarId) : MetaM MessageData := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := ty.eq? | return m!"goal is not an equation"
  let head : MessageData :=
    match lhs.getAppFn with
    | .const n _ => m!"{n}"
    | .fvar _ => m!"<fvar>"
    | .lam .. => m!"<lambda>"
    | _ => m!"<{lhs.ctorName}>"
  match ← matchMatcherApp? lhs with
  | some mapp =>
    let discrHeads := mapp.discrs.map fun d =>
      match d.getAppFn with
      | .const n _ => m!"{n}"
      | _ => m!"<{d.ctorName}>"
    return m!"stuck at match {head} on {discrHeads.toList}"
  | none =>
    -- an unresolved guard is the common residual; the condition is small by
    -- construction (it mentions the continuation's own parameters), so naming
    -- it is what tells the caller which fact is missing from `using`
    if lhs.isAppOfArity ``ite 5 then
      return m!"stuck at an `ite`, unresolved condition: {lhs.getAppArgs[1]!}"
    return m!"stuck at {head}"

/-- Why the walk could not start: which action the analyser picked and, for a
`delta`, whether the definition has an unfolding equation and what the rewrite
said.  Names only -- never prints a goal, which at these instantiations is a
megaterm. -/
private def diagnose (facts : Array Fact) (g0 : MVarId) : TacticM MessageData := do
  let g ← normalizeTarget g0
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let tyHead : MessageData :=
      match ty.getAppFn with
      | .const n _ => m!"{n}"
      | e => m!"<{e.ctorName}>"
    let some (_, lhs, _) := ty.eq? |
      return m!"goal is not an equation: a {ty.ctorName} headed by {tyHead}"
    let headName : MessageData :=
      match lhs.getAppFn with
      | .const n _ => m!"{n}"
      | e => m!"<{e.ctorName}>"
    match ← liftM (findAct facts lhs) with
    | none => return m!"lhs headed by {headName}: no action applies"
    | some .structural => return m!"chose structural on {headName}"
    | some (.guard _) => return m!"chose guard under {headName}"
    | some (.splitOn _) => return m!"chose split under {headName}"
    | some (.delta n) =>
      let eqn? ← try liftM (getUnfoldEqnFor? n (nonRec := true)) catch _ => pure none
      match eqn? with
      | none => return m!"chose delta {n}: no unfolding equation"
      | some eqn =>
        let msg ← try
          let e ← liftM (mkConstWithFreshMVarLevels eqn)
          match ← rewriteWith g e with
          | some _ => pure m!"rewrite succeeded (so the failure is elsewhere)"
          | none => pure m!"rewrite returned none"
        catch ex => pure m!"rewrite threw: {ex.toMessageData}"
        return m!"chose delta {n} via {eqn}: {msg}"

def abortPeelCore (facts0 : Array Expr) (simpArgs : Array Term) :
    TacticM Unit := do
  let budget ← IO.mkRef maxPeelSteps
  let acted ← IO.mkRef 0
  let mut facts : Array Fact := #[]
  for e in facts0 do
    facts := facts.push (← liftM (mkFact e))
  let ctx : PeelCtx := { facts, simpArgs, budget, acted }
  let gs ← getGoals
  let mut out : List MVarId := []
  for g in gs do
    out := out ++ (← peelGoal ctx g)
  if (← acted.get) == 0 then
    let mut why : MessageData := m!"(no goal)"
    for g in gs do
      why ← diagnose (ctx.facts ++ (← g.withContext do liftM localFacts)) g
      break
    throwError "abort_peel: no peel action applies to this goal -- {why}"
  if !out.isEmpty then
    let mut descs : List MessageData := []
    for g in out do
      descs := descs ++ [← liftM (residualDesc g)]
    let used := maxPeelSteps - (← budget.get)
    logInfo m!"abort_peel: {← acted.get} actions, {used} budget used, {out.length} residual goal(s): {MessageData.joinSep descs (MessageData.ofFormat "; ")}"
  replaceMainGoal out

end Prover.AbortPeel

open Lean Elab Tactic Meta in
/-- Peel a `<f>.aborts <args> = NoAbort` goal one definition level at a
time.  See `Prover.AbortPeel`. -/
elab "abort_peel" : tactic =>
  Prover.AbortPeel.abortPeelCore #[] #[]

open Lean Elab Tactic Meta in
/-- `abort_peel using [h₁, h₂, …]` — same walk, but the listed facts are
used (conclusion-first, arguments as unification holes) to discharge
irreducible sub-abort calls and each other's side conditions. -/
elab "abort_peel" " using" " [" ts:term,* "]" : tactic =>
  -- `withMainContext` matters: the listed facts are usually a mix of global
  -- lemmas and LOCAL hypotheses (`h_inner`, a `have` from earlier in the same
  -- proof), and without the goal's local context the latter do not resolve.
  withMainContext do
    let stxs : Array Term := ts.getElems
    let mut exprs : Array Expr := #[]
    for t in stxs do
      exprs := exprs.push (← elabTerm t none)
    Prover.AbortPeel.abortPeelCore exprs stxs
