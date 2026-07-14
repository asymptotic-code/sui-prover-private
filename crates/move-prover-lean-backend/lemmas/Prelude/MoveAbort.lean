-- Copyright (c) Asymptotic Labs
-- SPDX-License-Identifier: Apache-2.0
--
-- MoveAbort: a runtime-evaluable representation of Move aborts.
--
-- The Spec render face emits `sorry` for `IRNode::Abort`, which inhabits any
-- type but cannot be evaluated. The Test render face (`--test`) emits each
-- function's `.aborts` companion as `Option MoveAbort` instead of `Bool`.
-- A test passes if its `.aborts` is `none` and aborts (with code/source)
-- when it's `some _`. The driver harness inspects the verdict and compares
-- to the Move VM.

inductive MoveAbort.AbortSource where
  | userAssert
  | arithmetic
  deriving BEq, Repr, Inhabited

structure MoveAbort where
  source : MoveAbort.AbortSource
  code   : Nat
  -- Move `<package>::<module>` name where the abort originated. Empty
  -- string means "no module recorded" — natives and historical literal
  -- emitters use it to stay backward-compatible. The per-test driver
  -- defaults to the test module when this field is empty.
  module : String := ""
  deriving BEq, Repr, Inhabited

def MoveAbort.AbortSource.toString : MoveAbort.AbortSource → String
  | .userAssert => "userAssert"
  | .arithmetic => "arithmetic"

instance : ToString MoveAbort.AbortSource where
  toString := MoveAbort.AbortSource.toString

-- Test-mode emergency abort. Used when an `IRNode::Abort` (Move `abort`
-- statement) appears in a non-`.aborts` body that gets evaluated by the
-- test driver. Returns `default : α` so the call-site type-checks for
-- any return type, while panicking with a parseable line on stderr
-- (`__MOVE_ABORT__:<code>:<source>:<module>`) that the per-test driver
-- scans for to turn the panic into a structured abort verdict rather
-- than crashing the Lean executable with `INTERNAL PANIC: executed
-- 'sorry'`. The `module` argument is the Move `<package>::<module>`
-- name of the function containing the `abort`, so the harness can
-- report abort origin correctly to `#[expected_failure(abort_code=N,
-- location=<module>)]` Move test annotations.
--
-- `Inhabited α` lets it stand in for any return type the impl body
-- might have.
def MoveAbort.raiseAbort {α : Type _} [Inhabited α] (code : Nat) (source : MoveAbort.AbortSource) (module : String) : α :=
  let msg := "__MOVE_ABORT__:" ++ toString code ++ ":" ++ source.toString ++ ":" ++ module
  @panic α _ msg

-- Backward-compatible no-module overload. Used by callers (e.g.
-- hand-written natives) that don't have a Move module name to attach.
def MoveAbort.raiseAbortNoModule {α : Type _} [Inhabited α] (code : Nat) (source : MoveAbort.AbortSource) : α :=
  MoveAbort.raiseAbort code source ""

-- Abort-chain combinator. A function's `.aborts` body is a fold of these: it
-- evaluates the abort checks in Move execution order and returns the FIRST one
-- that fires, else `none`. The backend renders the `.aborts` spine with this in
-- place of the nested `match scrut with | some __abort => some __abort | none =>
-- rest` encoding, so that an `aborts = none` goal decomposes STRUCTURALLY (via
-- `orElse_eq_none_iff`) into one small goal per abort check — without the kernel
-- having to reduce the whole nested body (the term-size blow-up documented in
-- the "Kernel deep-recursion" note). It is definitionally the same `match`, so
-- consumers that need the value see through it unchanged.
@[reducible] def MoveAbort.orElse (a b : Option MoveAbort) : Option MoveAbort :=
  match a with
  | Option.some x => Option.some x
  | Option.none => b

-- Structural decomposition: the chain aborts-nowhere iff every check does. The
-- proof only `cases`-splits the head `Option`, never the heavy guard bodies, so
-- `simp only [orElse_eq_none_iff]` peels the whole spine into a conjunction of
-- per-check `= none` goals cheaply.
@[simp] theorem MoveAbort.orElse_eq_none_iff (a b : Option MoveAbort) :
    MoveAbort.orElse a b = Option.none ↔ a = Option.none ∧ b = Option.none := by
  cases a <;> simp [MoveAbort.orElse]

-- A discharged (`none`) check is absorbed on the left, so fully-reduced
-- `orElse` trees collapse to their tail (and all-`none` trees to `none`).
@[simp] theorem MoveAbort.orElse_none_left (b : Option MoveAbort) :
    MoveAbort.orElse Option.none b = b := rfl

/-! Structural recomposition combinators for generated `.aborts` obligation
bundles (see `aborts_obligations.rs`): the generator emits a bundle theorem
`<fn>.aborts_none_of` whose proof is a direct term built from these, one
application per body node — no tactics, no simp, checked linearly. -/

theorem MoveAbort.orElse_none_of {a b : Option MoveAbort}
    (ha : a = Option.none) (hb : b = Option.none) :
    MoveAbort.orElse a b = Option.none := by
  subst ha; exact hb

/-- Boolean-guarded abort check: the guard is false and the fall-through is
`none`. -/
theorem MoveAbort.bite_none_of_false {c : Bool} {x y : Option MoveAbort}
    (hc : c = false) (hy : y = Option.none) :
    (if c then x else y) = Option.none := by
  subst hc; simpa

/-- Boolean-guarded abort check with the polarity flipped (abort on the else
side). -/
theorem MoveAbort.bite_none_of_true {c : Bool} {x y : Option MoveAbort}
    (hc : c = true) (hx : x = Option.none) :
    (if c then x else y) = Option.none := by
  subst hc; simpa

/-- Real branch: both arms discharged under their guard fact. -/
theorem MoveAbort.bite_none_split {c : Bool} {x y : Option MoveAbort}
    (ht : c = true → x = Option.none) (he : c = false → y = Option.none) :
    (if c then x else y) = Option.none := by
  cases c
  · exact he rfl
  · exact ht rfl

/-- Dependent branch (`if h : p then ... else ...`): both arms discharged with
the branch hypothesis in scope. -/
theorem MoveAbort.dite_none_split {p : Prop} [inst : Decidable p]
    {x : p → Option MoveAbort} {y : ¬p → Option MoveAbort}
    (ht : ∀ h : p, x h = Option.none) (he : ∀ h : ¬p, y h = Option.none) :
    dite p x y = Option.none := by
  by_cases h : p
  · simpa [h] using ht h
  · simpa [h] using he h

/-- Dependent branch over a Bool guard (`if h : c = true then … else …`, the
loop-entry rendering): both arms discharged from Bool-polarity facts — the
else arm's `¬(c = true)` argument is rebuilt from `c = false` (aligned by
proof irrelevance). -/
theorem MoveAbort.bdite_none_split {c : Bool} {x : c = true → Option MoveAbort}
    {y : ¬c = true → Option MoveAbort}
    (ht : ∀ h : c = true, x h = Option.none)
    (he : ∀ h : c = false, y (by simp [h]) = Option.none) :
    dite (c = true) x y = Option.none := by
  cases c
  · simpa using he rfl
  · simpa using ht rfl
