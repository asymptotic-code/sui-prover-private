-- Native implementations for prover::prover module
-- These are specification-only functions that model abstract verification concepts

import Prelude.BoundedNat
import Prelude.MoveAbort

namespace Prover

-- Type invariant: always holds
-- In Lean's type system, type safety is guaranteed, so this is always satisfied
@[reducible] def type_inv (α : Type) (_x : α) : Prop := True
instance (α : Type) (x : α) : Decidable (type_inv α x) := inferInstanceAs (Decidable True)

-- Drop: no-op that returns Unit
-- Lean has automatic memory management, explicit drop is unnecessary
def drop (α : Type) (_x : α) : Unit := ()
-- `fresh` is a spec-mode marker that the IR pipeline extracts before
-- rendering. Reaching it at runtime indicates a translation bug, so
-- emit the parseable abort marker instead of `sorry` (which would
-- crash the Lean executable with `INTERNAL PANIC: executed 'sorry'`).
def fresh (α : Type) [Inhabited α] : α :=
  MoveAbort.raiseAbortNoModule 0 MoveAbort.AbortSource.userAssert
def val (α : Type) (x : α) : α := x

-- Ref: creates a reference (identity in Lean since references aren't distinguished at this level)
def ref (α : Type) (x : α) : α := x

-- Specification directives: no-ops that return Unit
-- These are used only during verification and have no runtime effect.
-- Param type is Bool (matching the Move source `requires(p: bool)` etc.)
-- so generated bodies that pass a Bool-typed condition type-check. The
-- spec-extraction pass strips these calls in Spec mode before rendering;
-- in Test mode they remain inline as no-ops.
def requires (_p : Bool) : Unit := ()
def ensures (_p : Bool) : Unit := ()
def asserts (_p : Bool) : Unit := ()
def invariant_begin : Unit := ()
def invariant_end : Unit := ()

-- Logical implication on Bool. Unlike requires/ensures/asserts (erased
-- spec directives that return Unit), `implies` appears in predicate
-- position inside spec conditions (e.g. `implies(is_empty, eq) && ...`),
-- so it must reduce to a real Bool: `p -> q` is `!p || q`.
def implies (p q : Bool) : Bool := !p || q

-- Ignored-abort channel query: in the prover, `asserts_of(b"name")` names
-- the Boogie variable that holds "the ignore_abort call to <name> did not
-- abort", and `asserts(asserts_of(b"name"))` folds the callee's abort
-- condition into the caller's asserts conjunction (see sui-prover's
-- ignore_aborts_by_function.ok.move). This Lean model has no ignore_abort
-- machinery -- callee aborts always flow through the caller's `.aborts`
-- chain -- so the channel is vacuously clean and the faithful constant is
-- `true`. The previous `false` stub flipped the polarity: it made every
-- asserts conjunction containing it identically false, turning the
-- generated `<fn>_asserts_correct` iff into "the caller always aborts",
-- a false statement. `true` is sound here: it can only STRENGTHEN the
-- obligation (the callee's aborts still count against `.aborts`, they are
-- just no longer excused by the asserts side), never weaken it.
def asserts_of (_name : List (BoundedNat (2^8))) : Bool := true

-- Boogie VC-shaping directives: no-ops that influence solver hints in
-- the prover backend. Lean has no equivalent; treat them as Unit.
def boogie_split_here : Unit := ()
def boogie_focus : Unit := ()
def boogie_allow_path_isolation : Unit := ()

def begin_forall_lambda (α : Type) [Inhabited α] : α :=
  MoveAbort.raiseAbortNoModule 0 MoveAbort.AbortSource.userAssert
@[reducible] def end_forall_lambda : Prop := True
instance : Decidable end_forall_lambda := inferInstanceAs (Decidable True)
def begin_exists_lambda (α : Type) [Inhabited α] : α :=
  MoveAbort.raiseAbortNoModule 0 MoveAbort.AbortSource.userAssert
@[reducible] def end_exists_lambda : Prop := False
instance : Decidable end_exists_lambda := inferInstanceAs (Decidable False)

end Prover
