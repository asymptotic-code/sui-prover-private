-- Native implementations for prover::prover module
-- These are specification-only functions that model abstract verification concepts

import Prelude.BoundedNat
import Prelude.MoveAbort
import Prelude.MoveType

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

-- Named-assertion lookup: in the prover, `asserts_of(b"name")` queries
-- whether a previously-declared assertion fired. With no assertion
-- machinery here we under-approximate to `false` (no assertion fired);
-- this is sound for abort detection because callers only branch on it
-- to short-circuit further checks.
def asserts_of (_name : List (BoundedNat (2^8))) : Bool := false

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
