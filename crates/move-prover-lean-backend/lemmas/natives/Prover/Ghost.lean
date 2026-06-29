-- Native implementations for prover::ghost module (deep embedding).
--
-- Note: a previous version imported `Prover.ProverNatives`, but that
-- module has been disambiguated to `Prover.ProverPkgNatives` whenever
-- the `prover` module lives inside the `Prover` package (which is
-- always, in practice). Nothing in this file actually references that
-- module's contents, so the import is dropped to keep `lake build`
-- green for downstream consumers.

import Prelude.MoveAbort
import Prelude.MoveType

set_option linter.unusedVariables false

namespace Ghost

-- Global ghost state accessor — reaching this at runtime indicates a
-- translation bug (spec-only ghost reads should be extracted by the
-- pipeline). Emit the parseable abort marker rather than `sorry` so
-- the test driver can convert it into a structured verdict instead of
-- crashing the Lean executable.
def global (T : Type) (U : Type) [Inhabited U] : U :=
  MoveAbort.raiseAbortNoModule 0 MoveAbort.AbortSource.userAssert

-- Set ghost state - no-op since we're not tracking state
def set (T : Type) (U : Type) (x : U) : Unit := ()

-- Borrow mutable ghost state — see `global`.
def borrow_mut (T : Type) (U : Type) [Inhabited U] : U :=
  MoveAbort.raiseAbortNoModule 0 MoveAbort.AbortSource.userAssert

-- Declare global ghost variable - no-op
def declare_global (T : Type) (U : Type) : Unit := ()

-- Declare mutable global ghost variable - no-op
def declare_global_mut (T : Type) (U : Type) : Unit := ()

-- Havoc global state - no-op
def havoc_global (T : Type) (U : Type) : Unit := ()

end Ghost
