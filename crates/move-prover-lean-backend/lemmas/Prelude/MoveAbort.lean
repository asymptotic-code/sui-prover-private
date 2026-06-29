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
