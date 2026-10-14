-- Native implementations for std::vector
-- These provide the short-named functions called by generated code

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.MoveAbort
import Prelude.MoveType
import Prelude.ProgramState

namespace MoveVector

-- Core vector operations using Lean's List type
-- Move vectors are represented as List in Lean
--
-- After mutable threading: functions that took Mutable (List tv0) s
-- now take List tv0 directly and return the updated list alongside
-- any original return value.

def empty (tv0 : Type) [BEq tv0] [Inhabited tv0] : List tv0 :=
  []

-- KNOWN INCONSISTENT as stated (models the Move VM u64-length invariant);
-- pending the vector-subtype overhaul (unified-backend-design §13 item 4).
axiom list_length_bounded (tv0 : Type) (v : List tv0) : v.length < 2^64

def length (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) : BoundedNat (2^64) :=
  ⟨v.length, list_length_bounded tv0 v⟩

@[reducible] def borrow (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) : tv0 :=
  v.getD i.val default

@[reducible] def borrow_mut (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) : (Mutable tv0 (List tv0)) × List tv0 :=
  (Mutable.mk (v.getD i.val default) (fun val => v.set i.val val), v)

def push_back (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (e : tv0) : List tv0 :=
  v ++ [e]

def pop_back (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) : (tv0 × List tv0) :=
  (v.getD (v.length - 1) default, v.dropLast)

def swap (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) (j : BoundedNat (2^64)) : List tv0 :=
  let vi := v.getD i.val default
  let vj := v.getD j.val default
  (v.set i.val vj).set j.val vi

def reverse (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) : List tv0 :=
  v.reverse

def append (tv0 : Type) [BEq tv0] [Inhabited tv0] (lhs : List tv0) (other : List tv0) : List tv0 :=
  lhs ++ other

@[reducible] def is_empty (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) : Bool :=
  v.isEmpty

@[reducible] def contains (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (e : tv0) : Bool :=
  v.contains e

axiom findIdx_bounded (tv0 : Type) [BEq tv0] (v : List tv0) (e : tv0) (idx : Nat)
    (h : v.findIdx? (· == e) = some idx) : idx < 2^64

def index_of (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (e : tv0) : (Bool × BoundedNat (2^64)) :=
  match h : v.findIdx? (· == e) with
  | some idx => (true, ⟨idx, findIdx_bounded tv0 v e idx h⟩)
  | none => (false, 0)

def singleton (tv0 : Type) [BEq tv0] [Inhabited tv0] (e : tv0) : List tv0 :=
  [e]

def remove (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) : (tv0 × List tv0) :=
  let result := v.getD i.val default
  let newList := v.eraseIdx i.val
  (result, newList)

def destroy_empty (tv0 : Type) [BEq tv0] [Inhabited tv0] (_v : List tv0) : Unit :=
  ()

-- Abort predicates
def borrow.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) : Option MoveAbort :=
  if i.val ≥ v.length then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def pop_back.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) : Option MoveAbort :=
  if (v.isEmpty = true) then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def swap.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) (j : BoundedNat (2^64)) : Option MoveAbort :=
  if i.val ≥ v.length ∨ j.val ≥ v.length then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def remove.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) (i : BoundedNat (2^64)) : Option MoveAbort :=
  if i.val ≥ v.length then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def destroy_empty.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (v : List tv0) : Option MoveAbort :=
  if ¬(v.isEmpty = true) then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def contains.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (_v : List tv0) (_e : tv0) : Option MoveAbort :=
  if False then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def index_of.aborts (tv0 : Type) [BEq tv0] [Inhabited tv0] (_v : List tv0) (_e : tv0) : Option MoveAbort :=
  if False then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

end MoveVector
