-- Native implementations for prover::vector_iter module
-- Standalone functions (not begin/end lambda pairs, which are handled by quantifier lifting)

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.MoveAbort
import MoveStdlib.MoveVectorNatives
import MoveStdlib.Integer

-- `Vector_iter.sum`/`sum_range` were originally `opaque` (uninterpreted), which made
-- any spec written in terms of them unprovable. They are only ever applied to
-- `List (BoundedNat n)` across all packages, so we give them a real computable
-- definition that interprets each element via the `HasMoveSum` class. The class
-- instance is auto-resolved from the element type at every call site — the generated
-- call `Vector_iter.sum (BoundedNat (2^64)) v` never passes it explicitly, but Lean
-- infers it. `Integer := Int`; Move sums of `u*` values are unbounded `Integer`
-- sums (no wraparound), matching the spec authors' intent.
class HasMoveSum (α : Type) where
  toInt : α → Integer.Integer

instance {n : Nat} : HasMoveSum (BoundedNat n) where
  toInt x := (x.val : Integer.Integer)

namespace Vector_iter

noncomputable section

def range (start : BoundedNat (2^64)) (end_ : BoundedNat (2^64)) : List (BoundedNat (2^64)) :=
  if start.val ≤ end_.val then
    (List.range (end_.val - start.val)).attach.map (fun ⟨i, hi⟩ =>
      ⟨i + start.val, by
        have := List.mem_range.mp hi
        exact Nat.lt_of_lt_of_le (by omega) end_.property⟩)
  else
    []

def range.aborts (_start : BoundedNat (2^64)) (_end_ : BoundedNat (2^64)) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def slice (t_tv0 : Type) [BEq t_tv0] [Inhabited t_tv0] (v : List t_tv0) (start : BoundedNat (2^64)) (end_ : BoundedNat (2^64)) : List t_tv0 :=
  v.drop start.val |>.take (end_.val - start.val)

def slice.aborts (_t_tv0 : Type) [BEq _t_tv0] [Inhabited _t_tv0] (_v : List _t_tv0) (_start : BoundedNat (2^64)) (_end_ : BoundedNat (2^64)) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def sum (t_tv0 : Type) [BEq t_tv0] [Inhabited t_tv0] [HasMoveSum t_tv0]
    (v : List t_tv0) : Integer.Integer :=
  (v.map HasMoveSum.toInt).foldr (· + ·) 0

def sum.aborts (_t_tv0 : Type) [BEq _t_tv0] [Inhabited _t_tv0] (_v : List _t_tv0) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def sum_range (t_tv0 : Type) [BEq t_tv0] [Inhabited t_tv0] [HasMoveSum t_tv0]
    (v : List t_tv0) (start : BoundedNat (2^64)) (end_ : BoundedNat (2^64)) : Integer.Integer :=
  ((v.drop start.val |>.take (end_.val - start.val)).map HasMoveSum.toInt).foldr (· + ·) 0

def sum_range.aborts (_t_tv0 : Type) [BEq _t_tv0] [Inhabited _t_tv0] (_v : List _t_tv0) (_start : BoundedNat (2^64)) (_end_ : BoundedNat (2^64)) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

end

end Vector_iter
