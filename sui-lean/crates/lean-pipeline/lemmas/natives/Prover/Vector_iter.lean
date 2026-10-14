-- Native implementations for prover::vector_iter module
-- Standalone functions (not begin/end lambda pairs, which are handled by quantifier lifting)

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.Quantifiers
import MoveStdlib.MoveVectorNatives
import MoveStdlib.IntegerNatives

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

def range.aborts (_start : BoundedNat (2^64)) (_end_ : BoundedNat (2^64)) : Bool := false

def slice (t_tv0 : Type) [BEq t_tv0] [Inhabited t_tv0] (v : List t_tv0) (start : BoundedNat (2^64)) (end_ : BoundedNat (2^64)) : List t_tv0 :=
  v.drop start.val |>.take (end_.val - start.val)

def slice.aborts (_t_tv0 : Type) [BEq _t_tv0] [Inhabited _t_tv0] (_v : List _t_tv0) (_start : BoundedNat (2^64)) (_end_ : BoundedNat (2^64)) : Bool := false

def sum (t_tv0 : Type) [BEq t_tv0] [Inhabited t_tv0] [SpecToInteger t_tv0] (v : List t_tv0) : Integer.Integer :=
  v.foldl (fun acc x => acc + SpecToInteger.toInteger x) 0

def sum.aborts (_t_tv0 : Type) [BEq _t_tv0] [Inhabited _t_tv0] (_v : List _t_tv0) : Bool := false

def sum_range (t_tv0 : Type) [BEq t_tv0] [Inhabited t_tv0] [SpecToInteger t_tv0] (v : List t_tv0) (start : BoundedNat (2^64)) (end_ : BoundedNat (2^64)) : Integer.Integer :=
  (List.range (end_.val - start.val)).foldl (fun acc i => acc + SpecToInteger.toInteger (v.getD (i + start.val) default)) 0

def sum_range.aborts (_t_tv0 : Type) [BEq _t_tv0] [Inhabited _t_tv0] (_v : List _t_tv0) (_start : BoundedNat (2^64)) (_end_ : BoundedNat (2^64)) : Bool := false

end

end Vector_iter
