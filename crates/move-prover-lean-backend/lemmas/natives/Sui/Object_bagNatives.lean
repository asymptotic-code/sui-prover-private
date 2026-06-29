-- Native implementations for sui::object_bag.
-- See `BagNatives.lean` for the design rationale (Bag (U : Type)
-- with no `[Universe U]` at struct level; constraint lives on
-- operations only).

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.Universe
import Prelude.MoveAbort
import Sui.ObjectNatives

namespace Object_bag

structure ObjectBag (U : Type) where
  id   : Object.UID
  size : BoundedNat (2^64)
deriving Inhabited, BEq

-- `object_bag::new` is omitted in the legacy backport (takes a TxContext the
-- legacy pipeline generates rather than defining in the prelude). See BagNatives.

def add {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K]
    (self : ObjectBag U) (_k : K) (_v : V) : ObjectBag U :=
  { self with size := self.size + 1 }
def add.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K]
    (_self : ObjectBag U) (_k : K) (_v : V) : Bool := false

def remove {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K] [Inhabited V]
    (self : ObjectBag U) (_k : K) : V × ObjectBag U :=
  (default, { self with size := self.size - 1 })
def remove.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K] [Inhabited V]
    (_self : ObjectBag U) (_k : K) : Bool := false

def borrow {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K] [Inhabited V]
    (_self : ObjectBag U) (_k : K) : V :=
  default
def borrow.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K] [Inhabited V]
    (_self : ObjectBag U) (_k : K) : Bool := false

def contains {U : Type} [Universe U] (K : Type)
    [HasCode U K] [BEq K]
    (_self : ObjectBag U) (_k : K) : Bool := false
def contains.aborts {U : Type} [Universe U] (K : Type)
    [HasCode U K] [BEq K]
    (_self : ObjectBag U) (_k : K) : Bool := false

def contains_with_type {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K]
    (_self : ObjectBag U) (_k : K) : Bool := false
def contains_with_type.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K]
    (_self : ObjectBag U) (_k : K) : Bool := false

def length {U : Type} (self : ObjectBag U) : BoundedNat (2^64) := self.size
def length.aborts {U : Type} (_self : ObjectBag U) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def is_empty {U : Type} (self : ObjectBag U) : Bool :=
  self.size == (0 : BoundedNat (2^64))
def is_empty.aborts {U : Type} (_self : ObjectBag U) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

end Object_bag
