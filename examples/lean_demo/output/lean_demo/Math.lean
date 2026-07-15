-- Module: math

import Prelude.AbortsTactics
import Prelude.BoundedArith
import Prelude.BoundedNat
import Prelude.Combinatorics
import Prelude.Helpers
import Prelude.LoopTermination
import Prelude.MoveAbort
import Prelude.MoveType
import Prelude.ProgramState
import Prelude.Quantifiers
import Prelude.TypeConversion
import Prelude.TypedMap
import Prelude.Universe
import Prelude.World
import Prelude.WorldSimp
import Prover.Prover

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Math

-- Struct: math::Balance
structure Balance where
  value : BoundedNat (2^64)
deriving BEq
instance : Inhabited Balance where default := ⟨default⟩

@[reducible] def max (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : BoundedNat (2^64) :=
  if decide (a ≥ b) then
    a
  else
    b

@[reducible] def max.aborts (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : (Option (MoveAbort)) :=
  MoveAbort.orElse (Option.none) (let tmp__t_2 := (if decide (a ≥ b) then
    a
  else
    b)
  Option.none)

@[reducible] def withdraw (balance : Balance) (amount : BoundedNat (2^64)) : (BoundedNat (2^64) × Balance) :=
  let t_t5 := balance.value
  let t_t7 := balance.value
  let t_t7 := t_t5 - amount
  let balance : Balance := { balance with value := t_t7 }
  let balance : Balance := { balance with value := t_t7 }
  (amount, balance)

@[reducible] def withdraw.aborts (balance : Balance) (amount : BoundedNat (2^64)) : (Option (MoveAbort)) :=
  MoveAbort.orElse (let t_t2 := balance.value
  let t_t3 := decide (amount ≤ t_t2)
  let t_t5 := balance.value
  MoveAbort.orElse (if (BoundedNat.sub_underflows t_t5 amount) then
    Option.some ((({ source := MoveAbort.AbortSource.arithmetic, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
  else
    Option.none) (let t_t6 := t_t5 - amount
  let t_t7 := balance.value
  let t_t7 := t_t6
  let balance : Balance := { balance with value := t_t7 }
  let balance : Balance := { balance with value := t_t7 }
  Option.none)) (let t_t2 := balance.value
  let t_t3 := decide (amount ≤ t_t2)
  if t_t3 then
    Option.none
  else
    Option.some ((({ source := MoveAbort.AbortSource.userAssert, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort))))

@[reducible] def clamp (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) : BoundedNat (2^64) :=
  if decide (value < low) then
    low
  else
    if decide (value > high) then
      high
    else
      value

@[reducible] def clamp.aborts (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) : (Option (MoveAbort)) :=
  MoveAbort.orElse (if decide (value < low) then
    Option.none
  else
    let t_t6 := decide (value > high)
    MoveAbort.orElse (if t_t6 then
      let tmp__t_3 := high
      Option.none
    else
      let tmp__t_3 := value
      Option.none) (let tmp__t_3 := (if t_t6 then
      high
    else
      value)
    Option.none)) (let tmp__t_4 := (if decide (value < low) then
    low
  else
    let t_t6 := decide (value > high)
    if t_t6 then
      high
    else
      value)
  Option.none)

@[reducible] def distance (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : BoundedNat (2^64) :=
  if decide (a ≥ b) then
    a - b
  else
    b - a

@[reducible] def distance.aborts (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : (Option (MoveAbort)) :=
  MoveAbort.orElse (if decide (a ≥ b) then
    MoveAbort.orElse (if (BoundedNat.sub_underflows a b) then
      Option.some ((({ source := MoveAbort.AbortSource.arithmetic, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
    else
      Option.none) (Option.none)
  else
    MoveAbort.orElse (if (BoundedNat.sub_underflows b a) then
      Option.some ((({ source := MoveAbort.AbortSource.arithmetic, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
    else
      Option.none) (Option.none)) (let tmp__t_2 := (if decide (a ≥ b) then
    a - b
  else
    b - a)
  Option.none)

def clamp_spec.requires (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) : Prop :=
  ((decide (low ≤ high)) = true)

def transfer_spec.asserts_cond (from_ : Balance) (to : Balance) (amount : BoundedNat (2^64)) : Prop :=
  ((decide (amount ≤ (from_.value))) = true)

def transfer_spec.asserts_cond_1 (from_ : Balance) (to : Balance) (amount : BoundedNat (2^64)) : Prop :=
  ((decide ((to.value) ≤ ((18446744073709551615 : BoundedNat (2^64)) - amount))) = true)

def withdraw_spec.asserts_cond (balance : Balance) (amount : BoundedNat (2^64)) : Prop :=
  ((decide (amount ≤ (balance.value))) = true)

@[reducible] def max_spec (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : BoundedNat (2^64) :=
  max a b

def max_spec.ensures (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : Prop :=
  ((decide ((_root_.Math.max a b) ≥ a)) = true)

def max_spec.ensures_1 (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : Prop :=
  ((decide ((_root_.Math.max a b) ≥ b)) = true)

def max_spec.ensures_2 (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : Prop :=
  let t_t4 := _root_.Math.max a b
  let tmp__t_2 := (t_t4 == a) || (t_t4 == b)
  (tmp__t_2 = true)

@[reducible] def max_spec.aborts (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : (Option (MoveAbort)) :=
  MoveAbort.orElse (MoveAbort.orElse (_root_.Math.max.aborts a b) (Option.none)) (let t_t4 := _root_.Math.max a b
  let t_t5 := decide (t_t4 ≥ a)
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts t_t5) (Option.none)) (let t_t6 := decide (t_t4 ≥ b)
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts t_t6) (Option.none)) (let t_t7 := t_t4 == a
  MoveAbort.orElse (if t_t7 then
    let t_t8 := true
    let tmp__t_2 := t_t8
    Option.none
  else
    let tmp__t_2 := t_t4 == b
    Option.none) (let tmp__t_2 := (if t_t7 then
    true
  else
    t_t4 == b)
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts tmp__t_2) (Option.none)) (Option.none)))))

@[reducible] def transfer (from_ : Balance) (to : Balance) (amount : BoundedNat (2^64)) : (Balance × Balance) :=
  let __pair__t_t9___mut_ret := withdraw from_ amount
  let t_t9 := __pair__t_t9___mut_ret.1
  let __mut_ret := __pair__t_t9___mut_ret.2
  let from_ := __mut_ret
  let t_t10 := to.value
  let t_t12 := to.value
  let t_t12 := t_t10 + t_t9
  let to : Balance := { to with value := t_t12 }
  let to : Balance := { to with value := t_t12 }
  (from_, to)

@[reducible] def withdraw_spec (balance : Balance) (amount : BoundedNat (2^64)) : (BoundedNat (2^64) × Balance) :=
  let t_t4 := balance.value
  let _ := Prover.asserts (decide (amount ≤ t_t4))
  let __pair__t_t6___mut_ret := withdraw balance amount
  let t_t6 := __pair__t_t6___mut_ret.1
  let __mut_ret := __pair__t_t6___mut_ret.2
  let balance := __mut_ret
  (t_t6, balance)

def withdraw_spec.ensures (balance : Balance) (amount : BoundedNat (2^64)) : Prop :=
  let __pair__t_t6___mut_ret := _root_.Math.withdraw balance amount
  let t_t6 := __pair__t_t6___mut_ret.1
  let __mut_ret := __pair__t_t6___mut_ret.2
  let balance_post := __mut_ret
  ((t_t6 == amount) = true)

def withdraw_spec.ensures_1 (balance : Balance) (amount : BoundedNat (2^64)) : Prop :=
  let t_t4 := balance.value
  let __pair___mut_ret := _root_.Math.withdraw balance amount
  let __mut_ret := __pair___mut_ret.2
  let balance_post := __mut_ret
  (((balance_post.value) == (t_t4 - amount)) = true)

@[reducible] def transfer.aborts (from_ : Balance) (to : Balance) (amount : BoundedNat (2^64)) : (Option (MoveAbort)) :=
  MoveAbort.orElse (let t_t4 := to.value
  let t_t5 := (18446744073709551615 : BoundedNat (2^64))
  MoveAbort.orElse (if (BoundedNat.sub_underflows t_t5 amount) then
    Option.some ((({ source := MoveAbort.AbortSource.arithmetic, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
  else
    Option.none) (let t_t6 := t_t5 - amount
  let t_t7 := decide (t_t4 ≤ t_t6)
  MoveAbort.orElse (MoveAbort.orElse (_root_.Math.withdraw.aborts from_ amount) (Option.none)) (let __pair__t_t9___mut_ret := _root_.Math.withdraw from_ amount
  let t_t9 := __pair__t_t9___mut_ret.1
  let __mut_ret := __pair__t_t9___mut_ret.2
  let from_ := __mut_ret
  let t_t10 := to.value
  MoveAbort.orElse (if (BoundedNat.add_overflows t_t10 t_t9) then
    Option.some ((({ source := MoveAbort.AbortSource.arithmetic, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
  else
    Option.none) (let t_t11 := t_t10 + t_t9
  let t_t12 := to.value
  let t_t12 := t_t11
  let to : Balance := { to with value := t_t12 }
  let to : Balance := { to with value := t_t12 }
  Option.none)))) (let t_t4 := to.value
  let t_t5 := (18446744073709551615 : BoundedNat (2^64))
  let t_t6 := t_t5 - amount
  let t_t7 := decide (t_t4 ≤ t_t6)
  if t_t7 then
    Option.none
  else
    Option.some ((({ source := MoveAbort.AbortSource.userAssert, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort))))

@[reducible] def withdraw_spec.aborts (balance : Balance) (amount : BoundedNat (2^64)) : (Option (MoveAbort)) :=
  MoveAbort.orElse (let t_t4 := balance.value
  let t_t5 := decide (amount ≤ t_t4)
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.asserts.aborts t_t5) (Option.none)) (MoveAbort.orElse (MoveAbort.orElse (_root_.Math.withdraw.aborts balance amount) (Option.none)) (let __pair__t_t6___mut_ret := _root_.Math.withdraw balance amount
  let t_t6 := __pair__t_t6___mut_ret.1
  let __mut_ret := __pair__t_t6___mut_ret.2
  let balance := __mut_ret
  let t_t7 := t_t6 == amount
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts t_t7) (Option.none)) (let t_t8 := balance.value
  MoveAbort.orElse (if (BoundedNat.sub_underflows t_t4 amount) then
    Option.some ((({ source := MoveAbort.AbortSource.arithmetic, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
  else
    Option.none) (let t_t9 := t_t4 - amount
  let t_t10 := t_t8 == t_t9
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts t_t10) (Option.none)) (Option.none)))))) (let t_t4 := balance.value
  let t_t5 := decide (amount ≤ t_t4)
  if !t_t5 then
    Option.some ((({ source := MoveAbort.AbortSource.userAssert, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
  else
    Option.none)

@[reducible] def clamp_spec (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) : BoundedNat (2^64) :=
  let t_t6 := clamp value low high
  let tmp__t_3 := (t_t6 == low) || (
    let t_t11 := t_t6 == value
    t_t11 || (t_t6 == high))
  t_t6

def clamp_spec.ensures (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) : Prop :=
  ((decide ((_root_.Math.clamp value low high) ≥ low)) = true)

def clamp_spec.ensures_1 (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) : Prop :=
  ((decide ((_root_.Math.clamp value low high) ≤ high)) = true)

def clamp_spec.ensures_2 (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) : Prop :=
  let t_t6 := _root_.Math.clamp value low high
  let tmp__t_3 := (t_t6 == low) || (
    let t_t11 := t_t6 == value
    t_t11 || (t_t6 == high))
  (tmp__t_3 = true)

@[reducible] def clamp_spec.aborts (value : BoundedNat (2^64)) (low : BoundedNat (2^64)) (high : BoundedNat (2^64)) : (Option (MoveAbort)) :=
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.requires.aborts (decide (low ≤ high))) (Option.none)) (MoveAbort.orElse (MoveAbort.orElse (_root_.Math.clamp.aborts value low high) (Option.none)) (let t_t6 := _root_.Math.clamp value low high
  let t_t7 := decide (t_t6 ≥ low)
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts t_t7) (Option.none)) (let t_t8 := decide (t_t6 ≤ high)
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts t_t8) (Option.none)) (let t_t9 := t_t6 == low
  MoveAbort.orElse (if t_t9 then
    let t_t10 := true
    let tmp__t_3 := t_t10
    Option.none
  else
    let t_t11 := t_t6 == value
    if t_t11 then
      let t_t12 := true
      let tmp__t_3 := t_t12
      Option.none
    else
      let tmp__t_3 := t_t6 == high
      Option.none) (let tmp__t_3 := (if t_t9 then
    true
  else
    let t_t11 := t_t6 == value
    if t_t11 then
      true
    else
      t_t6 == high)
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts tmp__t_3) (Option.none)) (Option.none))))))

@[reducible] def distance_spec (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : BoundedNat (2^64) :=
  let t_t4 := distance a b
  let t_t10 := Prover.implies (a == b) (t_t4 == (0 : BoundedNat (2^64)))
  let t_t14 := Prover.implies (t_t4 == (0 : BoundedNat (2^64))) (a == b)
  t_t4

def distance_spec.ensures (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : Prop :=
  let t_t4 := _root_.Math.distance a b
  let tmp__t_2 := (decide (t_t4 ≤ a)) || (decide (t_t4 ≤ b))
  (tmp__t_2 = true)

def distance_spec.ensures_1 (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : Prop :=
  ((_root_.Prover.implies (a == b) ((_root_.Math.distance a b) == (0 : BoundedNat (2^64)))) = true)

def distance_spec.ensures_2 (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : Prop :=
  let t_t4 := _root_.Math.distance a b
  let t_t10 := _root_.Prover.implies (a == b) (t_t4 == (0 : BoundedNat (2^64)))
  ((_root_.Prover.implies (t_t4 == (0 : BoundedNat (2^64))) (a == b)) = true)

@[reducible] def distance_spec.aborts (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : (Option (MoveAbort)) :=
  MoveAbort.orElse (MoveAbort.orElse (_root_.Math.distance.aborts a b) (Option.none)) (let t_t4 := _root_.Math.distance a b
  let t_t5 := decide (t_t4 ≤ a)
  MoveAbort.orElse (if t_t5 then
    let t_t6 := true
    let tmp__t_2 := t_t6
    Option.none
  else
    let tmp__t_2 := decide (t_t4 ≤ b)
    Option.none) (let tmp__t_2 := (if t_t5 then
    true
  else
    decide (t_t4 ≤ b))
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts tmp__t_2) (Option.none)) (let t_t7 := a == b
  let t_t8 := (0 : BoundedNat (2^64))
  let t_t9 := t_t4 == t_t8
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.implies.aborts t_t7 t_t9) (Option.none)) (let t_t10 := _root_.Prover.implies t_t7 t_t9
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts t_t10) (Option.none)) (let t_t11 := (0 : BoundedNat (2^64))
  let t_t12 := t_t4 == t_t11
  let t_t13 := a == b
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.implies.aborts t_t12 t_t13) (Option.none)) (let t_t14 := _root_.Prover.implies t_t12 t_t13
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts t_t14) (Option.none)) (Option.none)))))))

@[reducible] def transfer_spec (from_ : Balance) (to : Balance) (amount : BoundedNat (2^64)) : (Balance × Balance) :=
  let t_t5 := from_.value
  let t_t6 := to.value
  let _ := Prover.asserts (decide (amount ≤ t_t5))
  let _ := Prover.asserts (decide (t_t6 ≤ ((18446744073709551615 : BoundedNat (2^64)) - amount)))
  let __pair___mut_ret_0___mut_ret_1 := transfer from_ to amount
  let __mut_ret_0 := __pair___mut_ret_0___mut_ret_1.1
  let __mut_ret_1 := __pair___mut_ret_0___mut_ret_1.2
  let from_ := __mut_ret_0
  let to := __mut_ret_1
  (from_, to)

def transfer_spec.ensures (from_ : Balance) (to : Balance) (amount : BoundedNat (2^64)) : Prop :=
  let t_t5 := from_.value
  let __pair___mut_ret_0___mut_ret_1 := _root_.Math.transfer from_ to amount
  let __mut_ret_0 := __pair___mut_ret_0___mut_ret_1.1
  let __mut_ret_1 := __pair___mut_ret_0___mut_ret_1.2
  let from_post := __mut_ret_0
  let to_post1 := __mut_ret_1
  (((from_post.value) == (t_t5 - amount)) = true)

def transfer_spec.ensures_1 (from_ : Balance) (to : Balance) (amount : BoundedNat (2^64)) : Prop :=
  let t_t6 := to.value
  let __pair___mut_ret_0___mut_ret_1 := _root_.Math.transfer from_ to amount
  let __mut_ret_0 := __pair___mut_ret_0___mut_ret_1.1
  let __mut_ret_1 := __pair___mut_ret_0___mut_ret_1.2
  let from_post := __mut_ret_0
  let to_post1 := __mut_ret_1
  (((to_post1.value) == (t_t6 + amount)) = true)

def transfer_spec.ensures_2 (from_ : Balance) (to : Balance) (amount : BoundedNat (2^64)) : Prop :=
  let t_t5 := from_.value
  let t_t6 := to.value
  let __pair___mut_ret_0___mut_ret_1 := _root_.Math.transfer from_ to amount
  let __mut_ret_0 := __pair___mut_ret_0___mut_ret_1.1
  let __mut_ret_1 := __pair___mut_ret_0___mut_ret_1.2
  let from_post := __mut_ret_0
  let to_post1 := __mut_ret_1
  (((((BoundedNat.convert (from_post.value) : BoundedNat (2^128))) + ((BoundedNat.convert (to_post1.value) : BoundedNat (2^128)))) == (((BoundedNat.convert t_t5 : BoundedNat (2^128))) + ((BoundedNat.convert t_t6 : BoundedNat (2^128))))) = true)

@[reducible] def transfer_spec.aborts (from_ : Balance) (to : Balance) (amount : BoundedNat (2^64)) : (Option (MoveAbort)) :=
  MoveAbort.orElse (let t_t5 := from_.value
  let t_t6 := to.value
  let t_t7 := decide (amount ≤ t_t5)
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.asserts.aborts t_t7) (Option.none)) (let t_t8 := (18446744073709551615 : BoundedNat (2^64))
  MoveAbort.orElse (if (BoundedNat.sub_underflows t_t8 amount) then
    Option.some ((({ source := MoveAbort.AbortSource.arithmetic, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
  else
    Option.none) (let t_t9 := t_t8 - amount
  let t_t10 := decide (t_t6 ≤ t_t9)
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.asserts.aborts t_t10) (Option.none)) (MoveAbort.orElse (MoveAbort.orElse (_root_.Math.transfer.aborts from_ to amount) (Option.none)) (let __pair___mut_ret_0___mut_ret_1 := _root_.Math.transfer from_ to amount
  let __mut_ret_0 := __pair___mut_ret_0___mut_ret_1.1
  let __mut_ret_1 := __pair___mut_ret_0___mut_ret_1.2
  let from_ := __mut_ret_0
  let to := __mut_ret_1
  let t_t11 := from_.value
  MoveAbort.orElse (if (BoundedNat.sub_underflows t_t5 amount) then
    Option.some ((({ source := MoveAbort.AbortSource.arithmetic, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
  else
    Option.none) (let t_t12 := t_t5 - amount
  let t_t13 := t_t11 == t_t12
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts t_t13) (Option.none)) (let t_t14 := to.value
  MoveAbort.orElse (if (BoundedNat.add_overflows t_t6 amount) then
    Option.some ((({ source := MoveAbort.AbortSource.arithmetic, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
  else
    Option.none) (let t_t15 := t_t6 + amount
  let t_t16 := t_t14 == t_t15
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts t_t16) (Option.none)) (let t_t17 := from_.value
  let t_t18 := (BoundedNat.convert t_t17 : BoundedNat (2^128))
  let t_t19 := to.value
  let t_t20 := (BoundedNat.convert t_t19 : BoundedNat (2^128))
  MoveAbort.orElse (if (BoundedNat.add_overflows t_t18 t_t20) then
    Option.some ((({ source := MoveAbort.AbortSource.arithmetic, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
  else
    Option.none) (let t_t21 := t_t18 + t_t20
  let t_t22 := (BoundedNat.convert t_t5 : BoundedNat (2^128))
  let t_t23 := (BoundedNat.convert t_t6 : BoundedNat (2^128))
  MoveAbort.orElse (if (BoundedNat.add_overflows t_t22 t_t23) then
    Option.some ((({ source := MoveAbort.AbortSource.arithmetic, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
  else
    Option.none) (let t_t24 := t_t22 + t_t23
  let t_t25 := t_t21 == t_t24
  MoveAbort.orElse (MoveAbort.orElse (_root_.Prover.ensures.aborts t_t25) (Option.none)) (Option.none)))))))))))) (let t_t5 := from_.value
  let t_t6 := to.value
  let t_t7 := decide (amount ≤ t_t5)
  if !t_t7 then
    Option.some ((({ source := MoveAbort.AbortSource.userAssert, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
  else
    let t_t8 := (18446744073709551615 : BoundedNat (2^64))
    let t_t9 := t_t8 - amount
    let t_t10 := decide (t_t6 ≤ t_t9)
    if !t_t10 then
      Option.some ((({ source := MoveAbort.AbortSource.userAssert, code := ((0 : BoundedNat (2^64))).toNat, module := "lean_demo::math" } : MoveAbort)))
    else
      Option.none)

end Math

