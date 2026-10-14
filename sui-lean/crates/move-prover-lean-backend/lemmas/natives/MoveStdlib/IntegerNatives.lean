-- Native implementations for std::integer::Integer
-- This is a spec-only type representing mathematical integers

import Prelude.BoundedNat
import Prelude.MoveAbort

namespace Integer

-- Integer is represented as Lean's Int (arbitrary precision signed integer)
abbrev Integer := Int

private def toUnsigned (bound : Nat) (hbound : 0 < bound) (x : Integer) : BoundedNat bound :=
  let r : Int := x % (bound : Int)
  ⟨r.toNat, by
    have hboundInt : 0 < (bound : Int) := Int.ofNat_lt.mpr hbound
    have hnonzero : (bound : Int) ≠ 0 := Int.ne_of_gt hboundInt
    have hnonneg : 0 ≤ r := Int.emod_nonneg _ hnonzero
    have hlt : r < (bound : Int) := Int.emod_lt_of_pos _ hboundInt
    exact (Int.toNat_lt hnonneg).2 hlt
  ⟩

private def bitAndInt : Integer → Integer → Integer
  | .ofNat m, .ofNat n => .ofNat (m &&& n)
  | .ofNat m, .negSucc n => .ofNat (m ^^^ (m &&& n))
  | .negSucc m, .ofNat n => .ofNat (n ^^^ (m &&& n))
  | .negSucc m, .negSucc n => .negSucc (m ||| n)

private def bitOrInt : Integer → Integer → Integer
  | .ofNat m, .ofNat n => .ofNat (m ||| n)
  | .ofNat m, .negSucc n => .negSucc (n ^^^ (m &&& n))
  | .negSucc m, .ofNat n => .negSucc (m ^^^ (m &&& n))
  | .negSucc m, .negSucc n => .negSucc (m &&& n)

private def bitXorInt : Integer → Integer → Integer
  | .ofNat m, .ofNat n => .ofNat (m ^^^ n)
  | .ofNat m, .negSucc n => .negSucc (m ^^^ n)
  | .negSucc m, .ofNat n => .negSucc (m ^^^ n)
  | .negSucc m, .negSucc n => .ofNat (m ^^^ n)

-- Construction from unsigned integers
def from_u8 (x : BoundedNat (2^8)) : Integer := x.val
def from_u16 (x : BoundedNat (2^16)) : Integer := x.val
def from_u32 (x : BoundedNat (2^32)) : Integer := x.val
def from_u64 (x : BoundedNat (2^64)) : Integer := x.val
def from_u128 (x : BoundedNat (2^128)) : Integer := x.val
def from_u256 (x : BoundedNat (2^256)) : Integer := x.val

-- Conversion to unsigned integers
def to_u8 (x : Integer) : BoundedNat (2^8) := toUnsigned (2^8) (by decide) x
def to_u16 (x : Integer) : BoundedNat (2^16) := toUnsigned (2^16) (by decide) x
def to_u32 (x : Integer) : BoundedNat (2^32) := toUnsigned (2^32) (by decide) x
def to_u64 (x : Integer) : BoundedNat (2^64) := toUnsigned (2^64) (by decide) x
def to_u128 (x : Integer) : BoundedNat (2^128) := toUnsigned (2^128) (by decide) x
def to_u256 (x : Integer) : BoundedNat (2^256) := toUnsigned (2^256) (by decide) x

-- Arithmetic operations
def add (x y : Integer) : Integer := x + y
def sub (x y : Integer) : Integer := x - y
def mul (x y : Integer) : Integer := x * y
def div (x y : Integer) : Integer := x / y
def mod (x y : Integer) : Integer := x % y
def neg (x : Integer) : Integer := -x
-- Stub: integer square root requires Nat.sqrt which isn't available in this
-- Lean toolchain. Returns 0; tests that depend on actual sqrt values aren't
-- expressible against this stub.
def sqrt (_x : Integer) : Integer := 0
def pow (base exp : Integer) : Integer := base ^ exp.toNat

-- Bitwise operations
def bit_or (x y : Integer) : Integer := bitOrInt x y
def bit_and (x y : Integer) : Integer := bitAndInt x y
def bit_xor (x y : Integer) : Integer := bitXorInt x y
def bit_not (x : Integer) : Integer := ~~~x

-- Comparison operations
@[reducible] def lt (x y : Integer) : Prop := x < y
instance (x y : Integer) : Decidable (lt x y) := inferInstance
@[reducible] def le (x y : Integer) : Prop := x ≤ y
instance (x y : Integer) : Decidable (le x y) := inferInstance
@[reducible] def lte (x y : Integer) : Prop := x ≤ y
instance (x y : Integer) : Decidable (lte x y) := inferInstance
@[reducible] def gt (x y : Integer) : Prop := x > y
instance (x y : Integer) : Decidable (gt x y) := inferInstance
@[reducible] def ge (x y : Integer) : Prop := x ≥ y
instance (x y : Integer) : Decidable (ge x y) := inferInstance
@[reducible] def gte (x y : Integer) : Prop := x ≥ y
instance (x y : Integer) : Decidable (gte x y) := inferInstance

-- Derived functions
@[reducible] def is_neg (x : Integer) : Prop := x < 0
instance (x : Integer) : Decidable (is_neg x) := inferInstance
@[reducible] def is_pos (x : Integer) : Prop := x ≥ 0
instance (x : Integer) : Decidable (is_pos x) := inferInstance
def abs (x : Integer) : Integer := if x < 0 then -x else x

def div_round_up (x y : Integer) : Integer :=
  let result := x / y
  if x % y != 0 then result + 1 else result

def div_trunc (x y : Integer) : Integer :=
  let result_abs := (abs x) / (abs y)
  if (is_pos x ∧ is_pos y) ∨ (is_neg x ∧ is_neg y) then
    result_abs
  else
    -result_abs

def mod_trunc (x y : Integer) : Integer :=
  x - y * (div_trunc x y)

def shl (x y : Integer) : Integer := x * (pow 2 y)
def shr (x y : Integer) : Integer := x / (pow 2 y)

-- Signed integer conversions
def signed_from_u8 (x : BoundedNat (2^8)) : Integer :=
  if x.val ≤ 0x7f then from_u8 x
  else from_u8 x - from_u8 ⟨0xff, by decide⟩ - 1

def signed_from_u16 (x : BoundedNat (2^16)) : Integer :=
  if x.val ≤ 0x7fff then from_u16 x
  else from_u16 x - from_u16 ⟨0xffff, by decide⟩ - 1

def signed_from_u32 (x : BoundedNat (2^32)) : Integer :=
  if x.val ≤ 0x7fffffff then from_u32 x
  else from_u32 x - from_u32 ⟨0xffffffff, by decide⟩ - 1

def signed_from_u64 (x : BoundedNat (2^64)) : Integer :=
  if x.val ≤ 0x7fffffffffffffff then from_u64 x
  else from_u64 x - from_u64 ⟨0xffffffffffffffff, by decide⟩ - 1

def signed_from_u128 (x : BoundedNat (2^128)) : Integer :=
  if x.val ≤ 0x7fffffffffffffffffffffffffffffff then from_u128 x
  else from_u128 x - from_u128 ⟨0xffffffffffffffffffffffffffffffff, by decide⟩ - 1

def signed_from_u256 (x : BoundedNat (2^256)) : Integer :=
  if x.val ≤ 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff then from_u256 x
  else from_u256 x - from_u256 ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, by decide⟩ - 1

-- Range checks for signed integers
@[reducible] def is_i8 (x : Integer) : Prop := x ≥ -128 ∧ x ≤ 127
instance (x : Integer) : Decidable (is_i8 x) := inferInstance
@[reducible] def is_i16 (x : Integer) : Prop := x ≥ -32768 ∧ x ≤ 32767
instance (x : Integer) : Decidable (is_i16 x) := inferInstance
@[reducible] def is_i32 (x : Integer) : Prop := x ≥ -2147483648 ∧ x ≤ 2147483647
instance (x : Integer) : Decidable (is_i32 x) := inferInstance
@[reducible] def is_i64 (x : Integer) : Prop := x ≥ -9223372036854775808 ∧ x ≤ 9223372036854775807
instance (x : Integer) : Decidable (is_i64 x) := inferInstance
@[reducible] def is_i128 (x : Integer) : Prop := x ≥ -170141183460469231731687303715884105728 ∧ x ≤ 170141183460469231731687303715884105727
instance (x : Integer) : Decidable (is_i128 x) := inferInstance
@[reducible] def is_i256 (x : Integer) : Prop := x ≥ -57896044618658097711785492504343953926634992332820282019728792003956564819968 ∧ x ≤ 57896044618658097711785492504343953926634992332820282019728792003956564819967
instance (x : Integer) : Decidable (is_i256 x) := inferInstance

-- Abort predicates (these functions are pure and don't abort)
def div_round_up.aborts (_x _y : Integer) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none
def div_trunc.aborts (_x _y : Integer) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none
def mod_trunc.aborts (_x _y : Integer) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

end Integer
