/-
# Bounded Natural Numbers

Generic bounded natural number type that replaces UInt8, UInt16, UInt32, UInt64, UInt128, UInt256.

## Design

- Representation: { n : Nat // n < bound }
- Operations: Addition and multiplication use axioms to assume no overflow
- Other operations: Proven correct using Lean's built-in Nat theorems
- Bounds: Maintained by construction with omega proofs

This simplifies verification by assuming arithmetic operations never overflow.
-/

/-- Every fixed-width bound is `2 ^ n`, which is positive, so a bound is never
zero. This instance lets the width-changing operations below stay total without
an axiom; at concrete widths it is synthesized automatically. -/
instance instNeZeroTwoPow (n : Nat) : NeZero ((2 : Nat) ^ n) :=
  ⟨Nat.ne_of_gt (Nat.two_pow_pos n)⟩

/-- A natural number bounded by a given limit -/
structure BoundedNat (bound : Nat) where
  val : Nat
  property : val < bound

/-- Any inhabitant of `BoundedNat bound` witnesses `bound > 0`. Used to discharge
the unreachable `bound = 0` branch of the width-preserving operations without an
axiom. -/
theorem BoundedNat.bound_pos {bound : Nat} (a : BoundedNat bound) : bound > 0 :=
  Nat.lt_of_le_of_lt (Nat.zero_le a.val) a.property

namespace BoundedNat

variable {bound : Nat}

/-- Create a BoundedNat from a Nat literal -/
def ofNat (n : Nat) (h : n < bound) : BoundedNat bound :=
  ⟨n, h⟩

/-- Convert to natural number -/
def toNat (n : BoundedNat bound) : Nat := n.val

/-- Equality is decidable -/
instance : DecidableEq (BoundedNat bound) :=
  fun a b => decidable_of_iff (a.val = b.val) (by
    constructor
    · intro h; cases a; cases b; simp only at h; simp [BoundedNat.mk.injEq]; exact h
    · intro h; cases h; rfl)

/-- Ordering -/
instance : LT (BoundedNat bound) where
  lt a b := a.val < b.val

instance : LE (BoundedNat bound) where
  le a b := a.val ≤ b.val

instance : DecidableRel (fun (a b : BoundedNat bound) => a < b) :=
  fun a b => inferInstanceAs (Decidable (a.val < b.val))

instance : DecidableRel (fun (a b : BoundedNat bound) => a ≤ b) :=
  fun a b => inferInstanceAs (Decidable (a.val ≤ b.val))

/-- Comparison -/
def compare (a b : BoundedNat bound) : Ordering :=
  if a.val < b.val then Ordering.lt
  else if a.val = b.val then Ordering.eq
  else Ordering.gt

/-! ## Bool-valued comparison helpers

Named functions matching the Bool-returning shape the IR expects.
The `LT` / `LE` instances above are Prop-valued; these use Nat's
Bool-valued comparisons so the stage-10 IR rewriter has a callable
function target for `BinOp::Lt` etc. -/

@[reducible] def lt (a b : BoundedNat bound) : Bool := Nat.blt a.val b.val
@[reducible] def le (a b : BoundedNat bound) : Bool := Nat.ble a.val b.val
@[reducible] def gt (a b : BoundedNat bound) : Bool := Nat.blt b.val a.val
@[reducible] def ge (a b : BoundedNat bound) : Bool := Bool.not (Nat.blt a.val b.val)
@[reducible] def eq (a b : BoundedNat bound) : Bool := Nat.beq a.val b.val
@[reducible] def neq (a b : BoundedNat bound) : Bool := Bool.not (Nat.beq a.val b.val)

/-! ## Two's-complement interpretation

`UInt(N)` remains the sole fixed-width storage type in the shared IR.  The
helpers below interpret that same bit pattern as signed only for operations
whose IR names explicitly request signed semantics.
-/

/-- Interpret a bounded bit pattern as a two's-complement integer. -/
@[reducible] def signedValue (a : BoundedNat bound) : Int :=
  if a.val < bound / 2 then
    (a.val : Int)
  else
    (a.val : Int) - (bound : Int)

@[reducible] def slt (a b : BoundedNat bound) : Bool :=
  decide (signedValue a < signedValue b)

@[reducible] def sle (a b : BoundedNat bound) : Bool :=
  decide (signedValue a ≤ signedValue b)

@[reducible] def sgt (a b : BoundedNat bound) : Bool :=
  decide (signedValue a > signedValue b)

@[reducible] def sge (a b : BoundedNat bound) : Bool :=
  decide (signedValue a ≥ signedValue b)

/-- Bitwise NOT for fixed-width unsigned integers: `(bound - 1) - a`.
For power-of-2 bounds (Move's `u8`..`u256`), the result is always
`< bound`, so the `% bound` is a no-op. The mod keeps the function
total for arbitrary `bound`. -/
@[reducible] def bnot (a : BoundedNat bound) : BoundedNat bound :=
  if h : bound > 0 then
    ⟨(bound - 1 - a.val) % bound, Nat.mod_lt _ h⟩
  else
    ⟨0, bound_pos a⟩

/-- Addition (wrapping). Total and reducible by the kernel. The abort
predicate `add_overflows` exposes the overflow condition so callers can
state Move's overflow-aborts semantics without an axiom. -/
def add (a b : BoundedNat bound) : BoundedNat bound :=
  if h : bound > 0 then
    ⟨(a.val + b.val) % bound, Nat.mod_lt _ h⟩
  else
    ⟨0, bound_pos a⟩

/-- LLVM-style modular addition. Unlike `add`, stage 10 gives this operation
no abort companion. -/
@[reducible] def wrapping_add (a b : BoundedNat bound) : BoundedNat bound :=
  add a b

/-- True iff `add a b` would overflow at the given bound. Reducible. -/
@[reducible] def add_overflows (a b : BoundedNat bound) : Bool :=
  Bool.not (Nat.blt (a.val + b.val) bound)

/-- Subtraction (saturating to 0) -/
def sub (a b : BoundedNat bound) : BoundedNat bound :=
  ⟨a.val - b.val, Nat.lt_of_le_of_lt (Nat.sub_le a.val b.val) a.property⟩

/-- LLVM-style modular subtraction. This is deliberately separate from
Move's checked/saturating-body `sub`. -/
def wrapping_sub (a b : BoundedNat bound) : BoundedNat bound :=
  if h : bound > 0 then
    ⟨(a.val + bound - b.val) % bound, Nat.mod_lt _ h⟩
  else
    ⟨0, bound_pos a⟩

/-- True iff `sub a b` would underflow (saturate). Reducible. -/
@[reducible] def sub_underflows (a b : BoundedNat bound) : Bool :=
  Nat.blt a.val b.val

/-- Multiplication (wrapping). Total and reducible by the kernel. The abort
predicate `mul_overflows` exposes the overflow condition. -/
def mul (a b : BoundedNat bound) : BoundedNat bound :=
  if h : bound > 0 then
    ⟨(a.val * b.val) % bound, Nat.mod_lt _ h⟩
  else
    ⟨0, bound_pos a⟩

/-- LLVM-style modular multiplication. Unlike `mul`, stage 10 gives this
operation no abort companion. -/
@[reducible] def wrapping_mul (a b : BoundedNat bound) : BoundedNat bound :=
  mul a b

/-- Convert a mathematical integer back to its fixed-width bit pattern. -/
def ofSigned [NeZero bound] (x : Int) : BoundedNat bound :=
  if h : bound > 0 then
    let r : Int := x % (bound : Int)
    ⟨r.toNat, by
      have hboundInt : 0 < (bound : Int) := Int.ofNat_lt.mpr h
      have hnonzero : (bound : Int) ≠ 0 := Int.ne_of_gt hboundInt
      have hnonneg : 0 ≤ r := Int.emod_nonneg _ hnonzero
      have hlt : r < (bound : Int) := Int.emod_lt_of_pos _ hboundInt
      exact (Int.toNat_lt hnonneg).2 hlt⟩
  else
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne bound)⟩

/-- Whether a mathematical integer fits the signed range represented by
`bound`. Stage-10 signed checked arithmetic uses the negation as its abort
predicate. -/
@[reducible] def signedFits (bound : Nat) (x : Int) : Bool :=
  decide (-((bound / 2 : Nat) : Int) ≤ x ∧ x < ((bound / 2 : Nat) : Int))

/-- Signed checked operations return the wrapped bit pattern. Their abort
companions below make the result observable only when the mathematical result
fits the signed range. -/
@[reducible] def sadd (a b : BoundedNat bound) : BoundedNat bound :=
  wrapping_add a b

@[reducible] def ssub (a b : BoundedNat bound) : BoundedNat bound :=
  wrapping_sub a b

@[reducible] def smul (a b : BoundedNat bound) : BoundedNat bound :=
  wrapping_mul a b

@[reducible] def sadd_aborts (a b : BoundedNat bound) : Bool :=
  Bool.not (signedFits bound (signedValue a + signedValue b))

@[reducible] def ssub_aborts (a b : BoundedNat bound) : Bool :=
  Bool.not (signedFits bound (signedValue a - signedValue b))

@[reducible] def smul_aborts (a b : BoundedNat bound) : Bool :=
  Bool.not (signedFits bound (signedValue a * signedValue b))

/-- True iff `mul a b` would overflow at the given bound. -/
@[irreducible] def mul_overflows (a b : BoundedNat bound) : Bool :=
  Bool.not (Nat.blt (a.val * b.val) bound)

/-! ## Abort predicates

Move arithmetic is partial: every op below has a Lean body (total /
wrapping) plus a Bool predicate that captures the Move-level abort
condition. Stage 10's IR rewrite turns `BinOp::Add` on `UInt(N)` into
a Call to the corresponding wrapping helper; the `.aborts` companion
composes via the matching `_aborts` predicate.

Uniform `_aborts` aliases on `_overflows` / `_underflows` so the IR
side can use a single naming pattern (`<op>_aborts`).
-/

/-- Add aborts iff overflow. Alias on `add_overflows`. -/
@[reducible] def add_aborts (a b : BoundedNat bound) : Bool := add_overflows a b

/-- Sub aborts iff underflow. Alias on `sub_underflows`. -/
@[reducible] def sub_aborts (a b : BoundedNat bound) : Bool := sub_underflows a b

/-- Mul aborts iff overflow. Alias on `mul_overflows`. -/
@[reducible] def mul_aborts (a b : BoundedNat bound) : Bool := mul_overflows a b

theorem mul_overflows_eq_false_of_lt (a b : BoundedNat bound)
    (h : a.val * b.val < bound) : mul_overflows a b = false := by
  unfold mul_overflows
  rw [Bool.not_eq_false', Nat.blt_eq]
  exact h

theorem mul_overflows_eq_true_of_le (a b : BoundedNat bound)
    (h : bound ≤ a.val * b.val) : mul_overflows a b = true := by
  unfold mul_overflows
  rw [Bool.not_eq_true', ← Bool.not_eq_true, Nat.blt_eq]
  intro hlt
  exact Nat.not_lt_of_ge h hlt

theorem mul_aborts_eq_false_of_lt (a b : BoundedNat bound)
    (h : a.val * b.val < bound) : mul_aborts a b = false := by
  unfold mul_aborts
  exact mul_overflows_eq_false_of_lt a b h

theorem mul_aborts_eq_true_of_le (a b : BoundedNat bound)
    (h : bound ≤ a.val * b.val) : mul_aborts a b = true := by
  unfold mul_aborts
  exact mul_overflows_eq_true_of_le a b h

/-- Div aborts iff divisor is zero. -/
@[reducible] def div_aborts (_a b : BoundedNat bound) : Bool := Nat.beq b.val 0

/-- Mod aborts iff divisor is zero. -/
@[reducible] def mod_aborts (_a b : BoundedNat bound) : Bool := Nat.beq b.val 0

/-- Signed division/remainder additionally reject the two's-complement
`MIN / -1` overflow case. -/
@[reducible] def signed_div_overflows (a b : BoundedNat bound) : Bool :=
  decide (signedValue a = -((bound / 2 : Nat) : Int) ∧ signedValue b = -1)

@[reducible] def sdiv_aborts (a b : BoundedNat bound) : Bool :=
  Nat.beq b.val 0 || signed_div_overflows a b

@[reducible] def smod_aborts (a b : BoundedNat bound) : Bool :=
  Nat.beq b.val 0 || signed_div_overflows a b

/-- Shl aborts iff shift width meets or exceeds bitwidth. -/
@[reducible] def shl_aborts (_a : BoundedNat bound) (k : Nat) : Bool :=
  Bool.not (Nat.blt k (Nat.log2 bound))

/-- Shr aborts iff shift width meets or exceeds bitwidth. -/
@[reducible] def shr_aborts (_a : BoundedNat bound) (k : Nat) : Bool :=
  Bool.not (Nat.blt k (Nat.log2 bound))

/-- Shl (BoundedNat amount) aborts iff `k.val ≥ bitwidth`. -/
@[reducible] def shl_bounded_aborts {bound' : Nat}
    (_a : BoundedNat bound) (k : BoundedNat bound') : Bool :=
  Bool.not (Nat.blt k.val (Nat.log2 bound))

/-- Shr (BoundedNat amount) aborts iff `k.val ≥ bitwidth`. -/
@[reducible] def shr_bounded_aborts {bound' : Nat}
    (_a : BoundedNat bound) (k : BoundedNat bound') : Bool :=
  Bool.not (Nat.blt k.val (Nat.log2 bound))

@[reducible] def lshr_bounded_aborts {bound' : Nat}
    (a : BoundedNat bound) (k : BoundedNat bound') : Bool :=
  shr_bounded_aborts a k

@[reducible] def ashr_bounded_aborts {bound' : Nat}
    (a : BoundedNat bound) (k : BoundedNat bound') : Bool :=
  shr_bounded_aborts a k

/-- Cast aborts iff source value does not fit in target bound.
    Trivially `false` when widening (`bound_from ≤ bound_to`); only
    fires on narrowing. -/
@[reducible] def convert_aborts {bound_from bound_to : Nat}
    (a : BoundedNat bound_from) : Bool :=
  Bool.not (Nat.blt a.val bound_to)

/-- Division (never overflows) -/
def div (a b : BoundedNat bound) : BoundedNat bound :=
  ⟨a.val / b.val, Nat.lt_of_le_of_lt (Nat.div_le_self a.val b.val) a.property⟩

/-- Modulo. Nat's `a % 0 = a` makes this total for `b.val = 0`;
    the `mod_aborts` predicate gates the abort separately. -/
def mod (a b : BoundedNat bound) : BoundedNat bound :=
  ⟨a.val % b.val, Nat.lt_of_le_of_lt (Nat.mod_le a.val b.val) a.property⟩

/-- Signed division follows LLVM/C truncation toward zero. The abort companion
handles zero and `MIN / -1`, keeping this total Lean body harmless off-domain. -/
def sdiv (a b : BoundedNat bound) : BoundedNat bound :=
  haveI : NeZero bound := ⟨Nat.ne_of_gt (bound_pos a)⟩
  ofSigned (Int.tdiv (signedValue a) (signedValue b))

/-- Signed remainder follows LLVM/C: its sign follows the dividend. -/
def smod (a b : BoundedNat bound) : BoundedNat bound :=
  haveI : NeZero bound := ⟨Nat.ne_of_gt (bound_pos a)⟩
  ofSigned (Int.tmod (signedValue a) (signedValue b))

/-- Bitwise AND (never overflows) -/
def land (a b : BoundedNat bound) : BoundedNat bound :=
  if h : a.val &&& b.val < bound then
    ⟨a.val &&& b.val, h⟩
  else
    a  -- Fallback (should not happen as AND result is ≤ inputs)

/-- Bitwise OR -/
def lor (a b : BoundedNat bound) : BoundedNat bound :=
  if h : a.val ||| b.val < bound then
    ⟨a.val ||| b.val, h⟩
  else
    -- OR can overflow, saturate to a (which is already < bound)
    a

/-- Bitwise XOR -/
def bxor (a b : BoundedNat bound) : BoundedNat bound :=
  if h : a.val ^^^ b.val < bound then
    ⟨a.val ^^^ b.val, h⟩
  else
    -- XOR can overflow, saturate to a (which is already < bound)
    a

/-- Left shift (wrapping). Matches the `HShiftLeft` instance below.
    The `shl_aborts` predicate captures Move's `k ≥ bitwidth` abort
    separately. -/
def shiftLeft (a : BoundedNat bound) (k : Nat) : BoundedNat bound :=
  if h : bound > 0 then
    ⟨(a.val <<< k) % bound, Nat.mod_lt _ h⟩
  else
    ⟨0, bound_pos a⟩

/-- Right shift (never overflows) -/
def shiftRight (a : BoundedNat bound) (k : Nat) : BoundedNat bound :=
  ⟨a.val >>> k, Nat.lt_of_le_of_lt (by simp [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self a.val (2^k)) a.property⟩

/-- Arithmetic right shift of a two's-complement bit pattern. Euclidean
division by a positive power of two rounds negative values downward, exactly
matching sign-bit extension. -/
def ashr {bound' : Nat} (a : BoundedNat bound) (k : BoundedNat bound') :
    BoundedNat bound :=
  haveI : NeZero bound := ⟨Nat.ne_of_gt (bound_pos a)⟩
  ofSigned (Int.ediv (signedValue a) (2 ^ k.val : Nat))

/-- Complement (bitwise NOT) for power-of-2 bounds -/
def complement (a : BoundedNat bound) (_h : ∃ n, bound = 2^n) : BoundedNat bound :=
  if hc : bound - 1 - a.val < bound then
    ⟨bound - 1 - a.val, hc⟩
  else
    a  -- Fallback

/-- Convert between any two bounds (widen, truncate, or same size) -/
def convert {bound_from bound_to : Nat} [NeZero bound_to] (a : BoundedNat bound_from) : BoundedNat bound_to :=
  if h : a.val < bound_to then
    ⟨a.val, h⟩
  else if hb : bound_to > 0 then
    ⟨a.val % bound_to, Nat.mod_lt a.val hb⟩
  else
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne bound_to)⟩

/-- Convert to larger bound -/
def widen {bound bound' : Nat} [NeZero bound'] (a : BoundedNat bound) (_h : bound ≤ bound') : BoundedNat bound' :=
  convert a

/-- Truncate to smaller bound (modulo operation) -/
def truncate {bound bound' : Nat} [NeZero bound'] (a : BoundedNat bound) : BoundedNat bound' :=
  convert a

/-! ## Fixed-width bitvector composition and casts

These operations use the bound as the bit-pattern modulus.  The shared IR
represents an `iN` value as `BoundedNat (2^N)`, so extending by `bits`
multiplies the bound by `2^bits`, and concatenation uses the low operand's
bound as its radix.
-/

/-- Extract the inclusive bit slice `[high:low]`.  Shifting discards the
lower `low` bits and reduction modulo the result bound keeps exactly
`high - low + 1` bits. -/
def extract (high low : Nat) {bound : Nat} (a : BoundedNat bound) :
    BoundedNat (2 ^ (high - low + 1)) :=
  ⟨(a.val >>> low) % (2 ^ (high - low + 1)),
    Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))⟩

/-- Concatenate two bit patterns, placing `high` above `low`. -/
def concat {highBound lowBound : Nat}
    (high : BoundedNat highBound) (low : BoundedNat lowBound) :
    BoundedNat (2 ^ (Nat.log2 highBound + Nat.log2 lowBound)) :=
  ⟨(high.val * lowBound + low.val) %
      (2 ^ (Nat.log2 highBound + Nat.log2 lowBound)),
    Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))⟩

/-- Add `bits` leading zeroes to a bit pattern. -/
def zeroExtend (bits : Nat) {bound : Nat} (a : BoundedNat bound) :
    BoundedNat (bound * 2^bits) :=
  haveI : NeZero (bound * 2^bits) :=
    ⟨Nat.mul_ne_zero (Nat.ne_of_gt (bound_pos a)) (Nat.ne_of_gt (Nat.two_pow_pos bits))⟩
  convert a

/-- Add `bits` copies of the sign bit to a two's-complement bit pattern. -/
def signExtend (bits : Nat) {bound : Nat} (a : BoundedNat bound) :
    BoundedNat (bound * 2^bits) :=
  haveI : NeZero (bound * 2^bits) :=
    ⟨Nat.mul_ne_zero (Nat.ne_of_gt (bound_pos a)) (Nat.ne_of_gt (Nat.two_pow_pos bits))⟩
  ofSigned (signedValue a)

-- Instance for numeric literals (only for positive bounds)
instance {bound : Nat} (n : Nat) [NeZero bound] [h : Decidable (n < bound)] : OfNat (BoundedNat bound) n :=
  if h' : n < bound then
    ⟨⟨n, h'⟩⟩
  else if hb : bound > 0 then
    -- If literal is too large, wrap around (modulo behavior)
    ⟨⟨n % bound, Nat.mod_lt n hb⟩⟩
  else
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne bound)⟩⟩

end BoundedNat

-- Type aliases for common sizes
abbrev BoundedU8 := BoundedNat (2^8)
abbrev BoundedU16 := BoundedNat (2^16)
abbrev BoundedU32 := BoundedNat (2^32)
abbrev BoundedU64 := BoundedNat (2^64)
abbrev BoundedU128 := BoundedNat (2^128)
abbrev BoundedU256 := BoundedNat (2^256)

-- Instances for common operations
namespace BoundedNat

variable {bound : Nat}

instance : Add (BoundedNat bound) where
  add := add

instance : Sub (BoundedNat bound) where
  sub := sub

instance : Mul (BoundedNat bound) where
  mul := mul

instance : Div (BoundedNat bound) where
  div := div

instance : Mod (BoundedNat bound) where
  mod := mod

instance : AndOp (BoundedNat bound) where
  and := land

instance : OrOp (BoundedNat bound) where
  or := lor

instance : HXor (BoundedNat bound) (BoundedNat bound) (BoundedNat bound) where
  hXor := bxor

instance : HShiftLeft (BoundedNat bound) Nat (BoundedNat bound) where
  hShiftLeft a k :=
    -- Move uses modular shift left: (a <<< k) % bound
    if h : bound > 0 then
      ⟨(a.val <<< k) % bound, Nat.mod_lt _ h⟩
    else
      ⟨0, absurd a.property (by simp_all)⟩

instance : HShiftRight (BoundedNat bound) Nat (BoundedNat bound) where
  hShiftRight := shiftRight

-- Also provide instances for BoundedNat shift amounts
instance {bound' : Nat} : HShiftLeft (BoundedNat bound) (BoundedNat bound') (BoundedNat bound) where
  hShiftLeft a k :=
    -- Move uses modular shift left: (a <<< k) % bound
    if h : bound > 0 then
      ⟨(a.val <<< k.val) % bound, Nat.mod_lt _ h⟩
    else
      ⟨0, absurd a.property (by simp_all)⟩

instance {bound' : Nat} : HShiftRight (BoundedNat bound) (BoundedNat bound') (BoundedNat bound) where
  hShiftRight a k := shiftRight a k.val

-- Repr instance for debugging/printing
instance : Repr (BoundedNat bound) where
  reprPrec n _ := repr n.val

-- Zero / One instances for the BoundedNat sizes Move uses. Enumerated
-- explicitly (like the Inhabited instances below) because auto-params
-- (`:= by decide`) don't fire during typeclass instance search -- a
-- generic `instance (h : bound > 0 := by decide) : Zero (BoundedNat bound)`
-- is rejected by Lean as having "an argument that cannot be inferred".
instance : Zero (BoundedNat (2^8)) where zero := ⟨0, by omega⟩
instance : Zero (BoundedNat (2^16)) where zero := ⟨0, by omega⟩
instance : Zero (BoundedNat (2^32)) where zero := ⟨0, by omega⟩
instance : Zero (BoundedNat (2^64)) where zero := ⟨0, by omega⟩
instance : Zero (BoundedNat (2^128)) where zero := ⟨0, by omega⟩
instance : Zero (BoundedNat (2^256)) where zero := ⟨0, by omega⟩

instance : One (BoundedNat (2^8)) where one := ⟨1, by omega⟩
instance : One (BoundedNat (2^16)) where one := ⟨1, by omega⟩
instance : One (BoundedNat (2^32)) where one := ⟨1, by omega⟩
instance : One (BoundedNat (2^64)) where one := ⟨1, by omega⟩
instance : One (BoundedNat (2^128)) where one := ⟨1, by omega⟩
instance : One (BoundedNat (2^256)) where one := ⟨1, by omega⟩

-- Inhabited instances for all BoundedNat sizes used in Move.
-- We enumerate them explicitly because auto-params (by decide/omega) don't fire
-- during typeclass instance search, and `by decide` is too expensive for large bounds.
instance : Inhabited (BoundedNat (2^8)) where default := ⟨0, by omega⟩
instance : Inhabited (BoundedNat (2^16)) where default := ⟨0, by omega⟩
instance : Inhabited (BoundedNat (2^32)) where default := ⟨0, by omega⟩
instance : Inhabited (BoundedNat (2^64)) where default := ⟨0, by omega⟩
instance : Inhabited (BoundedNat (2^128)) where default := ⟨0, by omega⟩
instance : Inhabited (BoundedNat (2^256)) where default := ⟨0, by omega⟩

-- Min and Max operations
instance : Min (BoundedNat bound) where
  min a b := if a.val ≤ b.val then a else b

instance : Max (BoundedNat bound) where
  max a b := if a.val ≥ b.val then a else b

-- Ord instance for sorting
instance : Ord (BoundedNat bound) where
  compare := compare

-- Boolean equality
instance : BEq (BoundedNat bound) where
  beq a b := a.val == b.val

-- LawfulBEq instance for BoundedNat
instance : LawfulBEq (BoundedNat bound) where
  eq_of_beq := by
    intro a b h
    simp only [BEq.beq] at h
    have h_val_eq : a.val = b.val := by
      exact of_decide_eq_true h
    cases a; cases b
    simp only [mk.injEq]
    exact h_val_eq
  rfl := by
    intro a
    simp only [BEq.beq]
    rfl

-- Complement operation (bitwise NOT)
instance : Complement (BoundedNat bound) where
  complement a :=
    if h : bound > 0 then
      if hc : bound - 1 - a.val < bound then
        ⟨bound - 1 - a.val, hc⟩
      else
        a  -- Fallback (should not happen for valid values)
    else
      ⟨0, BoundedNat.bound_pos a⟩

/-! ## Value Extraction Lemmas

These lemmas allow extracting the underlying Nat value from BoundedNat operations.
They are essential for proving that implementations match specifications.
-/

/-- Extensionality: two BoundedNats are equal iff their values are equal -/
theorem ext {a b : BoundedNat bound} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only [mk.injEq]; exact h

/-- BEq equivalence to propositional equality -/
@[simp] theorem beq_eq_decide (a b : BoundedNat bound) :
    (a == b) = decide (a = b) := by
  simp only [BEq.beq, decide_eq_decide]
  constructor
  · intro h; exact ext h
  · intro h; cases h; rfl

/-- Addition extracts to wrapping Nat addition. -/
@[simp] theorem add_val (a b : BoundedNat bound) (h : bound > 0) :
    (a + b).val = (a.val + b.val) % bound := by
  show (BoundedNat.add a b).val = _
  simp only [BoundedNat.add, h, ↓reduceDIte]

/-- Addition is non-wrapping when no overflow. -/
theorem add_val_of_no_overflow (a b : BoundedNat bound)
    (h : a.val + b.val < bound) : (a + b).val = a.val + b.val := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  show (BoundedNat.add a b).val = _
  simp only [BoundedNat.add, hb, ↓reduceDIte, Nat.mod_eq_of_lt h]

/-- Subtraction extracts to Nat saturating subtraction. -/
@[simp] theorem sub_val (a b : BoundedNat bound) : (a - b).val = a.val - b.val := rfl

/-- Multiplication extracts to wrapping Nat multiplication. -/
@[simp] theorem mul_val (a b : BoundedNat bound) (h : bound > 0) :
    (a * b).val = (a.val * b.val) % bound := by
  show (BoundedNat.mul a b).val = _
  simp only [BoundedNat.mul, h, ↓reduceDIte]

/-- Multiplication is non-wrapping when no overflow. -/
theorem mul_val_of_no_overflow (a b : BoundedNat bound)
    (h : a.val * b.val < bound) : (a * b).val = a.val * b.val := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  show (BoundedNat.mul a b).val = _
  simp only [BoundedNat.mul, hb, ↓reduceDIte, Nat.mod_eq_of_lt h]

/-- Division extracts to Nat division -/
@[simp] theorem div_val (a b : BoundedNat bound) : (a / b).val = a.val / b.val := rfl

/-- Min extracts to Nat min -/
@[simp] theorem min_val (a b : BoundedNat bound) : (min a b).val = min a.val b.val := by
  change (if a.val ≤ b.val then a else b).val = min a.val b.val
  split <;> simp_all [Nat.min_eq_left, Nat.min_eq_right, Nat.le_of_not_le]

/-- Max extracts to Nat max -/
@[simp] theorem max_val (a b : BoundedNat bound) : (max a b).val = max a.val b.val := by
  change (if a.val ≥ b.val then a else b).val = max a.val b.val
  split <;> simp_all [Nat.max_eq_left, Nat.max_eq_right, Nat.le_of_not_le]

/-- Right shift with Nat extracts to Nat right shift -/
@[simp] theorem shiftRight_nat_val (a : BoundedNat bound) (k : Nat) :
    (a >>> k).val = a.val >>> k := rfl

/-- Right shift with BoundedNat extracts to Nat right shift -/
@[simp] theorem shiftRight_bounded_val {bound' : Nat} (a : BoundedNat bound) (k : BoundedNat bound') :
    (a >>> k).val = a.val >>> k.val := rfl

/-- Left shift with BoundedNat extracts to wrapped Nat left shift. -/
@[simp] theorem shiftLeft_bounded_val {bound' : Nat} (a : BoundedNat bound) (k : BoundedNat bound') :
    (a <<< k).val = (a.val <<< k.val) % bound := by
  change (if h : bound > 0 then
      (⟨(a.val <<< k.val) % bound, Nat.mod_lt _ h⟩ : BoundedNat bound)
    else
      (⟨0, absurd a.property (by simp_all)⟩ : BoundedNat bound)).val = _
  split
  · rfl
  · rename_i h
    have hb : bound = 0 := Nat.eq_zero_of_not_pos h
    exact False.elim (Nat.not_lt_zero a.val (by simpa [hb] using a.property))

/-- Convert when value fits in target bound -/
theorem convert_val_of_lt {bound_from bound_to : Nat} [NeZero bound_to] (a : BoundedNat bound_from)
    (h : a.val < bound_to) : (convert a : BoundedNat bound_to).val = a.val := by
  simp only [convert, h, ↓reduceDIte]

/-- Convert is identity when value already fits -/
theorem convert_val_eq_of_lt {bound_from bound_to : Nat} [NeZero bound_to] (a : BoundedNat bound_from)
    (h : a.val < bound_to) : (convert a : BoundedNat bound_to).val = a.val := by
  simp only [convert, h, ↓reduceDIte]

theorem convert_val_of_bound_le {bound_from bound_to : Nat} [NeZero bound_to]
    (a : BoundedNat bound_from) (h : bound_from ≤ bound_to) :
    (convert a : BoundedNat bound_to).val = a.val :=
  convert_val_of_lt a (Nat.lt_of_lt_of_le a.property h)

theorem convert_aborts_eq_false_of_bound_le {bound_from bound_to : Nat}
    (a : BoundedNat bound_from) (h : bound_from ≤ bound_to) :
    convert_aborts (bound_to := bound_to) a = false := by
  simp [convert_aborts, Nat.blt_eq, Nat.lt_of_lt_of_le a.property h]

theorem widen_val {bound_from bound_to : Nat} [NeZero bound_to] (a : BoundedNat bound_from)
    (h : bound_from ≤ bound_to) : (widen a h : BoundedNat bound_to).val = a.val := by
  exact convert_val_of_bound_le a h

theorem add_converted_val_of_bound_le {bound_a bound_b bound_to : Nat} [NeZero bound_to]
    (a : BoundedNat bound_a) (b : BoundedNat bound_b)
    (h_bound_a : bound_a ≤ bound_to) (h_bound_b : bound_b ≤ bound_to)
    (h_sum : a.val + b.val < bound_to) :
    (add (convert a) (convert b) : BoundedNat bound_to).val =
      a.val + b.val := by
  have ha := convert_val_of_bound_le a h_bound_a
  have hb := convert_val_of_bound_le b h_bound_b
  have h_no_overflow :
      (convert a : BoundedNat bound_to).val +
        (convert b : BoundedNat bound_to).val < bound_to := by
    simpa only [ha, hb] using h_sum
  have h_val := add_val_of_no_overflow
    (convert a : BoundedNat bound_to)
    (convert b : BoundedNat bound_to)
    h_no_overflow
  change
    (add (convert a) (convert b) : BoundedNat bound_to).val =
      (convert a : BoundedNat bound_to).val +
        (convert b : BoundedNat bound_to).val at h_val
  exact h_val.trans (by rw [ha, hb])

theorem mul_converted_val_of_bound_le {bound_a bound_b bound_to : Nat} [NeZero bound_to]
    (a : BoundedNat bound_a) (b : BoundedNat bound_b)
    (h_bound_a : bound_a ≤ bound_to) (h_bound_b : bound_b ≤ bound_to)
    (h_product : a.val * b.val < bound_to) :
    (mul (convert a) (convert b) : BoundedNat bound_to).val =
      a.val * b.val := by
  have ha := convert_val_of_bound_le a h_bound_a
  have hb := convert_val_of_bound_le b h_bound_b
  have h_no_overflow :
      (convert a : BoundedNat bound_to).val *
        (convert b : BoundedNat bound_to).val < bound_to := by
    simpa only [ha, hb] using h_product
  have h_val := mul_val_of_no_overflow
    (convert a : BoundedNat bound_to)
    (convert b : BoundedNat bound_to)
    h_no_overflow
  change
    (mul (convert a) (convert b) : BoundedNat bound_to).val =
      (convert a : BoundedNat bound_to).val *
        (convert b : BoundedNat bound_to).val at h_val
  exact h_val.trans (by rw [ha, hb])

/-! ## Common Bound Inequalities

Pre-computed facts about power-of-2 bounds that come up frequently in proofs.
-/

theorem bound_8_lt_64 : (2 : Nat)^8 < 2^64 := by decide
theorem bound_8_lt_128 : (2 : Nat)^8 < 2^128 := by decide
theorem bound_8_lt_256 : (2 : Nat)^8 < 2^256 := by decide
theorem bound_16_lt_64 : (2 : Nat)^16 < 2^64 := by decide
theorem bound_16_lt_128 : (2 : Nat)^16 < 2^128 := by decide
theorem bound_32_lt_64 : (2 : Nat)^32 < 2^64 := by decide
theorem bound_32_lt_128 : (2 : Nat)^32 < 2^128 := by decide
theorem bound_64_lt_128 : (2 : Nat)^64 < 2^128 := by decide
theorem bound_64_lt_256 : (2 : Nat)^64 < 2^256 := by decide
theorem bound_128_lt_256 : (2 : Nat)^128 < 2^256 := by decide
theorem bound_128_mul_128_eq_256 : (2 : Nat)^128 * 2^128 = 2^256 := by decide

theorem bound_pos_8 : (2 : Nat)^8 > 0 := by decide
theorem bound_pos_16 : (2 : Nat)^16 > 0 := by decide
theorem bound_pos_32 : (2 : Nat)^32 > 0 := by decide
theorem bound_pos_64 : (2 : Nat)^64 > 0 := by decide
theorem bound_pos_128 : (2 : Nat)^128 > 0 := by decide
theorem bound_pos_256 : (2 : Nat)^256 > 0 := by decide

end BoundedNat

/-! ## Shared Boolean/Nat Bridge Lemmas -/

theorem nat_blt_eq_true {a b : Nat} (h : a < b) :
    a.blt b = true := by
  rw [Nat.blt_eq]
  exact h

theorem nat_blt_eq_false {a b : Nat} (h : ¬ a < b) :
    a.blt b = false := by
  rw [← Bool.not_eq_true]
  rw [Nat.blt_eq]
  exact h

theorem nat_ble_eq_true {a b : Nat} (h : a ≤ b) :
    a.ble b = true := by
  rw [Nat.ble_eq]
  exact h

theorem nat_ble_eq_false {a b : Nat} (h : ¬ a ≤ b) :
    a.ble b = false := by
  rw [← Bool.not_eq_true]
  rw [Nat.ble_eq]
  exact h

theorem not_blt_eq_false_of_lt {a b : Nat} (h : a < b) :
    (!a.blt b) = false := by
  rw [Bool.not_eq_false']
  rw [Nat.blt_eq]
  exact h

theorem nat_bnot_blt_eq_true_of_le {a b : Nat} (h : b ≤ a) :
    (!a.blt b) = true := by
  have h_false := nat_blt_eq_false (Nat.not_lt_of_ge h)
  simp [h_false]

theorem nat_le_of_bnot_blt_eq_true {a b : Nat} (h : (!a.blt b) = true) :
    b ≤ a := by
  have h_false : a.blt b = false := by
    cases h_blt : a.blt b <;> simp [h_blt] at h ⊢
  have h_not_lt : ¬ a < b := by
    intro h_lt
    have h_true := nat_blt_eq_true h_lt
    rw [h_false] at h_true
    contradiction
  exact Nat.le_of_not_gt h_not_lt

theorem nat_beq_eq_true_of_eq {a b : Nat} (h : a = b) :
    a.beq b = true := by
  rw [Nat.beq_eq]
  exact h

theorem nat_beq_eq_false_of_ne {a b : Nat} (h : a ≠ b) :
    a.beq b = false := by
  rw [← Bool.not_eq_true]
  rw [Nat.beq_eq]
  exact h

theorem nat_eq_of_beq_eq_true {a b : Nat} (h : a.beq b = true) :
    a = b := by
  rw [Nat.beq_eq] at h
  exact h

theorem nat_ne_of_beq_eq_false {a b : Nat} (h : a.beq b = false) :
    a ≠ b := by
  intro h_eq
  have h_true := nat_beq_eq_true_of_eq h_eq
  rw [h] at h_true
  contradiction

theorem nat_bnot_beq_eq_true_of_ne {a b : Nat} (h : a ≠ b) :
    (!a.beq b) = true := by
  have h_false := nat_beq_eq_false_of_ne h
  simp [h_false]

theorem nat_ne_of_bnot_beq_eq_true {a b : Nat} (h : (!a.beq b) = true) :
    a ≠ b := by
  have h_false : a.beq b = false := by
    cases h_beq : a.beq b <;> simp [h_beq] at h ⊢
  exact nat_ne_of_beq_eq_false h_false

theorem nat_lt_of_blt_eq_true {a b : Nat} (h : a.blt b = true) :
    a < b := by
  rw [Nat.blt_eq] at h
  exact h

theorem not_nat_lt_of_blt_eq_false {a b : Nat} (h : a.blt b = false) :
    ¬ a < b := by
  intro hlt
  have htrue := nat_blt_eq_true hlt
  rw [h] at htrue
  contradiction

theorem nat_le_of_ble_eq_true {a b : Nat} (h : a.ble b = true) :
    a ≤ b := by
  rw [Nat.ble_eq] at h
  exact h

/-! ## Shared `BoundedNat` Arithmetic Lemmas -/

theorem boundedNat_neq_comm {bound : Nat} (a b : BoundedNat bound) :
    BoundedNat.neq a b = BoundedNat.neq b a := by
  unfold BoundedNat.neq
  by_cases h_eq : a.val = b.val
  · rw [nat_beq_eq_true_of_eq h_eq, nat_beq_eq_true_of_eq h_eq.symm]
  · have h_ne_rev : b.val ≠ a.val := by
      intro h
      exact h_eq h.symm
    rw [nat_beq_eq_false_of_ne h_eq, nat_beq_eq_false_of_ne h_ne_rev]

theorem boundedNat_le_self_true {bound : Nat} (a : BoundedNat bound) :
    BoundedNat.le a a = true := by
  unfold BoundedNat.le
  exact nat_ble_eq_true (Nat.le_refl a.val)

theorem boundedNat_lt_self_false {bound : Nat} (a : BoundedNat bound) :
    BoundedNat.lt a a = false := by
  unfold BoundedNat.lt
  exact nat_blt_eq_false (Nat.lt_irrefl a.val)

theorem boundedNat_u64_lt_zero_false (a : BoundedNat (2^64)) :
    BoundedNat.lt a (0 : BoundedNat (2^64)) = false := by
  unfold BoundedNat.lt
  have h_zero : (0 : BoundedNat (2^64)).val = 0 := by
    rfl
  rw [h_zero]
  exact nat_blt_eq_false (Nat.not_lt_zero a.val)

theorem boundedNat_sub_no_abort_of_le_nat {bound : Nat}
    (a b : BoundedNat bound) (h_le : b.val ≤ a.val) :
    BoundedNat.sub_aborts a b = false := by
  unfold BoundedNat.sub_aborts BoundedNat.sub_underflows
  exact nat_blt_eq_false (Nat.not_lt_of_ge h_le)

theorem boundedNat_sub_no_abort_of_le {bound : Nat}
    (a b : BoundedNat bound) (h_le : BoundedNat.le b a = true) :
    BoundedNat.sub_aborts a b = false := by
  apply boundedNat_sub_no_abort_of_le_nat
  unfold BoundedNat.le at h_le
  exact nat_le_of_ble_eq_true h_le

theorem boundedNat_u64_add_one_no_abort_of_lt
    (a limit : BoundedNat (2^64))
    (h_lt : BoundedNat.lt a limit = true) :
  BoundedNat.add_aborts a (1 : BoundedNat (2^64)) = false := by
  unfold BoundedNat.lt BoundedNat.add_aborts BoundedNat.add_overflows at *
  have h_lt_nat : a.val < limit.val := nat_lt_of_blt_eq_true h_lt
  have h_one : (1 : BoundedNat (2^64)).val = 1 := by
    rfl
  have h_sum_le_limit :
      a.val + (1 : BoundedNat (2^64)).val ≤ limit.val := by
    rw [h_one]
    exact Nat.succ_le_of_lt h_lt_nat
  exact not_blt_eq_false_of_lt
    (Nat.lt_of_le_of_lt h_sum_le_limit limit.property)

theorem boundedNat_u64_add_one_val_of_lt_max
    (a : BoundedNat (2^64))
    (h_lt :
      BoundedNat.lt a
        (18446744073709551615 : BoundedNat (2^64)) = true) :
    (BoundedNat.add a (1 : BoundedNat (2^64))).val = a.val + 1 := by
  unfold BoundedNat.lt at h_lt
  have h_lt_nat :
      a.val < (18446744073709551615 : BoundedNat (2^64)).val :=
    nat_lt_of_blt_eq_true h_lt
  have h_max :
      (18446744073709551615 : BoundedNat (2^64)).val =
        18446744073709551615 := by
    rfl
  have h_one : (1 : BoundedNat (2^64)).val = 1 := by
    rfl
  have h_sum_lt : a.val + (1 : BoundedNat (2^64)).val < 2^64 := by
    rw [h_one]
    change a.val + 1 < 18446744073709551616
    rw [h_max] at h_lt_nat
    omega
  unfold BoundedNat.add
  split
  · rw [h_one] at h_sum_lt
    exact Nat.mod_eq_of_lt h_sum_lt
  · contradiction

theorem boundedNat_u64_add_one_aborts_of_not_lt_max
    (a : BoundedNat (2^64))
    (h_not_lt :
      BoundedNat.lt a
        (18446744073709551615 : BoundedNat (2^64)) = false) :
    BoundedNat.add_aborts a (1 : BoundedNat (2^64)) = true := by
  unfold BoundedNat.lt at h_not_lt
  have h_not_lt_nat :
      ¬ a.val < (18446744073709551615 : BoundedNat (2^64)).val :=
    not_nat_lt_of_blt_eq_false h_not_lt
  unfold BoundedNat.add_aborts BoundedNat.add_overflows
  have h_max_val :
      (18446744073709551615 : BoundedNat (2^64)).val =
        18446744073709551615 := by
    rfl
  have h_one : (1 : BoundedNat (2^64)).val = 1 := by
    rfl
  have h_ge_max : 18446744073709551615 ≤ a.val := by
    rw [← h_max_val]
    exact Nat.le_of_not_gt h_not_lt_nat
  rw [h_one]
  have h_pow : 18446744073709551615 + 1 = 2^64 := by
    rfl
  have h_sum_ge : 18446744073709551615 + 1 ≤ a.val + 1 :=
    Nat.add_le_add_right h_ge_max 1
  rw [Bool.not_eq_true']
  exact nat_blt_eq_false (Nat.not_lt_of_ge (by
    simpa [h_pow] using h_sum_ge))

@[simp]
theorem boundedNat_u64_add_one_aborts_eq_not_lt_max
    (a : BoundedNat (2^64)) :
    BoundedNat.add_aborts a (1 : BoundedNat (2^64)) =
      !BoundedNat.lt a
        (18446744073709551615 : BoundedNat (2^64)) := by
  cases h_lt :
      BoundedNat.lt a
        (18446744073709551615 : BoundedNat (2^64))
  · rw [boundedNat_u64_add_one_aborts_of_not_lt_max a h_lt]
    simp [h_lt]
  · rw [boundedNat_u64_add_one_no_abort_of_lt
      a (18446744073709551615 : BoundedNat (2^64)) h_lt]
    simp [h_lt]

@[simp]
theorem boundedNat_u64_add_one_overflow_iff_not_lt_max
    (a : BoundedNat (2^64)) :
    (18446744073709551616 ≤ a.val + (1 : BoundedNat (2^64)).val) ↔
      ¬ a.val < (18446744073709551615 : BoundedNat (2^64)).val := by
  have h_one : (1 : BoundedNat (2^64)).val = 1 := by
    rfl
  have h_max :
      (18446744073709551615 : BoundedNat (2^64)).val =
        18446744073709551615 := by
    rfl
  constructor
  · intro h_over h_lt
    rw [h_one] at h_over
    rw [h_max] at h_lt
    omega
  · intro h_not_lt
    have h_bound : a.val < 18446744073709551616 := by
      simpa using a.property
    have h_ge : 18446744073709551615 ≤ a.val := by
      rw [← h_max]
      exact Nat.le_of_not_gt h_not_lt
    rw [h_one]
    omega

@[simp]
theorem boundedNat_u128_max_val :
    (340282366920938463463374607431768211455 : BoundedNat (2^128)).val =
      340282366920938463463374607431768211455 := by
  rfl

@[simp]
theorem boundedNat_u128_add_one_aborts_eq_not_lt_max
    (a : BoundedNat (2^128)) :
    BoundedNat.add_aborts a (1 : BoundedNat (2^128)) =
      !BoundedNat.lt a
        (340282366920938463463374607431768211455 : BoundedNat (2^128)) := by
  unfold BoundedNat.add_aborts BoundedNat.add_overflows BoundedNat.lt
  have h_one : (1 : BoundedNat (2^128)).val = 1 := by
    rfl
  have h_max :
      (340282366920938463463374607431768211455 : BoundedNat (2^128)).val =
        340282366920938463463374607431768211455 := by
    rfl
  have h_max_succ :
      340282366920938463463374607431768211455 + 1 = 2^128 := by
    rfl
  rw [h_one, h_max]
  by_cases h_lt :
      a.val < 340282366920938463463374607431768211455
  · have h_sum_lt : a.val + 1 < 2^128 := by
      omega
    have h_sum_bool :
        (a.val + 1).blt (2^128) = true :=
      nat_blt_eq_true h_sum_lt
    have h_lt_bool :
        a.val.blt 340282366920938463463374607431768211455 = true :=
      nat_blt_eq_true h_lt
    rw [h_sum_bool, h_lt_bool]
  · have h_over : a.val + 1 ≥ 2^128 := by
      omega
    have h_lt_bool :
        a.val.blt 340282366920938463463374607431768211455 = false :=
      nat_blt_eq_false h_lt
    have h_sum_bool :
        (a.val + 1).blt (2^128) = false :=
      nat_blt_eq_false (Nat.not_lt_of_ge h_over)
    rw [h_sum_bool, h_lt_bool]

@[simp]
theorem boundedNat_u128_add_one_blt_bound_eq_lt_max
    (a : BoundedNat (2^128)) :
    (a.val + (1 : BoundedNat (2^128)).val).blt (2^128) =
      a.val.blt
        (340282366920938463463374607431768211455 : BoundedNat (2^128)).val := by
  have h_one : (1 : BoundedNat (2^128)).val = 1 := by
    rfl
  have h_max :
      (340282366920938463463374607431768211455 : BoundedNat (2^128)).val =
        340282366920938463463374607431768211455 := by
    rfl
  have h_pow : (2^128 : Nat) =
      340282366920938463463374607431768211456 := by
    rfl
  rw [h_one, h_max]
  by_cases h_lt : a.val < 340282366920938463463374607431768211455
  · have h_sum_lt : a.val + 1 < 2^128 := by
      omega
    rw [nat_blt_eq_true h_sum_lt, nat_blt_eq_true h_lt]
  · have h_sum_ge : 2^128 ≤ a.val + 1 := by
      have h_bound := a.property
      change a.val < 2^128 at h_bound
      omega
    rw [nat_blt_eq_false (Nat.not_lt_of_ge h_sum_ge),
      nat_blt_eq_false h_lt]

@[simp]
theorem boundedNat_u128_add_one_blt_raw_bound_eq_lt_max
    (a : BoundedNat (2^128)) :
    (a.val + (1 : BoundedNat (2^128)).val).blt
        340282366920938463463374607431768211456 =
      a.val.blt
        (340282366920938463463374607431768211455 : BoundedNat (2^128)).val := by
  have h_pow : (2^128 : Nat) =
      340282366920938463463374607431768211456 := by
    rfl
  rw [← h_pow]
  exact boundedNat_u128_add_one_blt_bound_eq_lt_max a

@[simp]
theorem boundedNat_u128_add_one_overflows_iff_not_lt_max_val
    (a : BoundedNat (2^128)) :
    (340282366920938463463374607431768211456 ≤
        a.val + (1 : BoundedNat (2^128)).val) ↔
      ¬ a.val < 340282366920938463463374607431768211455 := by
  have h_one : (1 : BoundedNat (2^128)).val = 1 := by
    rfl
  rw [h_one]
  constructor
  · intro h_over h_lt
    omega
  · intro h_not_lt
    omega

theorem boundedNat_u128_add_one_lt_max_of_lt_pred
    (a : BoundedNat (2^128))
    (h_lt :
      BoundedNat.lt a
        (340282366920938463463374607431768211454 : BoundedNat (2^128)) = true) :
    BoundedNat.lt (BoundedNat.add a (1 : BoundedNat (2^128)))
      (340282366920938463463374607431768211455 : BoundedNat (2^128)) = true := by
  unfold BoundedNat.lt at h_lt ⊢
  have h_one : (1 : BoundedNat (2^128)).val = 1 := by
    rfl
  have h_pred :
      (340282366920938463463374607431768211454 : BoundedNat (2^128)).val =
        340282366920938463463374607431768211454 := by
    rfl
  have h_max :
      (340282366920938463463374607431768211455 : BoundedNat (2^128)).val =
        340282366920938463463374607431768211455 := by
    rfl
  have h_bound_pos : 2^128 > 0 := by
    decide
  have h_add_val :
      (BoundedNat.add a (1 : BoundedNat (2^128))).val = a.val + 1 := by
    have h_no_wrap : a.val + 1 < 2^128 := by
      have h_lt_nat : a.val < 340282366920938463463374607431768211454 := by
        simpa [h_pred] using h_lt
      have h_pow :
          (2^128 : Nat) = 340282366920938463463374607431768211456 := by
        rfl
      omega
    unfold BoundedNat.add
    rw [dif_pos h_bound_pos]
    simp [h_one, Nat.mod_eq_of_lt h_no_wrap]
  have h_lt_nat : a.val < 340282366920938463463374607431768211454 := by
    simpa [h_pred] using h_lt
  rw [h_add_val, h_max]
  exact nat_blt_eq_true (by omega)

theorem boundedNat_u128_add_one_aborts_of_lt_max_and_not_lt_pred
    (a : BoundedNat (2^128))
    (h_lt_max :
      BoundedNat.lt a
        (340282366920938463463374607431768211455 : BoundedNat (2^128)) = true)
    (h_not_lt_pred :
      BoundedNat.lt a
        (340282366920938463463374607431768211454 : BoundedNat (2^128)) = false) :
    BoundedNat.add_aborts (BoundedNat.add a (1 : BoundedNat (2^128)))
      (1 : BoundedNat (2^128)) = true := by
  unfold BoundedNat.lt at h_lt_max h_not_lt_pred
  have h_one : (1 : BoundedNat (2^128)).val = 1 := by
    rfl
  have h_pred :
      (340282366920938463463374607431768211454 : BoundedNat (2^128)).val =
        340282366920938463463374607431768211454 := by
    rfl
  have h_max :
      (340282366920938463463374607431768211455 : BoundedNat (2^128)).val =
        340282366920938463463374607431768211455 := by
    rfl
  have h_bound_pos : 2^128 > 0 := by
    decide
  have h_a_lt_max : a.val < 340282366920938463463374607431768211455 := by
    have h_bool :
        a.val.blt 340282366920938463463374607431768211455 = true := by
      simpa [h_max] using h_lt_max
    exact nat_lt_of_blt_eq_true h_bool
  have h_a_not_lt_pred :
      ¬ a.val < 340282366920938463463374607431768211454 := by
    have h_bool :
        a.val.blt 340282366920938463463374607431768211454 = false := by
      simpa [h_pred] using h_not_lt_pred
    exact not_nat_lt_of_blt_eq_false h_bool
  have h_a_eq_pred : a.val = 340282366920938463463374607431768211454 := by
    omega
  have h_add_one_lt : a.val + 1 < 2^128 := by
    have h_pow :
        (2^128 : Nat) = 340282366920938463463374607431768211456 := by
      rfl
    omega
  have h_add_one_val :
      (BoundedNat.add a (1 : BoundedNat (2^128))).val =
        340282366920938463463374607431768211455 := by
    unfold BoundedNat.add
    rw [dif_pos h_bound_pos]
    simp [h_one, h_a_eq_pred, Nat.mod_eq_of_lt h_add_one_lt]
  rw [boundedNat_u128_add_one_aborts_eq_not_lt_max]
  have h_inner_not_lt :
      BoundedNat.lt (BoundedNat.add a (1 : BoundedNat (2^128)))
        (340282366920938463463374607431768211455 : BoundedNat (2^128)) =
          false := by
    unfold BoundedNat.lt
    rw [h_add_one_val, h_max]
    exact nat_blt_eq_false (by omega)
  simp [h_inner_not_lt]

theorem boundedNat_u128_add_one_add_one_eq_add_two_of_lt_pred
    (a : BoundedNat (2^128))
    (h_lt :
      BoundedNat.lt a
        (340282366920938463463374607431768211454 : BoundedNat (2^128)) = true) :
    BoundedNat.add (BoundedNat.add a (1 : BoundedNat (2^128)))
        (1 : BoundedNat (2^128)) =
      BoundedNat.add a (2 : BoundedNat (2^128)) := by
  unfold BoundedNat.lt at h_lt
  have h_one : (1 : BoundedNat (2^128)).val = 1 := by
    rfl
  have h_two : (2 : BoundedNat (2^128)).val = 2 := by
    rfl
  have h_pred :
      (340282366920938463463374607431768211454 : BoundedNat (2^128)).val =
        340282366920938463463374607431768211454 := by
    rfl
  have h_bound_pos : 2^128 > 0 := by
    decide
  have h_lt_nat : a.val < 340282366920938463463374607431768211454 := by
    simpa [h_pred] using h_lt
  have h_add_one_lt : a.val + 1 < 2^128 := by
    have h_pow :
        (2^128 : Nat) = 340282366920938463463374607431768211456 := by
      rfl
    omega
  have h_add_two_lt : a.val + 2 < 2^128 := by
    have h_pow :
        (2^128 : Nat) = 340282366920938463463374607431768211456 := by
      rfl
    omega
  have h_add_one_val :
      (BoundedNat.add a (1 : BoundedNat (2^128))).val = a.val + 1 := by
    unfold BoundedNat.add
    rw [dif_pos h_bound_pos]
    simp [h_one, Nat.mod_eq_of_lt h_add_one_lt]
  have h_outer_lt :
      (BoundedNat.add a (1 : BoundedNat (2^128))).val +
          (1 : BoundedNat (2^128)).val < 2^128 := by
    rw [h_add_one_val, h_one]
    omega
  apply BoundedNat.ext
  unfold BoundedNat.add
  rw [dif_pos h_bound_pos]
  rw [dif_pos h_bound_pos]
  simp [h_add_one_val, h_one, h_two,
    Nat.mod_eq_of_lt h_outer_lt, Nat.mod_eq_of_lt h_add_two_lt]

/-! ## Compat bridge surface (hoisted from the client proof-repair kits)

Bridge vocabulary between the Bool shapes of the BoundedNat comparators /
abort predicates (`Nat.blt` / `Nat.ble` / `Nat.beq`) and the `decide`-shaped
idioms proofs are naturally written in. Hoisted verbatim from the
integer-mate `IMcompat` and move-stl `SLcompat` client kits (which had
independently grown identical copies); names preserved so client corpora
migrate by dropping the kit prefix. All lemmas are sorry-free and
axiom-clean; `large_to_lit` is itself axiom-free but its `h` argument is
typically a generated `large_uint_*_val` companion proved by
`native_decide`, so USES of it carry `Lean.ofReduceBool` -- accepted policy
for large_uint consumers. -/

section CompatBridges

theorem bool_eq_decide_of_iff {b : Bool} {p : Prop} [Decidable p]
    (h : b = true ↔ p) : b = decide p := by
  by_cases hp : p
  · rw [decide_eq_true hp]
    exact h.mpr hp
  · rw [decide_eq_false hp]
    cases hb : b
    · rfl
    · exact absurd (h.mp hb) hp

theorem bool_eq_false_iff_not_of_iff {b : Bool} {p : Prop}
    (h : b = true ↔ p) : b = false ↔ ¬ p := by
  constructor
  · intro hb hp
    rw [h.mpr hp] at hb
    cases hb
  · intro hp
    cases hb : b
    · rfl
    · exact absurd (h.mp hb) hp

theorem nat_blt_decide (a b : Nat) :
    a.blt b = decide (a < b) :=
  bool_eq_decide_of_iff (by rw [Nat.blt_eq])

theorem nat_ble_decide (a b : Nat) :
    a.ble b = decide (a ≤ b) :=
  bool_eq_decide_of_iff (by rw [Nat.ble_eq])

theorem nat_beq_decide (a b : Nat) :
    a.beq b = decide (a = b) :=
  bool_eq_decide_of_iff (by rw [Nat.beq_eq])

theorem nat_blt_eq_false_iff_le (a b : Nat) :
    a.blt b = false ↔ b ≤ a :=
  (bool_eq_false_iff_not_of_iff (by rw [Nat.blt_eq])).trans Nat.not_lt

theorem nat_ble_eq_false_iff_lt (a b : Nat) :
    a.ble b = false ↔ b < a :=
  (bool_eq_false_iff_not_of_iff (by rw [Nat.ble_eq])).trans Nat.not_le

theorem nat_beq_eq_false_iff_ne (a b : Nat) :
    a.beq b = false ↔ a ≠ b :=
  bool_eq_false_iff_not_of_iff (by rw [Nat.beq_eq])

variable {bound : Nat}

-- comparator true-iffs
theorem bn_lt_iff (a b : BoundedNat bound) :
    BoundedNat.lt a b = true ↔ a.val < b.val :=
  ⟨nat_lt_of_blt_eq_true, nat_blt_eq_true⟩

theorem bn_le_iff (a b : BoundedNat bound) :
    BoundedNat.le a b = true ↔ a.val ≤ b.val :=
  ⟨nat_le_of_ble_eq_true, nat_ble_eq_true⟩

theorem bn_gt_iff (a b : BoundedNat bound) :
    BoundedNat.gt a b = true ↔ b.val < a.val :=
  ⟨nat_lt_of_blt_eq_true, nat_blt_eq_true⟩

theorem bn_gt_iff_gt (a b : BoundedNat bound) :
    BoundedNat.gt a b = true ↔ a.val > b.val :=
  bn_gt_iff a b

theorem bn_ge_iff (a b : BoundedNat bound) :
    BoundedNat.ge a b = true ↔ b.val ≤ a.val :=
  ⟨nat_le_of_bnot_blt_eq_true, nat_bnot_blt_eq_true_of_le⟩

theorem bn_ge_iff_ge (a b : BoundedNat bound) :
    BoundedNat.ge a b = true ↔ a.val ≥ b.val :=
  bn_ge_iff a b

theorem bn_eq_iff (a b : BoundedNat bound) :
    BoundedNat.eq a b = true ↔ a.val = b.val :=
  ⟨nat_eq_of_beq_eq_true, nat_beq_eq_true_of_eq⟩

theorem bn_neq_iff (a b : BoundedNat bound) :
    BoundedNat.neq a b = true ↔ a.val ≠ b.val :=
  ⟨nat_ne_of_bnot_beq_eq_true, nat_bnot_beq_eq_true_of_ne⟩

-- val-injectivity + eq-to-propositional-equality
theorem bn_val_inj (a b : BoundedNat bound) : a.val = b.val ↔ a = b :=
  ⟨BoundedNat.ext, fun h => h ▸ rfl⟩

/-- The DECODE orientation of `bn_val_inj`. `simp` uses an iff left to right, and the
direction the proofs take is from a BoundedNat equality DOWN to a `.val` equality --
`apply BoundedNat.ext`, 182 of the 224 uses. `bn_val_inj` is stated the other way, and
`BoundedNat.ext` itself is an implication, which `simp` cannot use as a rewrite on the
equality face at all.

CITATION-ONLY, and deliberately so: this must NOT carry `@[simp]` or `@[move_effect]`.
Ambient, it rewrites a hypothesis `h : a = b` to `a.val = b.val` BEFORE `simp_all` can use
it to substitute `a := b`, which is a strictly worse normal form -- measured on the
momentum overlay, two replays whose context carried `product = (0 : BoundedNat (2^256))`
went from closing to exhausting an 8,000,000-heartbeat budget. Use it by name, or from a
goal-only rule channel. -/
theorem bn_eq_iff_val_eq (a b : BoundedNat bound) : a = b ↔ a.val = b.val :=
  (bn_val_inj a b).symm

theorem bn_eq_iff_eq (a b : BoundedNat bound) :
    BoundedNat.eq a b = true ↔ a = b :=
  (bn_eq_iff a b).trans (bn_val_inj a b)

theorem bn_eq_refl (a : BoundedNat bound) : BoundedNat.eq a a = true :=
  (bn_eq_iff a a).mpr rfl

-- decide-shape restorers
theorem bn_lt_decide (a b : BoundedNat bound) :
    BoundedNat.lt a b = decide (a.val < b.val) :=
  bool_eq_decide_of_iff (bn_lt_iff a b)

theorem bn_le_decide (a b : BoundedNat bound) :
    BoundedNat.le a b = decide (a.val ≤ b.val) :=
  bool_eq_decide_of_iff (bn_le_iff a b)

theorem bn_gt_decide (a b : BoundedNat bound) :
    BoundedNat.gt a b = decide (a.val > b.val) :=
  bool_eq_decide_of_iff (bn_gt_iff_gt a b)

theorem bn_gt_decide_lt (a b : BoundedNat bound) :
    BoundedNat.gt a b = decide (b.val < a.val) :=
  bool_eq_decide_of_iff (bn_gt_iff a b)

theorem bn_ge_decide (a b : BoundedNat bound) :
    BoundedNat.ge a b = decide (a.val ≥ b.val) :=
  bool_eq_decide_of_iff (bn_ge_iff_ge a b)

theorem bn_ge_decide_le (a b : BoundedNat bound) :
    BoundedNat.ge a b = decide (b.val ≤ a.val) :=
  bool_eq_decide_of_iff (bn_ge_iff a b)

theorem bn_eq_decide (a b : BoundedNat bound) :
    BoundedNat.eq a b = decide (a.val = b.val) :=
  bool_eq_decide_of_iff (bn_eq_iff a b)

theorem bn_neq_decide (a b : BoundedNat bound) :
    BoundedNat.neq a b = decide (a.val ≠ b.val) :=
  bool_eq_decide_of_iff (bn_neq_iff a b)

-- false-forms: ¬-shape first, then positive shape
theorem bn_lt_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.lt a b = false ↔ ¬ a.val < b.val :=
  bool_eq_false_iff_not_of_iff (bn_lt_iff a b)

theorem bn_lt_eq_false_iff_le (a b : BoundedNat bound) :
    BoundedNat.lt a b = false ↔ b.val ≤ a.val :=
  (bn_lt_eq_false_iff a b).trans Nat.not_lt

theorem bn_le_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.le a b = false ↔ ¬ a.val ≤ b.val :=
  bool_eq_false_iff_not_of_iff (bn_le_iff a b)

theorem bn_le_eq_false_iff_lt (a b : BoundedNat bound) :
    BoundedNat.le a b = false ↔ b.val < a.val :=
  (bn_le_eq_false_iff a b).trans Nat.not_le

theorem bn_gt_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.gt a b = false ↔ ¬ b.val < a.val :=
  bool_eq_false_iff_not_of_iff (bn_gt_iff a b)

theorem bn_gt_eq_false_iff_le (a b : BoundedNat bound) :
    BoundedNat.gt a b = false ↔ a.val ≤ b.val :=
  (bn_gt_eq_false_iff a b).trans Nat.not_lt

theorem bn_ge_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.ge a b = false ↔ a.val < b.val :=
  (bool_eq_false_iff_not_of_iff (bn_ge_iff a b)).trans Nat.not_le

theorem bn_eq_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.eq a b = false ↔ a.val ≠ b.val :=
  bool_eq_false_iff_not_of_iff (bn_eq_iff a b)

theorem bn_neq_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.neq a b = false ↔ a.val = b.val :=
  (bool_eq_false_iff_not_of_iff (bn_neq_iff a b)).trans Decidable.not_not

-- abort-predicate bridges: sub aborts iff underflow
theorem bn_sub_underflows_iff (a b : BoundedNat bound) :
    BoundedNat.sub_underflows a b = true ↔ a.val < b.val :=
  ⟨nat_lt_of_blt_eq_true, nat_blt_eq_true⟩

theorem bn_sub_aborts_iff (a b : BoundedNat bound) :
    BoundedNat.sub_aborts a b = true ↔ a.val < b.val :=
  bn_sub_underflows_iff a b

theorem bn_sub_underflows_decide (a b : BoundedNat bound) :
    BoundedNat.sub_underflows a b = decide (a.val < b.val) :=
  bool_eq_decide_of_iff (bn_sub_underflows_iff a b)

theorem bn_sub_aborts_decide (a b : BoundedNat bound) :
    BoundedNat.sub_aborts a b = decide (a.val < b.val) :=
  bn_sub_underflows_decide a b

theorem bn_sub_aborts_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.sub_aborts a b = false ↔ ¬ a.val < b.val :=
  bool_eq_false_iff_not_of_iff (bn_sub_aborts_iff a b)

theorem bn_sub_aborts_eq_false_iff_le (a b : BoundedNat bound) :
    BoundedNat.sub_aborts a b = false ↔ b.val ≤ a.val :=
  (bn_sub_aborts_eq_false_iff a b).trans Nat.not_lt

-- add: aborts iff overflow
theorem bn_add_overflows_iff (a b : BoundedNat bound) :
    BoundedNat.add_overflows a b = true ↔ a.val + b.val ≥ bound :=
  ⟨nat_le_of_bnot_blt_eq_true, nat_bnot_blt_eq_true_of_le⟩

theorem bn_add_aborts_iff (a b : BoundedNat bound) :
    BoundedNat.add_aborts a b = true ↔ a.val + b.val ≥ bound :=
  bn_add_overflows_iff a b

theorem bn_add_overflows_decide (a b : BoundedNat bound) :
    BoundedNat.add_overflows a b = decide (a.val + b.val ≥ bound) :=
  bool_eq_decide_of_iff (bn_add_overflows_iff a b)

theorem bn_add_aborts_decide (a b : BoundedNat bound) :
    BoundedNat.add_aborts a b = decide (a.val + b.val ≥ bound) :=
  bn_add_overflows_decide a b

theorem bn_add_aborts_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.add_aborts a b = false ↔ a.val + b.val < bound :=
  (bool_eq_false_iff_not_of_iff (bn_add_aborts_iff a b)).trans Nat.not_le

-- mul: aborts iff overflow. mul_overflows is @[irreducible]; route through
-- mul_overflows_eq_false_of_lt / _eq_true_of_le above.
theorem bn_mul_overflows_iff (a b : BoundedNat bound) :
    BoundedNat.mul_overflows a b = true ↔ a.val * b.val ≥ bound := by
  constructor
  · intro h
    by_cases hlt : a.val * b.val < bound
    · rw [BoundedNat.mul_overflows_eq_false_of_lt a b hlt] at h
      cases h
    · exact Nat.le_of_not_lt hlt
  · intro h
    exact BoundedNat.mul_overflows_eq_true_of_le a b h

theorem bn_mul_aborts_iff (a b : BoundedNat bound) :
    BoundedNat.mul_aborts a b = true ↔ a.val * b.val ≥ bound :=
  bn_mul_overflows_iff a b

theorem bn_mul_overflows_decide (a b : BoundedNat bound) :
    BoundedNat.mul_overflows a b = decide (a.val * b.val ≥ bound) :=
  bool_eq_decide_of_iff (bn_mul_overflows_iff a b)

theorem bn_mul_aborts_decide (a b : BoundedNat bound) :
    BoundedNat.mul_aborts a b = decide (a.val * b.val ≥ bound) :=
  bn_mul_overflows_decide a b

theorem bn_mul_aborts_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.mul_aborts a b = false ↔ a.val * b.val < bound :=
  (bool_eq_false_iff_not_of_iff (bn_mul_aborts_iff a b)).trans Nat.not_le

-- div / mod: abort iff divisor zero
theorem bn_div_aborts_iff (a b : BoundedNat bound) :
    BoundedNat.div_aborts a b = true ↔ b.val = 0 :=
  ⟨nat_eq_of_beq_eq_true, nat_beq_eq_true_of_eq⟩

theorem bn_div_aborts_decide (a b : BoundedNat bound) :
    BoundedNat.div_aborts a b = decide (b.val = 0) :=
  bool_eq_decide_of_iff (bn_div_aborts_iff a b)

theorem bn_div_aborts_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.div_aborts a b = false ↔ b.val ≠ 0 :=
  bool_eq_false_iff_not_of_iff (bn_div_aborts_iff a b)

theorem bn_mod_aborts_iff (a b : BoundedNat bound) :
    BoundedNat.mod_aborts a b = true ↔ b.val = 0 :=
  bn_div_aborts_iff a b

theorem bn_mod_aborts_decide (a b : BoundedNat bound) :
    BoundedNat.mod_aborts a b = decide (b.val = 0) :=
  bn_div_aborts_decide a b

theorem bn_mod_aborts_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.mod_aborts a b = false ↔ b.val ≠ 0 :=
  bn_div_aborts_eq_false_iff a b

-- shifts (Nat amount)
theorem bn_shl_aborts_iff (a : BoundedNat bound) (k : Nat) :
    BoundedNat.shl_aborts a k = true ↔ k ≥ Nat.log2 bound :=
  ⟨nat_le_of_bnot_blt_eq_true, nat_bnot_blt_eq_true_of_le⟩

theorem bn_shl_aborts_decide (a : BoundedNat bound) (k : Nat) :
    BoundedNat.shl_aborts a k = decide (k ≥ Nat.log2 bound) :=
  bool_eq_decide_of_iff (bn_shl_aborts_iff a k)

theorem bn_shr_aborts_iff (a : BoundedNat bound) (k : Nat) :
    BoundedNat.shr_aborts a k = true ↔ k ≥ Nat.log2 bound :=
  bn_shl_aborts_iff a k

theorem bn_shr_aborts_decide (a : BoundedNat bound) (k : Nat) :
    BoundedNat.shr_aborts a k = decide (k ≥ Nat.log2 bound) :=
  bn_shl_aborts_decide a k

-- shifts (BoundedNat amount)
theorem bn_shl_bounded_aborts_iff {bound' : Nat}
    (a : BoundedNat bound) (k : BoundedNat bound') :
    BoundedNat.shl_bounded_aborts a k = true ↔ k.val ≥ Nat.log2 bound :=
  ⟨nat_le_of_bnot_blt_eq_true, nat_bnot_blt_eq_true_of_le⟩

theorem bn_shl_bounded_aborts_decide {bound' : Nat}
    (a : BoundedNat bound) (k : BoundedNat bound') :
    BoundedNat.shl_bounded_aborts a k = decide (k.val ≥ Nat.log2 bound) :=
  bool_eq_decide_of_iff (bn_shl_bounded_aborts_iff a k)

theorem bn_shl_bounded_aborts_eq_false_iff {bound' : Nat}
    (a : BoundedNat bound) (k : BoundedNat bound') :
    BoundedNat.shl_bounded_aborts a k = false ↔ k.val < Nat.log2 bound :=
  (bool_eq_false_iff_not_of_iff (bn_shl_bounded_aborts_iff a k)).trans
    Nat.not_le

theorem bn_shr_bounded_aborts_iff {bound' : Nat}
    (a : BoundedNat bound) (k : BoundedNat bound') :
    BoundedNat.shr_bounded_aborts a k = true ↔ k.val ≥ Nat.log2 bound :=
  bn_shl_bounded_aborts_iff a k

theorem bn_shr_bounded_aborts_decide {bound' : Nat}
    (a : BoundedNat bound) (k : BoundedNat bound') :
    BoundedNat.shr_bounded_aborts a k = decide (k.val ≥ Nat.log2 bound) :=
  bn_shl_bounded_aborts_decide a k

theorem bn_shr_bounded_aborts_eq_false_iff {bound' : Nat}
    (a : BoundedNat bound) (k : BoundedNat bound') :
    BoundedNat.shr_bounded_aborts a k = false ↔ k.val < Nat.log2 bound :=
  bn_shl_bounded_aborts_eq_false_iff a k

-- convert (cast): aborts iff value does not fit the target bound
theorem bn_convert_aborts_iff {bound_from bound_to : Nat}
    (a : BoundedNat bound_from) :
    BoundedNat.convert_aborts (bound_to := bound_to) a = true
      ↔ a.val ≥ bound_to :=
  ⟨nat_le_of_bnot_blt_eq_true, nat_bnot_blt_eq_true_of_le⟩

theorem bn_convert_aborts_decide {bound_from bound_to : Nat}
    (a : BoundedNat bound_from) :
    BoundedNat.convert_aborts (bound_to := bound_to) a
      = decide (a.val ≥ bound_to) :=
  bool_eq_decide_of_iff (bn_convert_aborts_iff a)

theorem bn_convert_aborts_eq_false_iff {bound_from bound_to : Nat}
    (a : BoundedNat bound_from) :
    BoundedNat.convert_aborts (bound_to := bound_to) a = false
      ↔ a.val < bound_to :=
  (bool_eq_false_iff_not_of_iff (bn_convert_aborts_iff a)).trans Nat.not_le

theorem bn_add_val_of_no_abort (a b : BoundedNat bound)
    (h : BoundedNat.add_aborts a b = false) :
    (BoundedNat.add a b).val = a.val + b.val :=
  BoundedNat.add_val_of_no_overflow a b
    ((bn_add_aborts_eq_false_iff a b).mp h)

theorem bn_mul_val_of_no_abort (a b : BoundedNat bound)
    (h : BoundedNat.mul_aborts a b = false) :
    (BoundedNat.mul a b).val = a.val * b.val :=
  BoundedNat.mul_val_of_no_overflow a b
    ((bn_mul_aborts_eq_false_iff a b).mp h)

theorem bn_convert_val_of_no_abort {bound_from bound_to : Nat} [NeZero bound_to]
    (a : BoundedNat bound_from)
    (h : BoundedNat.convert_aborts (bound_to := bound_to) a = false) :
    (BoundedNat.convert a : BoundedNat bound_to).val = a.val :=
  BoundedNat.convert_val_of_lt a
    ((bn_convert_aborts_eq_false_iff a).mp h)

-- generic constant-to-literal rewriter for the hoisted large_uint opaques
theorem large_to_lit {v : Nat} {c : BoundedNat bound} (h : c.val = v)
    {l : BoundedNat bound} (hl : l.val = v) : c = l :=
  BoundedNat.ext (h.trans hl.symm)

-- literal-val conveniences (rfl-provable; named for simp sets)
theorem bn_zero_val_u64 : (0 : BoundedNat (2^64)).val = 0 := rfl
theorem bn_one_val_u64 : (1 : BoundedNat (2^64)).val = 1 := rfl
theorem bn_two_val_u64 : (2 : BoundedNat (2^64)).val = 2 := rfl

end CompatBridges

-- derived-BEq bridges for [DecidableEq] types (instBEqOfDecidableEq route)
theorem deq_beq_def {α : Type} [DecidableEq α] (a b : α) :
    (a == b) = decide (a = b) := rfl

theorem deq_beq_true_iff {α : Type} [DecidableEq α] (a b : α) :
    (a == b) = true ↔ a = b := by
  rw [deq_beq_def]
  exact ⟨of_decide_eq_true, decide_eq_true⟩

theorem deq_beq_false_iff {α : Type} [DecidableEq α] (a b : α) :
    (a == b) = false ↔ a ≠ b :=
  bool_eq_false_iff_not_of_iff (deq_beq_true_iff a b)

theorem deq_beq_refl {α : Type} [DecidableEq α] (a : α) : (a == a) = true :=
  (deq_beq_true_iff a a).mpr rfl

theorem deq_eq_of_beq {α : Type} [DecidableEq α] {a b : α}
    (h : (a == b) = true) : a = b :=
  (deq_beq_true_iff a b).mp h

theorem deq_beq_of_eq {α : Type} [DecidableEq α] {a b : α}
    (h : a = b) : (a == b) = true :=
  (deq_beq_true_iff a b).mpr h

-- List-BEq step equations
theorem list_beq_nil_nil {α : Type} [BEq α] :
    (([] : List α) == ([] : List α)) = true := rfl

theorem list_beq_nil_cons {α : Type} [BEq α] (b : α) (l : List α) :
    (([] : List α) == (b :: l)) = false := rfl

theorem list_beq_cons_nil {α : Type} [BEq α] (a : α) (l : List α) :
    ((a :: l) == ([] : List α)) = false := rfl

theorem list_beq_cons_cons {α : Type} [BEq α] (a b : α) (l₁ l₂ : List α) :
    ((a :: l₁) == (b :: l₂)) = ((a == b) && (l₁ == l₂)) := rfl

-- smoke tests: the canonical repair idioms stay closed
example (a num1 : BoundedNat (2^256)) (hle : num1.val ≤ a.val) :
    BoundedNat.sub_aborts a num1 = false := by
  rw [bn_sub_aborts_decide, decide_eq_false_iff_not]
  omega

example (n b : BoundedNat (2^256)) (h : n.val ≥ b.val) :
    BoundedNat.ge n b = true := by
  rw [bn_ge_decide]
  exact decide_eq_true_eq.mpr h

example (a b : BoundedNat (2^64)) (h : a.val * b.val < 2^64) :
    BoundedNat.mul_aborts a b = false :=
  (bn_mul_aborts_eq_false_iff a b).mpr h

example (x : BoundedNat (2^64)) : BoundedNat.eq x x = true := bn_eq_refl x

example {t : Type} [DecidableEq t] (a b : t) (h : (a == b) = true) : a = b :=
  deq_eq_of_beq h

/-! ## Shared `BoundedNat` step facts

Statements the client corpora keep re-deriving on top of the bridges above:
the `.aborts`-hypothesis form of `add_val_of_no_overflow`, the `+ 1` index-bump
pair, the `1 <<` no-abort fact, and the two widening casts. Everything here is
a corollary of a lemma already in this file -- the value is that a client cites
one name instead of re-running the same five-line derivation.

Namespaced per the standing rule in `plans/lean-pipeline/shared-proof-infra.md`:
these are exactly the names an overlay author reaches for (`addOneValOfLt`,
`u64_add_one_val_of_lt_max`, ...), so a root-namespace copy here would be a
latent compile break for every corpus that already has one. -/

namespace BoundedNatFacts

/-- `.val` of a non-aborting `add`, from the `add_aborts = false` hypothesis
the generated abort chains actually carry. -/
theorem add_val_of_add_aborts_false {bound : Nat} (a b : BoundedNat bound)
    (h : BoundedNat.add_aborts a b = false) :
    (BoundedNat.add a b).val = a.val + b.val :=
  BoundedNat.add_val_of_no_overflow a b ((bn_add_aborts_eq_false_iff a b).mp h)

/-- Index bump under a strict `lt` guard cannot overflow. -/
theorem add_one_aborts_of_lt (idx count : BoundedNat (2^64))
    (h : BoundedNat.lt idx count = true) :
    BoundedNat.add_aborts idx (1 : BoundedNat (2^64)) = false := by
  have h_lt : idx.val < count.val := (bn_lt_iff idx count).mp h
  have h_count := count.property
  rw [bn_add_aborts_eq_false_iff, bn_one_val_u64]
  omega

theorem add_one_val_of_lt (idx count : BoundedNat (2^64))
    (h : BoundedNat.lt idx count = true) :
    (BoundedNat.add idx (1 : BoundedNat (2^64))).val = idx.val + 1 := by
  rw [add_val_of_add_aborts_false idx (1 : BoundedNat (2^64))
    (add_one_aborts_of_lt idx count h), bn_one_val_u64]

theorem add_one_aborts_of_lt_max (value : BoundedNat (2^64))
    (h : value.val < 18446744073709551615) :
    BoundedNat.add_aborts value (1 : BoundedNat (2^64)) = false := by
  rw [bn_add_aborts_eq_false_iff, bn_one_val_u64]
  omega

theorem add_one_val_of_lt_max (value : BoundedNat (2^64))
    (h : value.val < 18446744073709551615) :
    (BoundedNat.add value (1 : BoundedNat (2^64))).val = value.val + 1 := by
  rw [add_val_of_add_aborts_false value (1 : BoundedNat (2^64))
    (add_one_aborts_of_lt_max value h), bn_one_val_u64]

/-- A shift whose amount type is no wider than the shiftee's bit width never
aborts -- the `u256 << u8` bitmap idiom. -/
theorem shl_bounded_aborts_eq_false_of_bound_le {bound bound' : Nat}
    (a : BoundedNat bound) (k : BoundedNat bound')
    (h : bound' ≤ Nat.log2 bound) :
    BoundedNat.shl_bounded_aborts a k = false :=
  (bn_shl_bounded_aborts_eq_false_iff a k).mpr
    (Nat.lt_of_lt_of_le k.property h)

theorem shl_bounded_aborts_u256_u8_eq_false (a : BoundedNat (2^256))
    (k : BoundedNat (2^8)) :
    BoundedNat.shl_bounded_aborts a k = false :=
  shl_bounded_aborts_eq_false_of_bound_le a k (by decide)

theorem convert_val_u64_u128 (a : BoundedNat (2^64)) :
    ((BoundedNat.convert a : BoundedNat (2^128))).val = a.val :=
  BoundedNat.convert_val_of_bound_le a (by decide)

theorem convert_val_u128_u256 (a : BoundedNat (2^128)) :
    ((BoundedNat.convert a : BoundedNat (2^256))).val = a.val :=
  BoundedNat.convert_val_of_bound_le a (by decide)

/-- The two remaining widening pairs the corpora re-derive privately: `u32 -> u64` (the
I32-abs oracle path) and `u64 -> u256` (the ClmmMath widening path). Unconditional, so
`move_norm`'s `simp only` can apply them -- which the general
`BoundedNat.convert_val_of_bound_le` cannot, since its side goal `2^64 <= 2^128` is not
discharged by an `only`-scoped set. -/
theorem convert_val_u32_u64 (a : BoundedNat (2^32)) :
    ((BoundedNat.convert a : BoundedNat (2^64))).val = a.val :=
  BoundedNat.convert_val_of_bound_le a (by decide)

theorem convert_val_u64_u256 (a : BoundedNat (2^64)) :
    ((BoundedNat.convert a : BoundedNat (2^256))).val = a.val :=
  BoundedNat.convert_val_of_bound_le a (by decide)

end BoundedNatFacts

/-! ## BoundedNat -> Nat bridge layer (phase-3 lemma wave)

Normalization vocabulary that takes BoundedNat-structured goals to honest Nat
arithmetic. This is a soundness boundary: the wrapping ops (`add`, `mul`,
`shiftLeft`, `convert`, the `OfNat` literal) are NOT monotone, so a Nat-side
fact about `a.val + b.val` says nothing about `(add a b).val` without a
no-overflow hypothesis. Every lemma here is therefore an EXACT collapse: the
wrapped value in `% bound` form unconditionally, the plain value under the
explicit fit hypothesis, or a projection that never wraps at all.

Two head-symbol families per op, both needed (simp/rw matching is syntactic):
the operator-notation head (`a % b`, `a <<< k`, `a &&& b`) that human spec
proofs present, and the named-function head (`BoundedNat.mod a b`, ...) that
generated code presents.

Attribute policy: `@[simp]` only on unconditional projections that complete an
existing `@[simp]` twin (`mod_val` next to `div_val`, `shiftLeft_nat_val` next
to `shiftLeft_bounded_val`). Everything carrying a hypothesis is
citation-only. -/

namespace BoundedNat

variable {bound : Nat}

/-- Mod extracts to Nat mod (`div_val`'s missing twin). Total at the Nat level
(`a % 0 = a`); `mod_aborts` gates the Move abort separately. -/
@[simp] theorem mod_val (a b : BoundedNat bound) : (a % b).val = a.val % b.val := rfl

/-- Left shift by a `Nat` amount extracts to wrapped Nat left shift
(`shiftLeft_bounded_val`'s missing twin). -/
@[simp] theorem shiftLeft_nat_val (a : BoundedNat bound) (k : Nat) :
    (a <<< k).val = (a.val <<< k) % bound := by
  change (if h : bound > 0 then
      (⟨(a.val <<< k) % bound, Nat.mod_lt _ h⟩ : BoundedNat bound)
    else
      (⟨0, absurd a.property (by simp_all)⟩ : BoundedNat bound)).val = _
  split
  · rfl
  · rename_i h
    have hb : bound = 0 := Nat.eq_zero_of_not_pos h
    exact False.elim (Nat.not_lt_zero a.val (by simpa [hb] using a.property))

/-- Wrap elimination for `<<<` with a `Nat` amount. -/
theorem shiftLeft_nat_val_of_lt (a : BoundedNat bound) (k : Nat)
    (h : a.val <<< k < bound) : (a <<< k).val = a.val <<< k := by
  rw [shiftLeft_nat_val, Nat.mod_eq_of_lt h]

/-- Wrap elimination for `<<<` with a `BoundedNat` amount. -/
theorem shiftLeft_bounded_val_of_lt {bound' : Nat} (a : BoundedNat bound)
    (k : BoundedNat bound') (h : a.val <<< k.val < bound) :
    (a <<< k).val = a.val <<< k.val := by
  rw [shiftLeft_bounded_val, Nat.mod_eq_of_lt h]

/-- AND never wraps: the result is dominated by the left operand. -/
theorem land_val (a b : BoundedNat bound) :
    (BoundedNat.land a b).val = a.val &&& b.val := by
  unfold BoundedNat.land
  rw [dif_pos (Nat.lt_of_le_of_lt Nat.and_le_left a.property)]

/-- `land_val` at the operator head. -/
theorem and_val (a b : BoundedNat bound) : (a &&& b).val = a.val &&& b.val :=
  land_val a b

/-- OR under an explicit fit hypothesis (the def saturates otherwise). -/
theorem lor_val_of_lt (a b : BoundedNat bound) (h : a.val ||| b.val < bound) :
    (BoundedNat.lor a b).val = a.val ||| b.val := by
  unfold BoundedNat.lor
  rw [dif_pos h]

/-- `lor_val_of_lt` at the operator head. -/
theorem or_val_of_lt (a b : BoundedNat bound) (h : a.val ||| b.val < bound) :
    (a ||| b).val = a.val ||| b.val :=
  lor_val_of_lt a b h

/-- At a power-of-2 bound (every Move width) OR never overflows. -/
theorem lor_val_pow2 {n : Nat} (a b : BoundedNat (2^n)) :
    (BoundedNat.lor a b).val = a.val ||| b.val :=
  lor_val_of_lt a b (Nat.or_lt_two_pow a.property b.property)

/-- `lor_val_pow2` at the operator head. -/
theorem or_val_pow2 {n : Nat} (a b : BoundedNat (2^n)) :
    (a ||| b).val = a.val ||| b.val :=
  lor_val_pow2 a b

/-- XOR under an explicit fit hypothesis. -/
theorem bxor_val_of_lt (a b : BoundedNat bound) (h : a.val ^^^ b.val < bound) :
    (BoundedNat.bxor a b).val = a.val ^^^ b.val := by
  unfold BoundedNat.bxor
  rw [dif_pos h]

/-- `bxor_val_of_lt` at the operator head. -/
theorem xor_val_of_lt (a b : BoundedNat bound) (h : a.val ^^^ b.val < bound) :
    (a ^^^ b).val = a.val ^^^ b.val :=
  bxor_val_of_lt a b h

/-- At a power-of-2 bound XOR never overflows. -/
theorem bxor_val_pow2 {n : Nat} (a b : BoundedNat (2^n)) :
    (BoundedNat.bxor a b).val = a.val ^^^ b.val :=
  bxor_val_of_lt a b (Nat.xor_lt_two_pow a.property b.property)

/-- `bxor_val_pow2` at the operator head. -/
theorem xor_val_pow2 {n : Nat} (a b : BoundedNat (2^n)) :
    (a ^^^ b).val = a.val ^^^ b.val :=
  bxor_val_pow2 a b

/-- Bitwise NOT in closed form: `bound - 1 - a.val` (the `% bound` in the def
is a no-op for any positive bound, not only powers of 2). -/
theorem bnot_val (a : BoundedNat bound) (h : bound > 0) :
    (BoundedNat.bnot a).val = bound - 1 - a.val := by
  unfold BoundedNat.bnot
  rw [dif_pos h]
  exact Nat.mod_eq_of_lt (by omega)

/-- The `Complement` instance (`~~~a`) in closed form. -/
theorem complement_val (a : BoundedNat bound) (h : bound > 0) :
    (~~~a).val = bound - 1 - a.val := by
  change (if h0 : bound > 0 then
      (if hc : bound - 1 - a.val < bound then
        (⟨bound - 1 - a.val, hc⟩ : BoundedNat bound)
      else a)
    else (⟨0, BoundedNat.bound_pos a⟩ : BoundedNat bound)).val = _
  rw [dif_pos h, dif_pos (by omega)]

/-- Truncating cast in closed form: `% bound_to`, unconditionally. Pairs with
`convert_val_of_lt` (the no-wrap face) the way `add_val` pairs with
`add_val_of_no_overflow`. -/
theorem convert_val_mod {bound_from bound_to : Nat} [NeZero bound_to] (a : BoundedNat bound_from)
    (h : bound_to > 0) :
    (convert a : BoundedNat bound_to).val = a.val % bound_to := by
  unfold convert
  by_cases hf : a.val < bound_to
  · rw [dif_pos hf, Nat.mod_eq_of_lt hf]
  · rw [dif_neg hf, dif_pos h]

/-- `convert_val_of_lt` at the `truncate` head (`truncate` is a definitional
alias of `convert`, but a distinct head symbol to matching). -/
theorem truncate_val_of_lt {bound bound' : Nat} [NeZero bound'] (a : BoundedNat bound)
    (h : a.val < bound') : (truncate a : BoundedNat bound').val = a.val :=
  convert_val_of_lt a h

/-- `convert_val_mod` at the `truncate` head. -/
theorem truncate_val_mod {bound bound' : Nat} [NeZero bound'] (a : BoundedNat bound)
    (h : bound' > 0) : (truncate a : BoundedNat bound').val = a.val % bound' :=
  convert_val_mod a h

end BoundedNat

/-! ### Named-function heads for the arithmetic core

Generated code calls `BoundedNat.add` / `.mul` / `.sub` / `.div` / `.mod` /
`.shiftLeft` / `.shiftRight` directly; the `@[simp]` projections above are
stated at the operator heads and do not match those goals. Root-level `bn_*`
names, following the CompatBridges convention. -/

section BnValHeads

variable {bound : Nat}

/-- Wrapping `add` in `% bound` form. -/
theorem bn_add_val_mod (a b : BoundedNat bound) (h : bound > 0) :
    (BoundedNat.add a b).val = (a.val + b.val) % bound := by
  simp only [BoundedNat.add, h, ↓reduceDIte]

/-- Wrap elimination for `add`: the `mod_eq_of_lt` collapse under the
no-overflow hypothesis, at the named head. -/
theorem bn_add_val_of_lt (a b : BoundedNat bound)
    (h : a.val + b.val < bound) :
    (BoundedNat.add a b).val = a.val + b.val := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  simp only [BoundedNat.add, hb, ↓reduceDIte, Nat.mod_eq_of_lt h]

/-- Wrapping `mul` in `% bound` form. -/
theorem bn_mul_val_mod (a b : BoundedNat bound) (h : bound > 0) :
    (BoundedNat.mul a b).val = (a.val * b.val) % bound := by
  simp only [BoundedNat.mul, h, ↓reduceDIte]

/-- Wrap elimination for `mul` under the no-overflow hypothesis. -/
theorem bn_mul_val_of_lt (a b : BoundedNat bound)
    (h : a.val * b.val < bound) :
    (BoundedNat.mul a b).val = a.val * b.val := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  simp only [BoundedNat.mul, hb, ↓reduceDIte, Nat.mod_eq_of_lt h]

/-- Saturating `sub` extracts unconditionally (Nat subtraction truncates the
same way; `sub_aborts` carries the Move underflow abort). -/
theorem bn_sub_val_eq (a b : BoundedNat bound) :
    (BoundedNat.sub a b).val = a.val - b.val := rfl

theorem bn_div_val_eq (a b : BoundedNat bound) :
    (BoundedNat.div a b).val = a.val / b.val := rfl

theorem bn_mod_val_eq (a b : BoundedNat bound) :
    (BoundedNat.mod a b).val = a.val % b.val := rfl

/-- Wrapping `shiftLeft` (Nat amount) in `% bound` form, named head. -/
theorem bn_shl_val_mod (a : BoundedNat bound) (k : Nat) (h : bound > 0) :
    (BoundedNat.shiftLeft a k).val = (a.val <<< k) % bound := by
  simp only [BoundedNat.shiftLeft, h, ↓reduceDIte]

/-- Wrap elimination for `shiftLeft` (Nat amount), named head. -/
theorem bn_shl_val_of_lt (a : BoundedNat bound) (k : Nat)
    (h : a.val <<< k < bound) :
    (BoundedNat.shiftLeft a k).val = a.val <<< k := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  simp only [BoundedNat.shiftLeft, hb, ↓reduceDIte, Nat.mod_eq_of_lt h]

theorem bn_shr_val_eq (a : BoundedNat bound) (k : Nat) :
    (BoundedNat.shiftRight a k).val = a.val >>> k := rfl

end BnValHeads

-- smoke tests: wrap elimination composes with the abort faces
example (a b : BoundedNat (2^64)) (h : BoundedNat.add_aborts a b = false) :
    (BoundedNat.add a b).val = a.val + b.val :=
  bn_add_val_of_lt a b ((bn_add_aborts_eq_false_iff a b).mp h)

example (a b : BoundedNat (2^128)) : (a &&& b).val = a.val &&& b.val :=
  BoundedNat.and_val a b

example (a b : BoundedNat (2^256)) : (a ||| b).val = a.val ||| b.val :=
  BoundedNat.or_val_pow2 a b

/-! ### Checked-op faces: completing the abort-predicate iff matrix

The CompatBridges section characterizes every abort predicate at its own head
symbol, but the `= false` faces were stated only at the `_aborts` alias heads
and only for the bounded-amount shifts. These complete the matrix: `= false`
faces at the `_overflows` / `_underflows` heads, the Nat-amount shift faces,
and the positive-divisor conveniences (hypotheses arrive as `0 < b.val` at
least as often as `b.val ≠ 0`). -/

section BnAbortFaces

variable {bound : Nat}

theorem bn_add_overflows_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.add_overflows a b = false ↔ a.val + b.val < bound :=
  (bool_eq_false_iff_not_of_iff (bn_add_overflows_iff a b)).trans Nat.not_le

theorem bn_mul_overflows_eq_false_iff (a b : BoundedNat bound) :
    BoundedNat.mul_overflows a b = false ↔ a.val * b.val < bound :=
  (bool_eq_false_iff_not_of_iff (bn_mul_overflows_iff a b)).trans Nat.not_le

theorem bn_sub_underflows_eq_false_iff_le (a b : BoundedNat bound) :
    BoundedNat.sub_underflows a b = false ↔ b.val ≤ a.val :=
  (bool_eq_false_iff_not_of_iff (bn_sub_underflows_iff a b)).trans Nat.not_lt

theorem bn_shl_aborts_eq_false_iff (a : BoundedNat bound) (k : Nat) :
    BoundedNat.shl_aborts a k = false ↔ k < Nat.log2 bound :=
  (bool_eq_false_iff_not_of_iff (bn_shl_aborts_iff a k)).trans Nat.not_le

theorem bn_shr_aborts_eq_false_iff (a : BoundedNat bound) (k : Nat) :
    BoundedNat.shr_aborts a k = false ↔ k < Nat.log2 bound :=
  bn_shl_aborts_eq_false_iff a k

theorem bn_div_aborts_eq_false_of_pos (a b : BoundedNat bound)
    (h : 0 < b.val) : BoundedNat.div_aborts a b = false :=
  (bn_div_aborts_eq_false_iff a b).mpr (by omega)

theorem bn_mod_aborts_eq_false_of_pos (a b : BoundedNat bound)
    (h : 0 < b.val) : BoundedNat.mod_aborts a b = false :=
  (bn_mod_aborts_eq_false_iff a b).mpr (by omega)

end BnAbortFaces

/-! ### `Nat.log2` collapses at the Move widths

The shift faces above leave a `Nat.log2 bound` that `omega` cannot see
through; at the six Move widths it is a constant. Kernel `decide` here is a
256-step structural evaluation, not a decision procedure over the value
domain. -/

theorem bn_log2_bound_u8 : Nat.log2 (2^8) = 8 := by decide
theorem bn_log2_bound_u16 : Nat.log2 (2^16) = 16 := by decide
theorem bn_log2_bound_u32 : Nat.log2 (2^32) = 32 := by decide
theorem bn_log2_bound_u64 : Nat.log2 (2^64) = 64 := by decide
theorem bn_log2_bound_u128 : Nat.log2 (2^128) = 128 := by decide
theorem bn_log2_bound_u256 : Nat.log2 (2^256) = 256 := by decide

-- smoke tests: the faces compose to honest Nat arithmetic
example (a b : BoundedNat (2^64)) (h : a.val * b.val < 2^64) :
    BoundedNat.mul_overflows a b = false :=
  (bn_mul_overflows_eq_false_iff a b).mpr h

example (a : BoundedNat (2^64)) (k : Nat) (h : k < 64) :
    BoundedNat.shl_aborts a k = false :=
  (bn_shl_aborts_eq_false_iff a k).mpr (by rw [bn_log2_bound_u64]; exact h)

example (a b : BoundedNat (2^128)) (h : 0 < b.val) :
    BoundedNat.div_aborts a b = false :=
  bn_div_aborts_eq_false_of_pos a b h

/-! ### Order and bounds transport

The Bool comparators are fully bridged above (`bn_lt_iff` matrix); these cover
the two remaining transports: the Prop-valued `LT`/`LE` instances (definitional,
but a citable name beats an `Iff.rfl` re-derivation at every site), and the
non-linear bounds facts `omega` cannot produce on its own -- division/mod/sub
domination and the Euclidean identity, which are exactly what a `.val`-form
goal needs after the projections above have fired. -/

namespace BoundedNat

variable {bound : Nat}

/-- The Prop-valued `<` instance is `.val` comparison, definitionally. -/
theorem lt_iff_val_lt (a b : BoundedNat bound) : a < b ↔ a.val < b.val :=
  Iff.rfl

/-- The Prop-valued `≤` instance is `.val` comparison, definitionally. -/
theorem le_iff_val_le (a b : BoundedNat bound) : a ≤ b ↔ a.val ≤ b.val :=
  Iff.rfl

end BoundedNat

section BnBoundsTransport

variable {bound : Nat}

/-- Propositional disequality transports to `.val` (completes `bn_val_inj`). -/
theorem bn_ne_iff_val_ne (a b : BoundedNat bound) : a ≠ b ↔ a.val ≠ b.val :=
  ⟨fun h hv => h (BoundedNat.ext hv), fun h he => h (he ▸ rfl)⟩

/-- The headroom fact every overflow discharge cites, under a uniform name. -/
theorem bn_val_lt_bound (a : BoundedNat bound) : a.val < bound :=
  a.property

/-- Saturating subtraction is dominated by the minuend. -/
theorem bn_sub_val_le (a b : BoundedNat bound) :
    (BoundedNat.sub a b).val ≤ a.val := by
  rw [bn_sub_val_eq]
  exact Nat.sub_le a.val b.val

/-- Division is dominated by the dividend (variable divisor -- outside
`omega`'s fragment). -/
theorem bn_div_val_le (a b : BoundedNat bound) :
    (BoundedNat.div a b).val ≤ a.val := by
  rw [bn_div_val_eq]
  exact Nat.div_le_self a.val b.val

/-- Mod is dominated by the dividend. -/
theorem bn_mod_val_le (a b : BoundedNat bound) :
    (BoundedNat.mod a b).val ≤ a.val := by
  rw [bn_mod_val_eq]
  exact Nat.mod_le a.val b.val

/-- Mod is bounded by a positive divisor. -/
theorem bn_mod_val_lt (a b : BoundedNat bound) (h : 0 < b.val) :
    (BoundedNat.mod a b).val < b.val := by
  rw [bn_mod_val_eq]
  exact Nat.mod_lt a.val h

/-- Euclidean identity at the named heads: reconnects `div` and `mod` results
to the operand after the projections have fired. -/
theorem bn_div_mul_add_mod (a b : BoundedNat bound) :
    b.val * (BoundedNat.div a b).val + (BoundedNat.mod a b).val = a.val := by
  rw [bn_div_val_eq, bn_mod_val_eq]
  exact Nat.div_add_mod a.val b.val

end BnBoundsTransport

-- smoke tests: transport facts feed omega where it is otherwise stuck
example (a b c : BoundedNat (2^64)) (h : c.val ≤ b.val) :
    (BoundedNat.div a b).val + c.val < 2^64 + b.val := by
  have h1 := bn_div_val_le a b
  have h2 := bn_val_lt_bound a
  omega

example (a b : BoundedNat (2^64)) (hb : 0 < b.val)
    (h : BoundedNat.mod a b = a) : a.val < b.val := by
  have := bn_mod_val_lt a b hb
  rw [h] at this
  exact this

/-! ### Literal machinery

The concrete-width literal projections all close by `rfl` today; what was
missing is the ABSTRACT-`n` form (`rfl` is unavailable when the numeral is a
variable -- the `Generic.val_ofNat` shape the scallop DecimalBound pack had to
re-derive in an overlay), plus the width-family completions of the existing
`bn_zero_val_u64` / `boundedNat_u128_max_val` conveniences. -/

namespace BoundedNat

variable {bound : Nat}

/-- Generic literal projection: a fitting numeral's `.val` is itself. Proof
cases the `Decidable` instance; on `isTrue` the `OfNat` body reduces
definitionally. -/
theorem val_ofNat {n : Nat} [NeZero bound] [i : Decidable (n < bound)] (h : n < bound) :
    (OfNat.ofNat n : BoundedNat bound).val = n := by
  cases i with
  | isTrue h' => rfl
  | isFalse h' => exact absurd h h'

/-- Projection at the explicit constructor head. -/
theorem ofNat_val {n : Nat} (h : n < bound) :
    (BoundedNat.ofNat n h).val = n := rfl

/-- `toNat` is `.val` (distinct head symbol, same projection). -/
theorem toNat_eq_val (a : BoundedNat bound) : a.toNat = a.val := rfl

end BoundedNat

-- max-literal projections completing the @[simp] boundedNat_u128_max_val family
@[simp]
theorem boundedNat_u8_max_val : (255 : BoundedNat (2^8)).val = 255 := rfl

@[simp]
theorem boundedNat_u16_max_val : (65535 : BoundedNat (2^16)).val = 65535 := rfl

@[simp]
theorem boundedNat_u32_max_val :
    (4294967295 : BoundedNat (2^32)).val = 4294967295 := rfl

@[simp]
theorem boundedNat_u64_max_val :
    (18446744073709551615 : BoundedNat (2^64)).val = 18446744073709551615 := rfl

@[simp]
theorem boundedNat_u256_max_val :
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 :
      BoundedNat (2^256)).val =
      115792089237316195423570985008687907853269984665640564039457584007913129639935 := rfl

-- zero/one literal projections at every Move width (u64 pair exists above)
theorem bn_zero_val_u8 : (0 : BoundedNat (2^8)).val = 0 := rfl
theorem bn_one_val_u8 : (1 : BoundedNat (2^8)).val = 1 := rfl
theorem bn_zero_val_u16 : (0 : BoundedNat (2^16)).val = 0 := rfl
theorem bn_one_val_u16 : (1 : BoundedNat (2^16)).val = 1 := rfl
theorem bn_zero_val_u32 : (0 : BoundedNat (2^32)).val = 0 := rfl
theorem bn_one_val_u32 : (1 : BoundedNat (2^32)).val = 1 := rfl
theorem bn_zero_val_u128 : (0 : BoundedNat (2^128)).val = 0 := rfl
theorem bn_one_val_u128 : (1 : BoundedNat (2^128)).val = 1 := rfl
theorem bn_zero_val_u256 : (0 : BoundedNat (2^256)).val = 0 := rfl
theorem bn_one_val_u256 : (1 : BoundedNat (2^256)).val = 1 := rfl

-- smoke tests: the abstract literal projection has no rfl route
example {bound : Nat} [NeZero bound] (n : Nat) [Decidable (n < bound)] (h : n < bound)
    (a : BoundedNat bound) (ha : a.val = n) :
    a = (OfNat.ofNat n : BoundedNat bound) :=
  BoundedNat.ext (ha.trans (BoundedNat.val_ofNat h).symm)

example : (255 : BoundedNat (2^8)) = ~~~(0 : BoundedNat (2^8)) := by
  apply BoundedNat.ext
  rw [BoundedNat.complement_val _ (by decide), bn_zero_val_u8,
    boundedNat_u8_max_val]

/-! ### mul_div, widening multiply, cancellation, nested div (pass 2, tier 1)

`mul_div` is not a Prelude op -- the fused form lives in client natives
(integer-mate `Math_u64.mul_div` and friends). What reaches this layer is the
COMPOSED head `div (mul a b) c`, plus the bare Nat shape `a * b / c` once the
`.val` projections have fired. Both are covered: Nat-level vocabulary first
(`omega` cannot produce any of it -- division by a variable is outside its
fragment), then the BoundedNat forms under the mul-fit hypothesis (the wrapped
product forfeits every bound below without it -- soundness boundary, stated
explicitly). -/

section NatMulDiv

/-- Pro-rata bound: scaling by `b / c` with `b ≤ c` cannot increase `a`. -/
theorem nat_mul_div_le_of_le (a : Nat) {b c : Nat} (h : b ≤ c) :
    a * b / c ≤ a := by
  by_cases hc : 0 < c
  · calc a * b / c ≤ a * c / c := Nat.div_le_div_right (Nat.mul_le_mul_left a h)
      _ = a := Nat.mul_div_cancel a hc
  · have hc0 : c = 0 := by omega
    rw [hc0, Nat.div_zero]
    exact Nat.zero_le a

/-- `a * b / c` is monotone in `a`. -/
theorem nat_mul_div_le_mul_div_left {a a' : Nat} (b c : Nat) (h : a ≤ a') :
    a * b / c ≤ a' * b / c :=
  Nat.div_le_div_right (Nat.mul_le_mul_right b h)

/-- `a * b / c` is monotone in `b`. -/
theorem nat_mul_div_le_mul_div_right (a : Nat) {b b' : Nat} (c : Nat)
    (h : b ≤ b') : a * b / c ≤ a * b' / c :=
  Nat.div_le_div_right (Nat.mul_le_mul_left a h)

/-- `a * b / c` is antitone in the divisor (positive lower divisor). -/
theorem nat_mul_div_anti_divisor (a b : Nat) {c c' : Nat} (h : c ≤ c')
    (hc : 0 < c) : a * b / c' ≤ a * b / c :=
  Nat.div_le_div_left h hc

/-- Exact cancellation, `c ≠ 0` spelling (core's is `0 < c`). -/
theorem nat_mul_div_cancel (a : Nat) {c : Nat} (hc : c ≠ 0) :
    a * c / c = a :=
  Nat.mul_div_cancel a (by omega)

end NatMulDiv

section BnMulDiv

variable {bound : Nat}

/-- Pro-rata bound at the composed head. The fit hypothesis is load-bearing:
without it the product wraps and the bound is false. -/
theorem bn_mul_div_val_le_of_le (a b c : BoundedNat bound)
    (hfit : a.val * b.val < bound) (h : b.val ≤ c.val) :
    (BoundedNat.div (BoundedNat.mul a b) c).val ≤ a.val := by
  rw [bn_div_val_eq, bn_mul_val_of_lt a b hfit]
  exact nat_mul_div_le_of_le a.val h

/-- Exact `mul_div` cancellation at the composed head. -/
theorem bn_mul_div_cancel (a c : BoundedNat bound)
    (hfit : a.val * c.val < bound) (hc : c.val ≠ 0) :
    BoundedNat.div (BoundedNat.mul a c) c = a := by
  refine BoundedNat.ext ?_
  rw [bn_div_val_eq, bn_mul_val_of_lt a c hfit]
  exact nat_mul_div_cancel a.val hc

/-- Monotone in the first factor. The fit hypothesis is needed only on the
LARGER side: the smaller side's wrapped value is dominated by its true value
(`Nat.mod_le`), so the chain still closes. -/
theorem bn_mul_div_val_mono_left (a a' b c : BoundedNat bound)
    (ha : a.val ≤ a'.val) (hfit : a'.val * b.val < bound) :
    (BoundedNat.div (BoundedNat.mul a b) c).val ≤
      (BoundedNat.div (BoundedNat.mul a' b) c).val := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  rw [bn_div_val_eq, bn_div_val_eq, bn_mul_val_of_lt a' b hfit,
    bn_mul_val_mod a b hb]
  refine Nat.div_le_div_right (Nat.le_trans (Nat.mod_le _ _) ?_)
  exact Nat.mul_le_mul_right b.val ha

/-- Monotone in the second factor (fit on the larger side only). -/
theorem bn_mul_div_val_mono_right (a b b' c : BoundedNat bound)
    (hb' : b.val ≤ b'.val) (hfit : a.val * b'.val < bound) :
    (BoundedNat.div (BoundedNat.mul a b) c).val ≤
      (BoundedNat.div (BoundedNat.mul a b') c).val := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  rw [bn_div_val_eq, bn_div_val_eq, bn_mul_val_of_lt a b' hfit,
    bn_mul_val_mod a b hb]
  refine Nat.div_le_div_right (Nat.le_trans (Nat.mod_le _ _) ?_)
  exact Nat.mul_le_mul_left a.val hb'

/-- Antitone in the divisor -- no fit hypothesis at all (the numerator is the
same wrapped value on both sides). -/
theorem bn_mul_div_val_anti_divisor (a b c c' : BoundedNat bound)
    (h : c.val ≤ c'.val) (hc : 0 < c.val) :
    (BoundedNat.div (BoundedNat.mul a b) c').val ≤
      (BoundedNat.div (BoundedNat.mul a b) c).val := by
  rw [bn_div_val_eq, bn_div_val_eq]
  exact Nat.div_le_div_left h hc

end BnMulDiv

namespace BoundedNat

variable {bound : Nat}

/-- `bn_mul_div_val_le_of_le` at the operator head. -/
theorem mul_div_val_le_of_le (a b c : BoundedNat bound)
    (hfit : a.val * b.val < bound) (h : b.val ≤ c.val) :
    (a * b / c).val ≤ a.val :=
  bn_mul_div_val_le_of_le a b c hfit h

/-- `bn_mul_div_cancel` at the operator head. -/
theorem mul_div_cancel (a c : BoundedNat bound)
    (hfit : a.val * c.val < bound) (hc : c.val ≠ 0) :
    a * c / c = a :=
  bn_mul_div_cancel a c hfit hc

/-- `bn_mul_div_val_mono_left` at the operator head. -/
theorem mul_div_val_mono_left (a a' b c : BoundedNat bound)
    (ha : a.val ≤ a'.val) (hfit : a'.val * b.val < bound) :
    (a * b / c).val ≤ (a' * b / c).val :=
  bn_mul_div_val_mono_left a a' b c ha hfit

/-- `bn_mul_div_val_mono_right` at the operator head. -/
theorem mul_div_val_mono_right (a b b' c : BoundedNat bound)
    (hb' : b.val ≤ b'.val) (hfit : a.val * b'.val < bound) :
    (a * b / c).val ≤ (a * b' / c).val :=
  bn_mul_div_val_mono_right a b b' c hb' hfit

/-- `bn_mul_div_val_anti_divisor` at the operator head. -/
theorem mul_div_val_anti_divisor (a b c c' : BoundedNat bound)
    (h : c.val ≤ c'.val) (hc : 0 < c.val) :
    (a * b / c').val ≤ (a * b / c).val :=
  bn_mul_div_val_anti_divisor a b c c' h hc

end BoundedNat

/-! #### Widening multiply: exact, hypothesis-free at the doubling pairs -/

section BnWidenMul

/-- Generic widening multiply: casts into a target that holds the full product
range are exact. The bound-arithmetic hypothesis is `decide`-dischargeable at
concrete widths. -/
theorem bn_widen_mul_val {bound_a bound_b bound_to : Nat} [NeZero bound_to]
    (a : BoundedNat bound_a) (b : BoundedNat bound_b)
    (h : bound_a * bound_b ≤ bound_to) :
    (BoundedNat.mul (BoundedNat.convert a) (BoundedNat.convert b) :
      BoundedNat bound_to).val = a.val * b.val := by
  have ha0 : 0 < bound_a := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  have hb0 : 0 < bound_b := Nat.lt_of_le_of_lt (Nat.zero_le _) b.property
  have hfit : a.val * b.val < bound_to :=
    Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_lt_of_lt a.property b.property) h
  have hav : (BoundedNat.convert a : BoundedNat bound_to).val = a.val :=
    BoundedNat.convert_val_of_lt a
      (Nat.lt_of_lt_of_le a.property
        (Nat.le_trans (Nat.le_mul_of_pos_right bound_a hb0) h))
  have hbv : (BoundedNat.convert b : BoundedNat bound_to).val = b.val :=
    BoundedNat.convert_val_of_lt b
      (Nat.lt_of_lt_of_le b.property
        (Nat.le_trans (Nat.le_mul_of_pos_left bound_b ha0) h))
  rw [bn_mul_val_of_lt _ _ (by rw [hav, hbv]; exact hfit), hav, hbv]

end BnWidenMul

-- the five width-doubling pairs, hypothesis-free, named head
@[simp] theorem bn_widen_mul_val_u8_u16 (a b : BoundedNat (2^8)) :
    (BoundedNat.mul (BoundedNat.convert a) (BoundedNat.convert b) :
      BoundedNat (2^16)).val = a.val * b.val :=
  bn_widen_mul_val a b (by decide)

@[simp] theorem bn_widen_mul_val_u16_u32 (a b : BoundedNat (2^16)) :
    (BoundedNat.mul (BoundedNat.convert a) (BoundedNat.convert b) :
      BoundedNat (2^32)).val = a.val * b.val :=
  bn_widen_mul_val a b (by decide)

@[simp] theorem bn_widen_mul_val_u32_u64 (a b : BoundedNat (2^32)) :
    (BoundedNat.mul (BoundedNat.convert a) (BoundedNat.convert b) :
      BoundedNat (2^64)).val = a.val * b.val :=
  bn_widen_mul_val a b (by decide)

@[simp] theorem bn_widen_mul_val_u64_u128 (a b : BoundedNat (2^64)) :
    (BoundedNat.mul (BoundedNat.convert a) (BoundedNat.convert b) :
      BoundedNat (2^128)).val = a.val * b.val :=
  bn_widen_mul_val a b (by decide)

@[simp] theorem bn_widen_mul_val_u128_u256 (a b : BoundedNat (2^128)) :
    (BoundedNat.mul (BoundedNat.convert a) (BoundedNat.convert b) :
      BoundedNat (2^256)).val = a.val * b.val :=
  bn_widen_mul_val a b (by decide)

namespace BoundedNat

-- operator-head twins of the doubling pairs
@[simp] theorem widen_mul_val_u8_u16 (a b : BoundedNat (2^8)) :
    ((convert a * convert b : BoundedNat (2^16))).val = a.val * b.val :=
  bn_widen_mul_val_u8_u16 a b

@[simp] theorem widen_mul_val_u16_u32 (a b : BoundedNat (2^16)) :
    ((convert a * convert b : BoundedNat (2^32))).val = a.val * b.val :=
  bn_widen_mul_val_u16_u32 a b

@[simp] theorem widen_mul_val_u32_u64 (a b : BoundedNat (2^32)) :
    ((convert a * convert b : BoundedNat (2^64))).val = a.val * b.val :=
  bn_widen_mul_val_u32_u64 a b

@[simp] theorem widen_mul_val_u64_u128 (a b : BoundedNat (2^64)) :
    ((convert a * convert b : BoundedNat (2^128))).val = a.val * b.val :=
  bn_widen_mul_val_u64_u128 a b

@[simp] theorem widen_mul_val_u128_u256 (a b : BoundedNat (2^128)) :
    ((convert a * convert b : BoundedNat (2^256))).val = a.val * b.val :=
  bn_widen_mul_val_u128_u256 a b

end BoundedNat

/-! #### Add/sub cancellation and nested-div collapse -/

section BnCancel

variable {bound : Nat}

/-- `(a - b) + b = a` under `b ≤ a`. The add re-fit is automatic:
`(a.val - b.val) + b.val = a.val < bound`. -/
theorem bn_sub_add_cancel (a b : BoundedNat bound) (h : b.val ≤ a.val) :
    BoundedNat.add (BoundedNat.sub a b) b = a := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  refine BoundedNat.ext ?_
  rw [bn_add_val_mod _ _ hb, bn_sub_val_eq, Nat.sub_add_cancel h,
    Nat.mod_eq_of_lt a.property]

/-- `(a + b) - b = a` under the no-overflow hypothesis (false without it:
the wrapped sum loses the high bits before the subtraction). -/
theorem bn_add_sub_cancel (a b : BoundedNat bound)
    (h : a.val + b.val < bound) :
    BoundedNat.sub (BoundedNat.add a b) b = a := by
  refine BoundedNat.ext ?_
  rw [bn_sub_val_eq, bn_add_val_of_lt a b h, Nat.add_sub_cancel]

/-- Nested division collapses to division by the product, under the
product-fit hypothesis (`mul b c` must not wrap). -/
theorem bn_div_div_eq_div_mul (a b c : BoundedNat bound)
    (h : b.val * c.val < bound) :
    BoundedNat.div (BoundedNat.div a b) c =
      BoundedNat.div a (BoundedNat.mul b c) := by
  refine BoundedNat.ext ?_
  rw [bn_div_val_eq, bn_div_val_eq, bn_div_val_eq, bn_mul_val_of_lt b c h]
  exact Nat.div_div_eq_div_mul a.val b.val c.val

end BnCancel

namespace BoundedNat

variable {bound : Nat}

/-- `bn_sub_add_cancel` at the operator head. -/
theorem sub_add_cancel (a b : BoundedNat bound) (h : b.val ≤ a.val) :
    (a - b) + b = a :=
  bn_sub_add_cancel a b h

/-- `bn_add_sub_cancel` at the operator head. -/
theorem add_sub_cancel (a b : BoundedNat bound) (h : a.val + b.val < bound) :
    (a + b) - b = a :=
  bn_add_sub_cancel a b h

/-- `bn_div_div_eq_div_mul` at the operator head. -/
theorem div_div_eq_div_mul (a b c : BoundedNat bound)
    (h : b.val * c.val < bound) : a / b / c = a / (b * c) :=
  bn_div_div_eq_div_mul a b c h

end BoundedNat

-- smoke tests: the tier-1 shapes as a consumer states them
example (amt fee scale : BoundedNat (2^64))
    (hfit : amt.val * fee.val < 2^64) (h : fee.val ≤ scale.val) :
    (amt * fee / scale).val ≤ amt.val :=
  BoundedNat.mul_div_val_le_of_le amt fee scale hfit h

example (a b : BoundedNat (2^64)) :
    (BoundedNat.mul (BoundedNat.convert a) (BoundedNat.convert b) :
      BoundedNat (2^128)).val = a.val * b.val := by
  simp

example (bal amt : BoundedNat (2^64)) (h : amt.val ≤ bal.val) :
    (bal - amt) + amt = bal :=
  BoundedNat.sub_add_cancel bal amt h

/-! ### Wrapping ring laws (pass 2, tier 2)

Surveyed: none present. All UNCONDITIONAL -- commutativity, associativity and
distributivity survive wrapping because `% bound` is a ring homomorphism (the
same fact that makes `U64Pow.pow_while_val` unconditional). The `bound = 0`
branch is degenerate but the laws still hold definitionally there, so no
positivity hypothesis is needed anywhere. Identities are `@[simp]`
(unconditional, literal-triggered); comm/assoc/distrib are citation-only --
AC lemmas loop plain simp. -/

section BnRingLaws

variable {bound : Nat}

private theorem bn_mod_mul_mod {x y m : Nat} (h : 0 < m) :
    x % m * y % m = x * y % m := by
  rw [Nat.mul_mod, Nat.mod_eq_of_lt (Nat.mod_lt x h), ← Nat.mul_mod]

private theorem bn_mul_mod_mod {x y m : Nat} (h : 0 < m) :
    x * (y % m) % m = x * y % m := by
  rw [Nat.mul_mod x (y % m), Nat.mod_eq_of_lt (Nat.mod_lt y h), ← Nat.mul_mod]

theorem bn_add_comm (a b : BoundedNat bound) :
    BoundedNat.add a b = BoundedNat.add b a := by
  by_cases h : bound > 0
  · exact BoundedNat.ext
      (by rw [bn_add_val_mod a b h, bn_add_val_mod b a h, Nat.add_comm])
  · unfold BoundedNat.add
    rw [dif_neg h, dif_neg h]

theorem bn_mul_comm (a b : BoundedNat bound) :
    BoundedNat.mul a b = BoundedNat.mul b a := by
  by_cases h : bound > 0
  · exact BoundedNat.ext
      (by rw [bn_mul_val_mod a b h, bn_mul_val_mod b a h, Nat.mul_comm])
  · unfold BoundedNat.mul
    rw [dif_neg h, dif_neg h]

theorem bn_add_assoc (a b c : BoundedNat bound) :
    BoundedNat.add (BoundedNat.add a b) c =
      BoundedNat.add a (BoundedNat.add b c) := by
  by_cases h : bound > 0
  · refine BoundedNat.ext ?_
    rw [bn_add_val_mod _ c h, bn_add_val_mod a b h, bn_add_val_mod a _ h,
      bn_add_val_mod b c h, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
  · exact absurd (BoundedNat.bound_pos a) h

theorem bn_mul_assoc (a b c : BoundedNat bound) :
    BoundedNat.mul (BoundedNat.mul a b) c =
      BoundedNat.mul a (BoundedNat.mul b c) := by
  by_cases h : bound > 0
  · refine BoundedNat.ext ?_
    rw [bn_mul_val_mod _ c h, bn_mul_val_mod a b h, bn_mul_val_mod a _ h,
      bn_mul_val_mod b c h, bn_mod_mul_mod h, bn_mul_mod_mod h, Nat.mul_assoc]
  · exact absurd (BoundedNat.bound_pos a) h

/-- Left distributivity (wrapping). -/
theorem bn_mul_add (a b c : BoundedNat bound) :
    BoundedNat.mul a (BoundedNat.add b c) =
      BoundedNat.add (BoundedNat.mul a b) (BoundedNat.mul a c) := by
  by_cases h : bound > 0
  · refine BoundedNat.ext ?_
    rw [bn_mul_val_mod a _ h, bn_add_val_mod b c h, bn_mul_mod_mod h,
      Nat.mul_add, bn_add_val_mod _ _ h, bn_mul_val_mod a b h,
      bn_mul_val_mod a c h, Nat.mod_add_mod, Nat.add_mod_mod]
  · unfold BoundedNat.mul BoundedNat.add
    rw [dif_neg h, dif_neg h]

/-- Right distributivity (wrapping). -/
theorem bn_add_mul (a b c : BoundedNat bound) :
    BoundedNat.mul (BoundedNat.add a b) c =
      BoundedNat.add (BoundedNat.mul a c) (BoundedNat.mul b c) := by
  by_cases h : bound > 0
  · refine BoundedNat.ext ?_
    rw [bn_mul_val_mod _ c h, bn_add_val_mod a b h, bn_mod_mul_mod h,
      Nat.add_mul, bn_add_val_mod _ _ h, bn_mul_val_mod a c h,
      bn_mul_val_mod b c h, Nat.mod_add_mod, Nat.add_mod_mod]
  · exact absurd (BoundedNat.bound_pos a) h

theorem bn_add_zero [NeZero bound] (a : BoundedNat bound) :
    BoundedNat.add a (0 : BoundedNat bound) = a := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  refine BoundedNat.ext ?_
  rw [bn_add_val_mod a _ hb, BoundedNat.val_ofNat hb, Nat.add_zero,
    Nat.mod_eq_of_lt a.property]

theorem bn_zero_add [NeZero bound] (a : BoundedNat bound) :
    BoundedNat.add (0 : BoundedNat bound) a = a := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  refine BoundedNat.ext ?_
  rw [bn_add_val_mod _ a hb, BoundedNat.val_ofNat hb, Nat.zero_add,
    Nat.mod_eq_of_lt a.property]

theorem bn_mul_zero [NeZero bound] (a : BoundedNat bound) :
    BoundedNat.mul a (0 : BoundedNat bound) = (0 : BoundedNat bound) := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  refine BoundedNat.ext ?_
  rw [bn_mul_val_mod a _ hb, BoundedNat.val_ofNat hb, Nat.mul_zero,
    Nat.zero_mod]

theorem bn_zero_mul [NeZero bound] (a : BoundedNat bound) :
    BoundedNat.mul (0 : BoundedNat bound) a = (0 : BoundedNat bound) := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  refine BoundedNat.ext ?_
  rw [bn_mul_val_mod _ a hb, BoundedNat.val_ofNat hb, Nat.zero_mul,
    Nat.zero_mod]

/-- `mul a 1 = a`, unconditional: the `bound = 1` degenerate case (where the
literal `1` wraps to `0`) still satisfies it -- every `BoundedNat 1` is `0`. -/
theorem bn_mul_one [NeZero bound] (a : BoundedNat bound) :
    BoundedNat.mul a (1 : BoundedNat bound) = a := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  by_cases h1 : 1 < bound
  · refine BoundedNat.ext ?_
    rw [bn_mul_val_mod a _ hb, BoundedNat.val_ofNat h1, Nat.mul_one,
      Nat.mod_eq_of_lt a.property]
  · refine BoundedNat.ext ?_
    have hm := (BoundedNat.mul a (1 : BoundedNat bound)).property
    have ha := a.property
    omega

theorem bn_one_mul [NeZero bound] (a : BoundedNat bound) :
    BoundedNat.mul (1 : BoundedNat bound) a = a := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  by_cases h1 : 1 < bound
  · refine BoundedNat.ext ?_
    rw [bn_mul_val_mod _ a hb, BoundedNat.val_ofNat h1, Nat.one_mul,
      Nat.mod_eq_of_lt a.property]
  · refine BoundedNat.ext ?_
    have hm := (BoundedNat.mul (1 : BoundedNat bound) a).property
    have ha := a.property
    omega

end BnRingLaws

namespace BoundedNat

variable {bound : Nat}

-- operator-head twins: comm/assoc/distrib citation-only, identities @[simp]
theorem add_comm (a b : BoundedNat bound) : a + b = b + a :=
  bn_add_comm a b

theorem mul_comm (a b : BoundedNat bound) : a * b = b * a :=
  bn_mul_comm a b

theorem add_assoc (a b c : BoundedNat bound) : a + b + c = a + (b + c) :=
  bn_add_assoc a b c

theorem mul_assoc (a b c : BoundedNat bound) : a * b * c = a * (b * c) :=
  bn_mul_assoc a b c

theorem mul_add (a b c : BoundedNat bound) : a * (b + c) = a * b + a * c :=
  bn_mul_add a b c

theorem add_mul (a b c : BoundedNat bound) : (a + b) * c = a * c + b * c :=
  bn_add_mul a b c

@[simp] theorem add_zero [NeZero bound] (a : BoundedNat bound) : a + (0 : BoundedNat bound) = a :=
  bn_add_zero a

@[simp] theorem zero_add [NeZero bound] (a : BoundedNat bound) : (0 : BoundedNat bound) + a = a :=
  bn_zero_add a

@[simp] theorem mul_zero [NeZero bound] (a : BoundedNat bound) :
    a * (0 : BoundedNat bound) = (0 : BoundedNat bound) :=
  bn_mul_zero a

@[simp] theorem zero_mul [NeZero bound] (a : BoundedNat bound) :
    (0 : BoundedNat bound) * a = (0 : BoundedNat bound) :=
  bn_zero_mul a

@[simp] theorem mul_one [NeZero bound] (a : BoundedNat bound) : a * (1 : BoundedNat bound) = a :=
  bn_mul_one a

@[simp] theorem one_mul [NeZero bound] (a : BoundedNat bound) : (1 : BoundedNat bound) * a = a :=
  bn_one_mul a

end BoundedNat

attribute [simp] bn_add_zero bn_zero_add bn_mul_zero bn_zero_mul bn_mul_one bn_one_mul

/-! ### Successor step at the literal head (pass 2, tier 2)

`bn_add_val_of_lt` is head-keyed on a general second operand, so a goal
carrying the literal `1` and a hypothesis `a.val + 1 < bound` still owes the
`(1 : BoundedNat bound).val = 1` collapse before the general lemma fires.
These state the fused special case; `1 < bound` is derivable from the
hypothesis itself (`a.val + 1 < bound` forces `bound ≥ 2`), so they stay
fully generic. -/

section BnSuccStep

variable {bound : Nat}

theorem bn_add_one_val_of_lt [NeZero bound] (a : BoundedNat bound) (h : a.val + 1 < bound) :
    (BoundedNat.add a (1 : BoundedNat bound)).val = a.val + 1 := by
  have h1 : (1 : BoundedNat bound).val = 1 :=
    BoundedNat.val_ofNat (show 1 < bound by omega)
  rw [bn_add_val_of_lt a _ (by rw [h1]; omega), h1]

theorem bn_add_one_aborts_eq_false_of_lt [NeZero bound] (a : BoundedNat bound)
    (h : a.val + 1 < bound) :
    BoundedNat.add_aborts a (1 : BoundedNat bound) = false := by
  have h1 : (1 : BoundedNat bound).val = 1 :=
    BoundedNat.val_ofNat (show 1 < bound by omega)
  rw [bn_add_aborts_eq_false_iff, h1]
  exact h

end BnSuccStep

namespace BoundedNat

variable {bound : Nat}

/-- `bn_add_one_val_of_lt` at the operator head. -/
theorem add_one_val_of_lt [NeZero bound] (a : BoundedNat bound) (h : a.val + 1 < bound) :
    (a + (1 : BoundedNat bound)).val = a.val + 1 :=
  bn_add_one_val_of_lt a h

end BoundedNat

-- smoke tests: ring laws at concrete widths, identity simp firing, successor
example (a b : BoundedNat (2^64)) : a * b = b * a := BoundedNat.mul_comm a b

example (a : BoundedNat (2^64)) : a + 0 = a := by simp

example (a : BoundedNat (2^128)) : (1 : BoundedNat (2^128)) * a = a := by simp

example (a b c : BoundedNat (2^256)) : a * (b + c) = a * b + a * c :=
  BoundedNat.mul_add a b c

example (i : BoundedNat (2^64)) (h : i.val + 1 < 2^64) :
    (i + 1).val = i.val + 1 :=
  BoundedNat.add_one_val_of_lt i h

/-! ### Shift-arithmetic cross-head bridges (pass 3, tier A)

`<<< k` IS `* 2^k` (wrapped) and `>>> k` IS `/ 2^k` (exact) -- stating the
crossings lets shift goals inherit the whole mul/div toolkit above
(pro-rata, monotonicity, Euclid, nested-div). Right shift is unconditional;
left shift gets the wrapped form unconditionally and the exact form under
the product-fit hypothesis, at all four head spellings (operator/named x
Nat-amount/BoundedNat-amount where they exist). -/

section BnShiftArith

variable {bound : Nat}

theorem bn_shl_val_mod_pow (a : BoundedNat bound) (k : Nat) :
    (BoundedNat.shiftLeft a k).val = (a.val * 2^k) % bound := by
  rw [← Nat.shiftLeft_eq]
  exact BoundedNat.shiftLeft_nat_val a k

theorem bn_shl_val_eq_mul_pow (a : BoundedNat bound) (k : Nat)
    (h : a.val * 2^k < bound) :
    (BoundedNat.shiftLeft a k).val = a.val * 2^k := by
  rw [bn_shl_val_of_lt a k (by rw [Nat.shiftLeft_eq]; exact h),
    Nat.shiftLeft_eq]

theorem bn_shr_val_eq_div_pow (a : BoundedNat bound) (k : Nat) :
    (BoundedNat.shiftRight a k).val = a.val / 2^k := by
  rw [bn_shr_val_eq, Nat.shiftRight_eq_div_pow]

end BnShiftArith

namespace BoundedNat

variable {bound : Nat}

theorem shiftLeft_nat_val_mod_pow (a : BoundedNat bound) (k : Nat) :
    (a <<< k).val = (a.val * 2^k) % bound := by
  rw [shiftLeft_nat_val, Nat.shiftLeft_eq]

theorem shiftLeft_nat_val_eq_mul_pow (a : BoundedNat bound) (k : Nat)
    (h : a.val * 2^k < bound) : (a <<< k).val = a.val * 2^k := by
  rw [shiftLeft_nat_val_of_lt a k (by rw [Nat.shiftLeft_eq]; exact h),
    Nat.shiftLeft_eq]

theorem shiftLeft_bounded_val_mod_pow {bound' : Nat} (a : BoundedNat bound)
    (k : BoundedNat bound') :
    (a <<< k).val = (a.val * 2^k.val) % bound := by
  rw [shiftLeft_bounded_val, Nat.shiftLeft_eq]

theorem shiftLeft_bounded_val_eq_mul_pow {bound' : Nat} (a : BoundedNat bound)
    (k : BoundedNat bound') (h : a.val * 2^k.val < bound) :
    (a <<< k).val = a.val * 2^k.val := by
  rw [shiftLeft_bounded_val_of_lt a k (by rw [Nat.shiftLeft_eq]; exact h),
    Nat.shiftLeft_eq]

theorem shiftRight_nat_val_eq_div_pow (a : BoundedNat bound) (k : Nat) :
    (a >>> k).val = a.val / 2^k := by
  rw [shiftRight_nat_val, Nat.shiftRight_eq_div_pow]

theorem shiftRight_bounded_val_eq_div_pow {bound' : Nat} (a : BoundedNat bound)
    (k : BoundedNat bound') : (a >>> k).val = a.val / 2^k.val := by
  rw [shiftRight_bounded_val, Nat.shiftRight_eq_div_pow]

end BoundedNat

/-! ### Exact-division round-trip (pass 3, tier A)

The tick-spacing reconstruction family: divisibility (as the `% = 0` form
the guards actually carry) makes `div` exactly invertible. The `b.val = 0`
degenerate case is covered by the hypothesis itself (`a.val % 0 = a.val = 0`
forces `a.val = 0`), so no positivity hypothesis is needed. -/

section BnExactDiv

variable {bound : Nat}

theorem bn_mul_div_cancel_of_mod_eq_zero (a b : BoundedNat bound)
    (h : a.val % b.val = 0) :
    BoundedNat.mul b (BoundedNat.div a b) = a := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  refine BoundedNat.ext ?_
  rw [bn_mul_val_mod _ _ hb, bn_div_val_eq,
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h),
    Nat.mod_eq_of_lt a.property]

theorem bn_div_mul_cancel_of_mod_eq_zero (a b : BoundedNat bound)
    (h : a.val % b.val = 0) :
    BoundedNat.mul (BoundedNat.div a b) b = a := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  refine BoundedNat.ext ?_
  rw [bn_mul_val_mod _ _ hb, bn_div_val_eq,
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h),
    Nat.mod_eq_of_lt a.property]

/-- Transport of the divisibility guard itself to `.val` form. -/
theorem bn_mod_eq_zero_iff_val [NeZero bound] (a b : BoundedNat bound) :
    BoundedNat.mod a b = (0 : BoundedNat bound) ↔ a.val % b.val = 0 := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  rw [← bn_val_inj, bn_mod_val_eq, BoundedNat.val_ofNat hb]

end BnExactDiv

namespace BoundedNat

variable {bound : Nat}

theorem mul_div_cancel_of_mod_eq_zero (a b : BoundedNat bound)
    (h : a.val % b.val = 0) : b * (a / b) = a :=
  bn_mul_div_cancel_of_mod_eq_zero a b h

theorem div_mul_cancel_of_mod_eq_zero (a b : BoundedNat bound)
    (h : a.val % b.val = 0) : (a / b) * b = a :=
  bn_div_mul_cancel_of_mod_eq_zero a b h

theorem mod_eq_zero_iff_val [NeZero bound] (a b : BoundedNat bound) :
    a % b = (0 : BoundedNat bound) ↔ a.val % b.val = 0 :=
  bn_mod_eq_zero_iff_val a b

end BoundedNat

/-! ### Sub interplay (pass 3, tier A)

`Nat.sub_sub` is unconditional, but the fused subtrahend `add b c` wraps --
the guard is on the ADD, not the subtraction. Monotonicity completes the
pass-1 domination fact (`bn_sub_val_le`), which was the only sub-order
bridge present. -/

section BnSubInterplay

variable {bound : Nat}

theorem bn_sub_sub (a b c : BoundedNat bound) (h : b.val + c.val < bound) :
    BoundedNat.sub (BoundedNat.sub a b) c =
      BoundedNat.sub a (BoundedNat.add b c) := by
  refine BoundedNat.ext ?_
  rw [bn_sub_val_eq, bn_sub_val_eq, bn_sub_val_eq, bn_add_val_of_lt b c h]
  exact Nat.sub_sub a.val b.val c.val

theorem bn_sub_val_mono_left (a a' b : BoundedNat bound)
    (h : a.val ≤ a'.val) :
    (BoundedNat.sub a b).val ≤ (BoundedNat.sub a' b).val := by
  rw [bn_sub_val_eq, bn_sub_val_eq]
  exact Nat.sub_le_sub_right h b.val

theorem bn_sub_val_anti_right (a b b' : BoundedNat bound)
    (h : b.val ≤ b'.val) :
    (BoundedNat.sub a b').val ≤ (BoundedNat.sub a b).val := by
  rw [bn_sub_val_eq, bn_sub_val_eq]
  exact Nat.sub_le_sub_left h a.val

end BnSubInterplay

namespace BoundedNat

variable {bound : Nat}

theorem sub_sub (a b c : BoundedNat bound) (h : b.val + c.val < bound) :
    (a - b) - c = a - (b + c) :=
  bn_sub_sub a b c h

theorem sub_val_mono_left (a a' b : BoundedNat bound) (h : a.val ≤ a'.val) :
    (a - b).val ≤ (a' - b).val :=
  bn_sub_val_mono_left a a' b h

theorem sub_val_anti_right (a b b' : BoundedNat bound) (h : b.val ≤ b'.val) :
    (a - b').val ≤ (a - b).val :=
  bn_sub_val_anti_right a b b' h

end BoundedNat

-- smoke tests: shift goals reach the mul/div toolkit; round-trip fires from
-- the guard form
example (a : BoundedNat (2^64)) (k : BoundedNat (2^8))
    (h : a.val * 2^k.val < 2^64) (b : BoundedNat (2^64))
    (hb : 2^k.val ≤ b.val) : (a <<< k).val * b.val ≥ a.val * 2^k.val := by
  rw [BoundedNat.shiftLeft_bounded_val_eq_mul_pow a k h]
  exact Nat.le_mul_of_pos_right _ (Nat.lt_of_lt_of_le (Nat.two_pow_pos k.val) hb)

example (tick spacing : BoundedNat (2^32))
    (h : tick % spacing = (0 : BoundedNat (2^32))) :
    spacing * (tick / spacing) = tick :=
  BoundedNat.mul_div_cancel_of_mod_eq_zero tick spacing
    ((BoundedNat.mod_eq_zero_iff_val tick spacing).mp h)

example (a b c : BoundedNat (2^64)) (h : b.val + c.val < 2^64) :
    (a - b) - c = a - (b + c) :=
  BoundedNat.sub_sub a b c h

/-! ### Bitwise domination, mod twins, BEq bridge (pass 3, tier B)

Survey results: bitwise domination absent (pass 1 added only the value
projections); `lor`'s right-domination is FALSE unconditionally -- the def
saturates to `a` when the OR overflows, dropping `b`'s bits -- so that face
carries the fit hypothesis, with the pow2 corollary unconditional.
`(lor a b).val ≤ a.val + b.val` is SKIPPED: not clean in bare core (no
`Nat.or_le_add`; momentum re-derives it privately via a 3-helper div2
induction, `SpecInt_ops.nat_or_le_add` -- banked as extraction evidence).
Mod twins and the BEq val-bridge were absent; min/max val-bridges are
already present (`min_val`/`max_val`, pass 0). -/

section BnBitDomination

variable {bound : Nat}

theorem bn_land_val_le_left (a b : BoundedNat bound) :
    (BoundedNat.land a b).val ≤ a.val := by
  rw [BoundedNat.land_val]
  exact Nat.and_le_left

theorem bn_land_val_le_right (a b : BoundedNat bound) :
    (BoundedNat.land a b).val ≤ b.val := by
  rw [BoundedNat.land_val]
  exact Nat.and_le_right

/-- Left domination is unconditional: even the saturation branch returns `a`. -/
theorem bn_lor_val_ge_left (a b : BoundedNat bound) :
    a.val ≤ (BoundedNat.lor a b).val := by
  unfold BoundedNat.lor
  split
  · exact Nat.left_le_or
  · exact Nat.le_refl a.val

/-- Right domination NEEDS the fit hypothesis: the saturation branch drops
`b`'s bits entirely. -/
theorem bn_lor_val_ge_right_of_lt (a b : BoundedNat bound)
    (h : a.val ||| b.val < bound) :
    b.val ≤ (BoundedNat.lor a b).val := by
  rw [BoundedNat.lor_val_of_lt a b h]
  exact Nat.right_le_or

/-- ... and is unconditional at a power-of-2 bound, where OR cannot overflow. -/
theorem bn_lor_val_ge_right_pow2 {n : Nat} (a b : BoundedNat (2^n)) :
    b.val ≤ (BoundedNat.lor a b).val := by
  rw [BoundedNat.lor_val_pow2]
  exact Nat.right_le_or

end BnBitDomination

namespace BoundedNat

variable {bound : Nat}

theorem and_val_le_left (a b : BoundedNat bound) : (a &&& b).val ≤ a.val :=
  bn_land_val_le_left a b

theorem and_val_le_right (a b : BoundedNat bound) : (a &&& b).val ≤ b.val :=
  bn_land_val_le_right a b

theorem or_val_ge_left (a b : BoundedNat bound) : a.val ≤ (a ||| b).val :=
  bn_lor_val_ge_left a b

theorem or_val_ge_right_of_lt (a b : BoundedNat bound)
    (h : a.val ||| b.val < bound) : b.val ≤ (a ||| b).val :=
  bn_lor_val_ge_right_of_lt a b h

theorem or_val_ge_right_pow2 {n : Nat} (a b : BoundedNat (2^n)) :
    b.val ≤ (a ||| b).val :=
  bn_lor_val_ge_right_pow2 a b

end BoundedNat

section BnModTwins

variable {bound : Nat}

/-- Mod is idempotent at the BN head (the `b.val = 0` branch is `a % 0 = a`,
idempotent trivially). -/
theorem bn_mod_mod_self (a b : BoundedNat bound) :
    BoundedNat.mod (BoundedNat.mod a b) b = BoundedNat.mod a b := by
  refine BoundedNat.ext ?_
  rw [bn_mod_val_eq, bn_mod_val_eq]
  by_cases h : 0 < b.val
  · exact Nat.mod_eq_of_lt (Nat.mod_lt a.val h)
  · have hb0 : b.val = 0 := by omega
    rw [hb0, Nat.mod_zero, Nat.mod_zero]

theorem bn_mod_self_eq_zero [NeZero bound] (a : BoundedNat bound) :
    BoundedNat.mod a a = (0 : BoundedNat bound) := by
  have hb : bound > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) a.property
  refine BoundedNat.ext ?_
  rw [bn_mod_val_eq, Nat.mod_self, BoundedNat.val_ofNat hb]

/-- A value already below the divisor is a fixed point of `mod`. -/
theorem bn_mod_eq_self_of_lt (a b : BoundedNat bound) (h : a.val < b.val) :
    BoundedNat.mod a b = a := by
  refine BoundedNat.ext ?_
  rw [bn_mod_val_eq]
  exact Nat.mod_eq_of_lt h

end BnModTwins

namespace BoundedNat

variable {bound : Nat}

theorem mod_mod_self (a b : BoundedNat bound) : (a % b) % b = a % b :=
  bn_mod_mod_self a b

theorem mod_self_eq_zero [NeZero bound] (a : BoundedNat bound) :
    a % a = (0 : BoundedNat bound) :=
  bn_mod_self_eq_zero a

theorem mod_eq_self_of_lt (a b : BoundedNat bound) (h : a.val < b.val) :
    a % b = a :=
  bn_mod_eq_self_of_lt a b h

end BoundedNat

section BnBeqBridge

variable {bound : Nat}

/-- The lawful-BEq face at `.val` level (`==` has a single head spelling). -/
theorem bn_beq_iff_val (a b : BoundedNat bound) :
    (a == b) = true ↔ a.val = b.val := by
  rw [BoundedNat.beq_eq_decide, decide_eq_true_eq]
  exact (bn_val_inj a b).symm

theorem bn_beq_eq_false_iff_val_ne (a b : BoundedNat bound) :
    (a == b) = false ↔ a.val ≠ b.val :=
  bool_eq_false_iff_not_of_iff (bn_beq_iff_val a b)

end BnBeqBridge

-- smoke tests: dominations feed omega; BEq guard transports to val form
example (mask bits : BoundedNat (2^64)) (h : mask.val < 2^32) :
    (bits &&& mask).val < 2^32 :=
  Nat.lt_of_le_of_lt (BoundedNat.and_val_le_right bits mask) h

example (flags bit : BoundedNat (2^256)) : flags.val ≤ (flags ||| bit).val :=
  BoundedNat.or_val_ge_left flags bit

example (a b : BoundedNat (2^64)) (h : (a == b) = true)
    (k : BoundedNat (2^64)) (hk : a.val < k.val) : b.val < k.val := by
  have := (bn_beq_iff_val a b).mp h
  omega
