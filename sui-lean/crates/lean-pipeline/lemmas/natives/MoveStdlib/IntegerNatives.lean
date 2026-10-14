-- Native implementations for std::integer::Integer
-- This is a spec-only type representing mathematical integers

import Prelude.BoundedNat
import Prover.MoveAutoAttr

namespace Integer

-- Integer is represented as Lean's Int (arbitrary precision signed integer)
abbrev Integer := Int

-- Euclidean (wrapping) conversion of a mathematical Int to a bounded unsigned.
-- Uses `Int.emod` (`%`), which is non-negative for a positive modulus, so
-- negative inputs wrap correctly (e.g. -1 ↦ bound-1). A truncating shape
-- `⟨x.toNat % bound, …⟩` is WRONG for negatives: `Int.toNat` sends every
-- negative to 0, so all negatives would collapse to 0.
private def toUnsigned (bound : Nat) (hbound : 0 < bound) (x : Integer) : BoundedNat bound :=
  let r : Int := x % (bound : Int)
  ⟨r.toNat, by
    have hboundInt : 0 < (bound : Int) := Int.ofNat_lt.mpr hbound
    have hnonzero : (bound : Int) ≠ 0 := Int.ne_of_gt hboundInt
    have hnonneg : 0 ≤ r := Int.emod_nonneg _ hnonzero
    have hlt : r < (bound : Int) := Int.emod_lt_of_pos _ hboundInt
    exact (Int.toNat_lt hnonneg).2 hlt
  ⟩

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

theorem toUnsigned_of_bounded {bound : Nat} (hbound : 0 < bound)
    (x : BoundedNat bound) :
    toUnsigned bound hbound (x.val : Int) = x := by
  apply BoundedNat.ext
  unfold toUnsigned
  change (((x.val : Int) % (bound : Int)).toNat) = x.val
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg x.val) (Int.ofNat_lt.mpr x.property)]
  rfl

@[move_effect] theorem from_u8_eq_val (x : BoundedNat (2^8)) :
    from_u8 x = (x.val : Int) := rfl

@[move_effect] theorem from_u16_eq_val (x : BoundedNat (2^16)) :
    from_u16 x = (x.val : Int) := rfl

@[move_effect] theorem from_u32_eq_val (x : BoundedNat (2^32)) :
    from_u32 x = (x.val : Int) := rfl

@[move_effect] theorem from_u64_eq_val (x : BoundedNat (2^64)) :
    from_u64 x = (x.val : Int) := rfl

@[move_effect] theorem from_u128_eq_val (x : BoundedNat (2^128)) :
    from_u128 x = (x.val : Int) := rfl

@[move_effect] theorem from_u256_eq_val (x : BoundedNat (2^256)) :
    from_u256 x = (x.val : Int) := rfl

@[move_effect] theorem to_u8_from_u8 (x : BoundedNat (2^8)) :
    to_u8 (from_u8 x) = x :=
  toUnsigned_of_bounded (by decide) x

@[move_effect] theorem to_u16_from_u16 (x : BoundedNat (2^16)) :
    to_u16 (from_u16 x) = x :=
  toUnsigned_of_bounded (by decide) x

@[move_effect] theorem to_u32_from_u32 (x : BoundedNat (2^32)) :
    to_u32 (from_u32 x) = x :=
  toUnsigned_of_bounded (by decide) x

@[move_effect] theorem to_u64_from_u64 (x : BoundedNat (2^64)) :
    to_u64 (from_u64 x) = x :=
  toUnsigned_of_bounded (by decide) x

@[move_effect] theorem to_u128_from_u128 (x : BoundedNat (2^128)) :
    to_u128 (from_u128 x) = x :=
  toUnsigned_of_bounded (by decide) x

@[move_effect] theorem to_u256_from_u256 (x : BoundedNat (2^256)) :
    to_u256 (from_u256 x) = x :=
  toUnsigned_of_bounded (by decide) x

@[move_effect] theorem to_u8_of_bounded_val (x : BoundedNat (2^8)) :
    to_u8 (x.val : Int) = x :=
  toUnsigned_of_bounded (by decide) x

@[move_effect] theorem to_u16_of_bounded_val (x : BoundedNat (2^16)) :
    to_u16 (x.val : Int) = x :=
  toUnsigned_of_bounded (by decide) x

@[move_effect] theorem to_u32_of_bounded_val (x : BoundedNat (2^32)) :
    to_u32 (x.val : Int) = x :=
  toUnsigned_of_bounded (by decide) x

@[move_effect] theorem to_u64_of_bounded_val (x : BoundedNat (2^64)) :
    to_u64 (x.val : Int) = x :=
  toUnsigned_of_bounded (by decide) x

@[move_effect] theorem to_u128_of_bounded_val (x : BoundedNat (2^128)) :
    to_u128 (x.val : Int) = x :=
  toUnsigned_of_bounded (by decide) x

@[move_effect] theorem to_u256_of_bounded_val (x : BoundedNat (2^256)) :
    to_u256 (x.val : Int) = x :=
  toUnsigned_of_bounded (by decide) x

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

-- Two's-complement-correct signed bitwise ops (ported from legacy lemmas,
-- commit fa944f0e; 5140e73b ported only the Euclidean to_uN half). The naive
-- `x.toNat &&& y.toNat` is WRONG for negatives (`Int.toNat` sends every negative
-- to 0), which breaks the signed I32/I64/I128 `and`/`or`/`xor` correctness specs.
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

theorem lt_iff_lt (x y : Integer) : lt x y ↔ x < y := Iff.rfl
theorem le_iff_le (x y : Integer) : le x y ↔ x ≤ y := Iff.rfl
theorem lte_iff_le (x y : Integer) : lte x y ↔ x ≤ y := Iff.rfl
theorem gt_iff_gt (x y : Integer) : gt x y ↔ x > y := Iff.rfl
theorem ge_iff_ge (x y : Integer) : ge x y ↔ x ≥ y := Iff.rfl
theorem gte_iff_ge (x y : Integer) : gte x y ↔ x ≥ y := Iff.rfl
theorem is_neg_iff_lt_zero (x : Integer) : is_neg x ↔ x < 0 := Iff.rfl
theorem is_pos_iff_nonneg (x : Integer) : is_pos x ↔ 0 ≤ x := Iff.rfl

theorem not_is_neg_iff_is_pos (x : Integer) : ¬ is_neg x ↔ is_pos x := by
  change (¬ x < 0) ↔ 0 ≤ x
  exact Int.not_lt

theorem not_is_pos_iff_is_neg (x : Integer) : ¬ is_pos x ↔ is_neg x := by
  change (¬ 0 ≤ x) ↔ x < 0
  exact Int.not_le

theorem lt_of_is_neg_of_is_pos {x y : Integer}
    (hx : is_neg x) (hy : is_pos y) : lt x y := by
  exact Int.lt_of_lt_of_le hx hy

theorem not_lt_of_is_pos_of_is_neg {x y : Integer}
    (hx : is_pos x) (hy : is_neg y) : ¬ lt x y := by
  exact Int.not_lt_of_ge (Int.le_trans (Int.le_of_lt hy) hx)

theorem gt_of_is_pos_of_is_neg {x y : Integer}
    (hx : is_pos x) (hy : is_neg y) : gt x y := by
  exact Int.lt_of_lt_of_le hy hx

theorem not_gt_of_is_neg_of_is_pos {x y : Integer}
    (hx : is_neg x) (hy : is_pos y) : ¬ gt x y := by
  exact Int.not_lt_of_ge (Int.le_trans (Int.le_of_lt hx) hy)

def abs (x : Integer) : Integer := if x < 0 then -x else x

@[move_effect] theorem abs_of_nonneg {x : Integer} (h : 0 ≤ x) :
    abs x = x := by
  simp [abs, Int.not_lt.mpr h]

@[move_effect] theorem abs_of_neg {x : Integer} (h : x < 0) :
    abs x = -x := by
  simp [abs, h]

@[move_effect] theorem abs_nonneg (x : Integer) :
    0 ≤ abs x := by
  by_cases h : x < 0
  · rw [abs_of_neg h]
    exact Int.neg_nonneg_of_nonpos (Int.le_of_lt h)
  · have h_nonneg := Int.le_of_not_gt h
    rw [abs_of_nonneg h_nonneg]
    exact h_nonneg

@[move_effect] theorem abs_neg (x : Integer) :
    abs (-x) = abs x := by
  by_cases h : x < 0
  · rw [abs_of_neg h,
      abs_of_nonneg (Int.neg_nonneg_of_nonpos (Int.le_of_lt h))]
  · have h_nonneg : 0 ≤ x := Int.le_of_not_gt h
    by_cases h_zero : x = 0
    · subst x
      rfl
    · have h_pos : 0 < x := by
        apply Int.lt_of_not_ge
        intro h_nonpos
        exact h_zero (Int.le_antisymm h_nonpos h_nonneg)
      rw [abs_of_nonneg h_nonneg, abs_of_neg (Int.neg_lt_zero_iff.mpr h_pos)]
      simp

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

def signedValue (modulus midpoint value : Nat) : Integer :=
  if value < midpoint then (value : Int) else (value : Int) - (modulus : Int)

theorem signedValue_of_lt {modulus midpoint value : Nat}
    (h : value < midpoint) :
    signedValue modulus midpoint value = (value : Int) := by
  simp [signedValue, h]

theorem signedValue_of_not_lt {modulus midpoint value : Nat}
    (h : ¬ value < midpoint) :
    signedValue modulus midpoint value =
      (value : Int) - (modulus : Int) := by
  simp [signedValue, h]

theorem signedValue_is_neg_iff {modulus midpoint value : Nat}
    (h_value : value < modulus) :
    is_neg (signedValue modulus midpoint value) ↔ midpoint ≤ value := by
  by_cases h_sign : value < midpoint
  · have h_not_ge : ¬ midpoint ≤ value := Nat.not_le_of_gt h_sign
    rw [signedValue_of_lt h_sign]
    exact iff_of_false (Int.not_lt_of_ge (Int.natCast_nonneg value)) h_not_ge
  · have h_ge : midpoint ≤ value := Nat.le_of_not_gt h_sign
    have h_cast : (value : Int) < (modulus : Int) := Int.ofNat_lt.mpr h_value
    have h_negative : (value : Int) - (modulus : Int) < 0 := by
      omega
    rw [signedValue_of_not_lt h_sign]
    exact iff_of_true h_negative h_ge

theorem signedValue_is_pos_iff {modulus midpoint value : Nat}
    (h_value : value < modulus) :
    is_pos (signedValue modulus midpoint value) ↔ value < midpoint := by
  by_cases h_sign : value < midpoint
  · rw [signedValue_of_lt h_sign]
    exact iff_of_true (Int.natCast_nonneg value) h_sign
  · have h_cast : (value : Int) < (modulus : Int) := Int.ofNat_lt.mpr h_value
    have h_negative : (value : Int) - (modulus : Int) < 0 := by
      omega
    have h_not_nonnegative :
        ¬ 0 ≤ (value : Int) - (modulus : Int) := Int.not_le.mpr h_negative
    rw [signedValue_of_not_lt h_sign]
    exact iff_of_false h_not_nonnegative h_sign

theorem signedValue_inj_iff {modulus midpoint a b : Nat}
    (ha : a < modulus) (hb : b < modulus) :
    signedValue modulus midpoint a = signedValue modulus midpoint b ↔ a = b := by
  constructor
  · intro h
    have h_sign : midpoint ≤ a ↔ midpoint ≤ b := by
      rw [← signedValue_is_neg_iff ha, ← signedValue_is_neg_iff hb, h]
    by_cases hsa : a < midpoint
    · have h_not_ge_a : ¬ midpoint ≤ a := Nat.not_le_of_gt hsa
      have h_not_ge_b : ¬ midpoint ≤ b := fun h_ge => h_not_ge_a (h_sign.mpr h_ge)
      have hsb : b < midpoint := Nat.lt_of_not_ge h_not_ge_b
      rw [signedValue_of_lt hsa, signedValue_of_lt hsb] at h
      exact Int.ofNat_inj.mp h
    · have h_ge_a : midpoint ≤ a := Nat.le_of_not_gt hsa
      have h_ge_b : midpoint ≤ b := h_sign.mp h_ge_a
      have hsb : ¬ b < midpoint := Nat.not_lt_of_ge h_ge_b
      rw [signedValue_of_not_lt hsa, signedValue_of_not_lt hsb] at h
      exact Int.ofNat_inj.mp ((Int.sub_left_inj (modulus : Int)).mp h)
  · intro h
    subst b
    rfl

theorem signedValue_lt_iff {modulus midpoint a b : Nat}
    (ha : a < modulus) (hb : b < modulus) :
    lt (signedValue modulus midpoint a) (signedValue modulus midpoint b) ↔
      (midpoint ≤ a ∧ b < midpoint) ∨
      ((a < midpoint ↔ b < midpoint) ∧ a < b) := by
  unfold lt signedValue
  by_cases hsa : a < midpoint
  · by_cases hsb : b < midpoint
    · have h_not_ge_a : ¬ midpoint ≤ a := Nat.not_le_of_gt hsa
      simpa [hsa, hsb, h_not_ge_a] using (Int.ofNat_lt (n := a) (m := b))
    · have h_cast : (b : Int) < (modulus : Int) := Int.ofNat_lt.mpr hb
      have h_negative : (b : Int) - (modulus : Int) < 0 := by
        omega
      have h_not :
          ¬ (a : Int) < (b : Int) - (modulus : Int) :=
        Int.not_lt_of_ge
          (Int.le_trans (Int.le_of_lt h_negative) (Int.natCast_nonneg a))
      simp [hsa, hsb, h_not]
  · by_cases hsb : b < midpoint
    · have h_cast : (a : Int) < (modulus : Int) := Int.ofNat_lt.mpr ha
      have h_negative : (a : Int) - (modulus : Int) < 0 := by
        omega
      have h_lt :
          (a : Int) - (modulus : Int) < (b : Int) :=
        Int.lt_of_lt_of_le h_negative (Int.natCast_nonneg b)
      simp [hsa, hsb, h_lt, Nat.le_of_not_gt hsa]
    · have h_cancel :
          ((a : Int) - (modulus : Int) < (b : Int) - (modulus : Int)) ↔
            (a : Int) < (b : Int) := by
        simpa [Int.sub_eq_add_neg] using
          (Int.add_lt_add_iff_right (a := (a : Int)) (b := (b : Int))
            (-(modulus : Int)))
      simpa [hsa, hsb] using h_cancel.trans Int.ofNat_lt

theorem signedValue_le_iff {modulus midpoint a b : Nat}
    (ha : a < modulus) (hb : b < modulus) :
    le (signedValue modulus midpoint a) (signedValue modulus midpoint b) ↔
      (midpoint ≤ a ∧ b < midpoint) ∨
      ((a < midpoint ↔ b < midpoint) ∧ a ≤ b) := by
  unfold le signedValue
  by_cases hsa : a < midpoint
  · by_cases hsb : b < midpoint
    · have h_not_ge_a : ¬ midpoint ≤ a := Nat.not_le_of_gt hsa
      simpa [hsa, hsb, h_not_ge_a] using (Int.ofNat_le (m := a) (n := b))
    · have h_cast : (b : Int) < (modulus : Int) := Int.ofNat_lt.mpr hb
      have h_negative : (b : Int) - (modulus : Int) < 0 := by
        omega
      have h_not :
          ¬ (a : Int) ≤ (b : Int) - (modulus : Int) :=
        Int.not_le_of_gt
          (Int.lt_of_lt_of_le h_negative (Int.natCast_nonneg a))
      simp [hsa, hsb, h_not]
  · by_cases hsb : b < midpoint
    · have h_cast : (a : Int) < (modulus : Int) := Int.ofNat_lt.mpr ha
      have h_negative : (a : Int) - (modulus : Int) < 0 := by
        omega
      have h_le :
          (a : Int) - (modulus : Int) ≤ (b : Int) :=
        Int.le_trans (Int.le_of_lt h_negative) (Int.natCast_nonneg b)
      simp [hsa, hsb, h_le, Nat.le_of_not_gt hsa]
    · have h_cancel :
          ((a : Int) - (modulus : Int) ≤ (b : Int) - (modulus : Int)) ↔
            (a : Int) ≤ (b : Int) := by
        simpa [Int.sub_eq_add_neg] using
          (Int.add_le_add_iff_right (a := (a : Int)) (b := (b : Int))
            (-(modulus : Int)))
      simpa [hsa, hsb] using h_cancel.trans Int.ofNat_le

theorem signedValue_lte_iff {modulus midpoint a b : Nat}
    (ha : a < modulus) (hb : b < modulus) :
    lte (signedValue modulus midpoint a) (signedValue modulus midpoint b) ↔
      (midpoint ≤ a ∧ b < midpoint) ∨
      ((a < midpoint ↔ b < midpoint) ∧ a ≤ b) :=
  signedValue_le_iff ha hb

theorem signedValue_gt_iff {modulus midpoint a b : Nat}
    (ha : a < modulus) (hb : b < modulus) :
    gt (signedValue modulus midpoint a) (signedValue modulus midpoint b) ↔
      (midpoint ≤ b ∧ a < midpoint) ∨
      ((b < midpoint ↔ a < midpoint) ∧ b < a) :=
  signedValue_lt_iff hb ha

theorem signedValue_ge_iff {modulus midpoint a b : Nat}
    (ha : a < modulus) (hb : b < modulus) :
    ge (signedValue modulus midpoint a) (signedValue modulus midpoint b) ↔
      (midpoint ≤ b ∧ a < midpoint) ∨
      ((b < midpoint ↔ a < midpoint) ∧ b ≤ a) :=
  signedValue_le_iff hb ha

theorem signedValue_gte_iff {modulus midpoint a b : Nat}
    (ha : a < modulus) (hb : b < modulus) :
    gte (signedValue modulus midpoint a) (signedValue modulus midpoint b) ↔
      (midpoint ≤ b ∧ a < midpoint) ∨
      ((b < midpoint ↔ a < midpoint) ∧ b ≤ a) :=
  signedValue_le_iff hb ha

@[move_effect] theorem signedValue_bounded_is_neg_iff
    {modulus midpoint : Nat} (value : BoundedNat modulus) :
    is_neg (signedValue modulus midpoint value.val) ↔
      midpoint ≤ value.val :=
  signedValue_is_neg_iff value.property

@[move_effect] theorem signedValue_bounded_is_pos_iff
    {modulus midpoint : Nat} (value : BoundedNat modulus) :
    is_pos (signedValue modulus midpoint value.val) ↔
      value.val < midpoint :=
  signedValue_is_pos_iff value.property

@[move_effect] theorem signedValue_bounded_inj_iff
    {modulus midpoint : Nat} (a b : BoundedNat modulus) :
    signedValue modulus midpoint a.val =
      signedValue modulus midpoint b.val ↔ a.val = b.val :=
  signedValue_inj_iff a.property b.property

@[move_effect] theorem signedValue_bounded_lt_iff
    {modulus midpoint : Nat} (a b : BoundedNat modulus) :
    lt (signedValue modulus midpoint a.val)
        (signedValue modulus midpoint b.val) ↔
      (midpoint ≤ a.val ∧ b.val < midpoint) ∨
      ((a.val < midpoint ↔ b.val < midpoint) ∧ a.val < b.val) :=
  signedValue_lt_iff a.property b.property

@[move_effect] theorem signedValue_bounded_le_iff
    {modulus midpoint : Nat} (a b : BoundedNat modulus) :
    le (signedValue modulus midpoint a.val)
        (signedValue modulus midpoint b.val) ↔
      (midpoint ≤ a.val ∧ b.val < midpoint) ∨
      ((a.val < midpoint ↔ b.val < midpoint) ∧ a.val ≤ b.val) :=
  signedValue_le_iff a.property b.property

@[move_effect] theorem signedValue_bounded_lte_iff
    {modulus midpoint : Nat} (a b : BoundedNat modulus) :
    lte (signedValue modulus midpoint a.val)
        (signedValue modulus midpoint b.val) ↔
      (midpoint ≤ a.val ∧ b.val < midpoint) ∨
      ((a.val < midpoint ↔ b.val < midpoint) ∧ a.val ≤ b.val) :=
  signedValue_lte_iff a.property b.property

@[move_effect] theorem signedValue_bounded_gt_iff
    {modulus midpoint : Nat} (a b : BoundedNat modulus) :
    gt (signedValue modulus midpoint a.val)
        (signedValue modulus midpoint b.val) ↔
      (midpoint ≤ b.val ∧ a.val < midpoint) ∨
      ((b.val < midpoint ↔ a.val < midpoint) ∧ b.val < a.val) :=
  signedValue_gt_iff a.property b.property

@[move_effect] theorem signedValue_bounded_ge_iff
    {modulus midpoint : Nat} (a b : BoundedNat modulus) :
    ge (signedValue modulus midpoint a.val)
        (signedValue modulus midpoint b.val) ↔
      (midpoint ≤ b.val ∧ a.val < midpoint) ∨
      ((b.val < midpoint ↔ a.val < midpoint) ∧ b.val ≤ a.val) :=
  signedValue_ge_iff a.property b.property

@[move_effect] theorem signedValue_bounded_gte_iff
    {modulus midpoint : Nat} (a b : BoundedNat modulus) :
    gte (signedValue modulus midpoint a.val)
        (signedValue modulus midpoint b.val) ↔
      (midpoint ≤ b.val ∧ a.val < midpoint) ∨
      ((b.val < midpoint ↔ a.val < midpoint) ∧ b.val ≤ a.val) :=
  signedValue_gte_iff a.property b.property

theorem if_le_eq_signedValue (value signedMax unsignedMax : Nat) :
    (if value ≤ signedMax then
      (value : Int)
    else
      (value : Int) - (unsignedMax : Int) - 1) =
      signedValue (unsignedMax + 1) (signedMax + 1) value := by
  unfold signedValue
  by_cases h : value ≤ signedMax
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]
    omega

@[move_effect] theorem signed_from_u8_eq_signedValue (x : BoundedNat (2^8)) :
    signed_from_u8 x = signedValue (2^8) (2^7) x.val := by
  unfold signed_from_u8 from_u8
  simpa using if_le_eq_signedValue x.val 0x7f 0xff

@[move_effect] theorem signed_from_u16_eq_signedValue (x : BoundedNat (2^16)) :
    signed_from_u16 x = signedValue (2^16) (2^15) x.val := by
  unfold signed_from_u16 from_u16
  simpa using if_le_eq_signedValue x.val 0x7fff 0xffff

@[move_effect] theorem signed_from_u32_eq_signedValue (x : BoundedNat (2^32)) :
    signed_from_u32 x = signedValue (2^32) (2^31) x.val := by
  unfold signed_from_u32 from_u32
  change
    (if x.val ≤ 2147483647 then
      (x.val : Int)
    else
      (x.val : Int) - 4294967295 - 1) =
      signedValue 4294967296 2147483648 x.val
  exact if_le_eq_signedValue x.val 2147483647 4294967295

@[move_effect] theorem signed_from_u64_eq_signedValue (x : BoundedNat (2^64)) :
    signed_from_u64 x = signedValue (2^64) (2^63) x.val := by
  unfold signed_from_u64 from_u64
  change
    (if x.val ≤ 9223372036854775807 then
      (x.val : Int)
    else
      (x.val : Int) - 18446744073709551615 - 1) =
      signedValue 18446744073709551616 9223372036854775808 x.val
  exact if_le_eq_signedValue x.val 9223372036854775807 18446744073709551615

@[move_effect] theorem signed_from_u128_eq_signedValue (x : BoundedNat (2^128)) :
    signed_from_u128 x = signedValue (2^128) (2^127) x.val := by
  unfold signed_from_u128 from_u128
  change
    (if x.val ≤ 170141183460469231731687303715884105727 then
      (x.val : Int)
    else
      (x.val : Int) - 340282366920938463463374607431768211455 - 1) =
      signedValue
        340282366920938463463374607431768211456
        170141183460469231731687303715884105728
        x.val
  exact if_le_eq_signedValue x.val
    170141183460469231731687303715884105727
    340282366920938463463374607431768211455

@[move_effect] theorem signed_from_u256_eq_signedValue (x : BoundedNat (2^256)) :
    signed_from_u256 x = signedValue (2^256) (2^255) x.val := by
  unfold signed_from_u256 from_u256
  simpa using if_le_eq_signedValue x.val
    0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
    0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

@[simp]
theorem boundedNat_u64_add_aborts_eq_not_integer_lte_max
    (a b : BoundedNat (2^64)) :
    BoundedNat.add_aborts a b =
      !(Integer.lte
        (Integer.add (Integer.from_u64 a) (Integer.from_u64 b))
        (Integer.from_u64 (18446744073709551615 : BoundedNat (2^64)))) := by
  unfold BoundedNat.add_aborts BoundedNat.add_overflows
  unfold Integer.lte Integer.add Integer.from_u64
  have h_max :
      (18446744073709551615 : BoundedNat (2^64)).val =
        18446744073709551615 := rfl
  rw [h_max]
  by_cases h_over : a.val + b.val ≥ 2^64
  · have h_not_lte :
        ¬ (a.val : Int) + (b.val : Int) ≤
          (18446744073709551615 : Int) := by
      have h_pow : (2^64 : Nat) = 18446744073709551616 := rfl
      omega
    simp [h_over, h_not_lte]
    exact nat_blt_eq_false (Nat.not_lt_of_ge h_over)
  · have h_lte :
        (a.val : Int) + (b.val : Int) ≤
          (18446744073709551615 : Int) := by
      have h_pow : (2^64 : Nat) = 18446744073709551616 := rfl
      omega
    simp [h_over, h_lte]
    omega

theorem boundedNat_u64_not_over_of_integer_lte_max
    (a b : BoundedNat (2^64)) :
    Integer.lte
        (Integer.add (Integer.from_u64 a) (Integer.from_u64 b))
        (Integer.from_u64 (18446744073709551615 : BoundedNat (2^64))) →
      ¬ 18446744073709551616 ≤ a.val + b.val := by
  intro h_lte h_over
  have h_max :
      (18446744073709551615 : BoundedNat (2^64)).val =
        18446744073709551615 := rfl
  have h_lte_int :
      (a.val : Int) + (b.val : Int) ≤
        (18446744073709551615 : Int) := by
    simpa [Integer.lte, Integer.add, Integer.from_u64,
      h_max] using h_lte
  omega

theorem boundedNat_u64_over_of_not_integer_lte_max
    (a b : BoundedNat (2^64)) :
    ¬ Integer.lte
        (Integer.add (Integer.from_u64 a) (Integer.from_u64 b))
        (Integer.from_u64 (18446744073709551615 : BoundedNat (2^64))) →
      18446744073709551616 ≤ a.val + b.val := by
  intro h_not_lte
  have h_max :
      (18446744073709551615 : BoundedNat (2^64)).val =
        18446744073709551615 := rfl
  have h_not_lte_int :
      ¬ (a.val : Int) + (b.val : Int) ≤
        (18446744073709551615 : Int) := by
    simpa [Integer.lte, Integer.add, Integer.from_u64,
      h_max] using h_not_lte
  by_cases h_over : 18446744073709551616 ≤ a.val + b.val
  · exact h_over
  · exfalso
    apply h_not_lte_int
    omega

theorem boundedNat_u64_add_val_int_of_integer_lte_max
    (a b : BoundedNat (2^64))
    (h_lte :
      Integer.lte
        (Integer.add (Integer.from_u64 a) (Integer.from_u64 b))
        (Integer.from_u64 (18446744073709551615 : BoundedNat (2^64)))) :
    ((BoundedNat.add a b).val : Int) =
      Integer.add (Integer.from_u64 a) (Integer.from_u64 b) := by
  have h_not_over := boundedNat_u64_not_over_of_integer_lte_max a b h_lte
  have h_sum_lt : a.val + b.val < 2^64 := by
    have h_pow : (2^64 : Nat) = 18446744073709551616 := rfl
    omega
  change (((a + b).val : Nat) : Int) =
    Integer.add (Integer.from_u64 a) (Integer.from_u64 b)
  rw [BoundedNat.add_val_of_no_overflow _ _ h_sum_lt]
  simp [Integer.add, Integer.from_u64]

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
def div_round_up.aborts (_x _y : Integer) : Bool := false
def div_trunc.aborts (_x _y : Integer) : Bool := false
def mod_trunc.aborts (_x _y : Integer) : Bool := false

end Integer

@[simp]
theorem boundedNat_u64_add_aborts_eq_not_integer_lte_max
    (a b : BoundedNat (2^64)) :
    BoundedNat.add_aborts a b =
      !(Integer.lte
        (Integer.add (Integer.from_u64 a) (Integer.from_u64 b))
        (Integer.from_u64 (18446744073709551615 : BoundedNat (2^64)))) :=
  Integer.boundedNat_u64_add_aborts_eq_not_integer_lte_max a b

theorem boundedNat_u64_not_over_of_integer_lte_max
    (a b : BoundedNat (2^64)) :
    Integer.lte
        (Integer.add (Integer.from_u64 a) (Integer.from_u64 b))
        (Integer.from_u64 (18446744073709551615 : BoundedNat (2^64))) →
      ¬ 18446744073709551616 ≤ a.val + b.val :=
  Integer.boundedNat_u64_not_over_of_integer_lte_max a b

theorem boundedNat_u64_over_of_not_integer_lte_max
    (a b : BoundedNat (2^64)) :
    ¬ Integer.lte
        (Integer.add (Integer.from_u64 a) (Integer.from_u64 b))
        (Integer.from_u64 (18446744073709551615 : BoundedNat (2^64))) →
      18446744073709551616 ≤ a.val + b.val :=
  Integer.boundedNat_u64_over_of_not_integer_lte_max a b

theorem boundedNat_u64_add_val_int_of_integer_lte_max
    (a b : BoundedNat (2^64))
    (h_lte :
      Integer.lte
        (Integer.add (Integer.from_u64 a) (Integer.from_u64 b))
        (Integer.from_u64 (18446744073709551615 : BoundedNat (2^64)))) :
    ((BoundedNat.add a b).val : Int) =
      Integer.add (Integer.from_u64 a) (Integer.from_u64 b) :=
  Integer.boundedNat_u64_add_val_int_of_integer_lte_max a b h_lte
