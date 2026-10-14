/-
# Bounded Natural Numbers

Generic bounded natural number type that replaces UInt8, UInt16, UInt32, UInt64, UInt128, UInt256.

## Design

- Representation: { n : Nat // n < bound }
- Arithmetic (`add`/`sub`/`mul`) and narrowing casts (`convert`) are HONEST:
  the happy path carries its no-overflow/no-underflow proof and returns the
  exact value; the overflow path returns an OPAQUE junk value (`addJunk`,
  `subJunk`, `mulJunk`, `convertJunk`). Nothing is provable about junk except
  its bound, so proofs cannot silently exploit wrapping/saturation on paths
  where real Move aborts. The matching abort predicates (`add_overflows`,
  `sub_underflows`, `mul_overflows`, `convert_overflows`) expose the abort
  conditions for `.aborts` synthesis.
- Division/modulo keep the Nat conventions (`x / 0 = 0`, `x % 0 = x`); the
  division-by-zero abort is modeled separately in `.aborts` synthesis.
- Shifts follow Move semantics (left shift truncates high bits — that is real
  behavior, not junk).
- Bounds: maintained by construction; `BoundedNat 0` is uninhabited and every
  dead `bound = 0` branch is discharged by inhabitant elimination
  (`bound_pos`), NOT by an axiom.
-/

/-- A natural number bounded by a given limit -/
structure BoundedNat (bound : Nat) where
  val : Nat
  property : val < bound

namespace BoundedNat

variable {bound : Nat}

/-- Inhabitant elimination: any `BoundedNat bound` witnesses `bound > 0`.
Replaces the former (inconsistent) `BoundedNat_bound_zero_absurd` axiom in
dead `bound = 0` branches. -/
theorem bound_pos (a : BoundedNat bound) : bound > 0 :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) a.property

/-! ## Opaque junk values

Returned on the overflow/underflow/truncation paths. `opaque` (with a
compilation witness after `:=`) means Lean can prove NOTHING about these
values beyond their type — in particular no equation connects them to a
wrapped or saturated result. -/

/-- Opaque junk value returned by `add` on overflow. -/
opaque addJunk {bound : Nat} (a b : BoundedNat bound) : BoundedNat bound := a

/-- Opaque junk value returned by `sub` on underflow. -/
opaque subJunk {bound : Nat} (a b : BoundedNat bound) : BoundedNat bound := a

/-- Opaque junk value returned by `mul` on overflow. -/
opaque mulJunk {bound : Nat} (a b : BoundedNat bound) : BoundedNat bound := a

/-- Opaque junk value returned by `convert` when the value does not fit the
target bound (real Move `as` aborts here). -/
opaque convertJunk {bound_from bound_to : Nat} (a : BoundedNat bound_from)
    (h : 0 < bound_to) : BoundedNat bound_to := ⟨0, h⟩

/-- Opaque junk value backing the `OfNat` instance for out-of-bounds literals
(the generator only ever emits in-bounds literals). -/
opaque ofNatJunk (n : Nat) {bound : Nat} (h : 0 < bound) : BoundedNat bound := ⟨0, h⟩

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

@[simp] theorem lt_def {a b : BoundedNat bound} : (a < b) ↔ (a.val < b.val) := Iff.rfl
@[simp] theorem le_def {a b : BoundedNat bound} : (a ≤ b) ↔ (a.val ≤ b.val) := Iff.rfl

instance : DecidableRel (fun (a b : BoundedNat bound) => a < b) :=
  fun a b => inferInstanceAs (Decidable (a.val < b.val))

instance : DecidableRel (fun (a b : BoundedNat bound) => a ≤ b) :=
  fun a b => inferInstanceAs (Decidable (a.val ≤ b.val))

/-- Comparison -/
def compare (a b : BoundedNat bound) : Ordering :=
  if a.val < b.val then Ordering.lt
  else if a.val = b.val then Ordering.eq
  else Ordering.gt

/-- Addition. Exact on the no-overflow path, opaque junk on overflow (real
Move aborts there — see `add_overflows`). -/
def add (a b : BoundedNat bound) : BoundedNat bound :=
  if h : a.val + b.val < bound then
    ⟨a.val + b.val, h⟩
  else
    addJunk a b

/-- True iff `add a b` would overflow at the given bound. Reducible. -/
@[reducible] def add_overflows (a b : BoundedNat bound) : Bool :=
  decide (a.val + b.val ≥ bound)

/-- Subtraction. Exact on the no-underflow path, opaque junk on underflow
(real Move aborts there — see `sub_underflows`). -/
def sub (a b : BoundedNat bound) : BoundedNat bound :=
  if _h : b.val ≤ a.val then
    ⟨a.val - b.val, Nat.lt_of_le_of_lt (Nat.sub_le a.val b.val) a.property⟩
  else
    subJunk a b

/-- True iff `sub a b` would underflow. Reducible. -/
@[reducible] def sub_underflows (a b : BoundedNat bound) : Bool :=
  decide (a.val < b.val)

/-- Multiplication. Exact on the no-overflow path, opaque junk on overflow
(real Move aborts there — see `mul_overflows`). -/
def mul (a b : BoundedNat bound) : BoundedNat bound :=
  if h : a.val * b.val < bound then
    ⟨a.val * b.val, h⟩
  else
    mulJunk a b

/-- True iff `mul a b` would overflow at the given bound. Reducible. -/
@[reducible] def mul_overflows (a b : BoundedNat bound) : Bool :=
  decide (a.val * b.val ≥ bound)

/-- Division (never overflows; `x / 0 = 0` per Nat convention — the
division-by-zero abort is modeled in `.aborts` synthesis) -/
def div (a b : BoundedNat bound) : BoundedNat bound :=
  ⟨a.val / b.val, Nat.lt_of_le_of_lt (Nat.div_le_self a.val b.val) a.property⟩

/-- Modulo (never overflows when divisor > 0; `x % 0 = x` per Nat convention —
the modulo-by-zero abort is modeled in `.aborts` synthesis) -/
def mod (a b : BoundedNat bound) : BoundedNat bound :=
  if hb : b.val = 0 then
    -- When divisor is 0, return a (like Nat.mod)
    a
  else
    ⟨a.val % b.val, Nat.lt_of_lt_of_le (Nat.mod_lt a.val (Nat.pos_of_ne_zero hb)) (Nat.le_of_lt b.property)⟩

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
    -- unreachable for the power-of-2 bounds Move uses
    a

/-- Bitwise XOR -/
def bxor (a b : BoundedNat bound) : BoundedNat bound :=
  if h : a.val ^^^ b.val < bound then
    ⟨a.val ^^^ b.val, h⟩
  else
    -- unreachable for the power-of-2 bounds Move uses
    a

/-- Left shift (returns Option to handle overflow) -/
def shiftLeft? (a : BoundedNat bound) (k : Nat) : Option (BoundedNat bound) :=
  if h : a.val <<< k < bound then
    some ⟨a.val <<< k, h⟩
  else
    none

/-- Left shift (saturating to max value on overflow). NOT used by generated
code — the `HShiftLeft` instances below implement Move's truncating shift. -/
def shiftLeft (a : BoundedNat bound) (k : Nat) : BoundedNat bound :=
  match shiftLeft? a k with
  | some result => result
  | none => ⟨bound - 1, Nat.sub_lt (bound_pos a) (by omega)⟩

/-- Right shift (never overflows) -/
def shiftRight (a : BoundedNat bound) (k : Nat) : BoundedNat bound :=
  ⟨a.val >>> k, Nat.lt_of_le_of_lt (by simp [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self a.val (2^k)) a.property⟩

/-- Complement (bitwise NOT) for power-of-2 bounds -/
def complement (a : BoundedNat bound) (_h : ∃ n, bound = 2^n) : BoundedNat bound :=
  if hc : bound - 1 - a.val < bound then
    ⟨bound - 1 - a.val, hc⟩
  else
    a  -- Fallback

/-- Convert between any two bounds. Proof-carrying when the value fits
(widening or in-range narrowing); opaque junk when it does not (real Move `as`
aborts there — see `convert_overflows`). The positivity of the target bound is
an auto-param: generated call sites always target a literal `2^k`, so `decide`
discharges it silently; abstract-bound users supply it explicitly. -/
def convert {bound_from bound_to : Nat} (a : BoundedNat bound_from)
    (hb : 0 < bound_to := by first | decide | omega) : BoundedNat bound_to :=
  if h : a.val < bound_to then
    ⟨a.val, h⟩
  else
    convertJunk a hb

/-- True iff `convert a : BoundedNat bound_to` would truncate — i.e. a real
Move `as` cast to a type with bound `bound_to` would abort. Reducible.
`bound_to` is explicit (it does not occur in the result type). -/
@[reducible] def convert_overflows (bound_to : Nat) {bound_from : Nat}
    (a : BoundedNat bound_from) : Bool :=
  decide (a.val ≥ bound_to)

/-- Convert to larger bound -/
def widen {bound bound' : Nat} (a : BoundedNat bound) (h : bound ≤ bound') : BoundedNat bound' :=
  convert a (Nat.lt_of_lt_of_le (bound_pos a) h)

/-- Truncate to smaller bound (junk when the value does not fit) -/
def truncate {bound bound' : Nat} (a : BoundedNat bound)
    (hb : 0 < bound' := by first | decide | omega) : BoundedNat bound' :=
  convert a hb

/-- Positivity of a bound, as a typeclass so the `OfNat` instance below can
demand it (auto-params do not fire during instance search). The generic
power-of-2 instance covers every bound Move uses. -/
class BoundPos (bound : Nat) : Prop where
  pos : 0 < bound

instance {n : Nat} : BoundPos (2^n) := ⟨Nat.two_pow_pos n⟩

-- Instance for numeric literals. In-bounds literals (the only ones the
-- generator emits) construct the exact value; out-of-bounds literals produce
-- opaque junk (no wrapping equation is provable about them).
instance {bound : Nat} (n : Nat) [BoundPos bound] [Decidable (n < bound)] :
    OfNat (BoundedNat bound) n :=
  ⟨if h : n < bound then ⟨n, h⟩ else ofNatJunk n BoundPos.pos⟩

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
    -- Move uses truncating shift left: (a <<< k) % bound
    ⟨(a.val <<< k) % bound, Nat.mod_lt _ (bound_pos a)⟩

instance : HShiftRight (BoundedNat bound) Nat (BoundedNat bound) where
  hShiftRight := shiftRight

-- Also provide instances for BoundedNat shift amounts
instance {bound' : Nat} : HShiftLeft (BoundedNat bound) (BoundedNat bound') (BoundedNat bound) where
  hShiftLeft a k :=
    -- Move uses truncating shift left: (a <<< k) % bound
    ⟨(a.val <<< k.val) % bound, Nat.mod_lt _ (bound_pos a)⟩

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
    if hc : bound - 1 - a.val < bound then
      ⟨bound - 1 - a.val, hc⟩
    else
      a  -- Fallback (unreachable: bound > 0 by inhabitant `a`)

/-! ## Value Extraction Lemmas

These lemmas allow extracting the underlying Nat value from BoundedNat operations.
They are essential for proving that implementations match specifications.
All arithmetic value lemmas are CONDITIONAL on non-overflow/non-underflow —
nothing is provable about the junk face.
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

/-- Addition extracts to Nat addition when it does not overflow. -/
@[simp] theorem add_val (a b : BoundedNat bound) (h : a.val + b.val < bound) :
    (a + b).val = a.val + b.val := by
  show (BoundedNat.add a b).val = _
  simp only [BoundedNat.add, h, ↓reduceDIte]

/-- Alias of `add_val` kept for proof-surface compatibility. -/
theorem add_val_of_no_overflow (a b : BoundedNat bound)
    (h : a.val + b.val < bound) : (a + b).val = a.val + b.val := add_val a b h

/-- Unconditionally true upper bound: exact on the happy path; on overflow the
junk value is `< bound ≤ a.val + b.val`. (The honest replacement for the
former wrapping `Nat.mod_le` argument.) -/
theorem add_val_le (a b : BoundedNat bound) : (a + b).val ≤ a.val + b.val := by
  by_cases h : a.val + b.val < bound
  · exact Nat.le_of_eq (add_val a b h)
  · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (a + b).property (by omega))

/-- Subtraction extracts to Nat subtraction when it does not underflow. -/
@[simp] theorem sub_val (a b : BoundedNat bound) (h : b.val ≤ a.val) :
    (a - b).val = a.val - b.val := by
  show (BoundedNat.sub a b).val = _
  simp only [BoundedNat.sub, h, ↓reduceDIte]

/-- Alias of `sub_val` kept for symmetry with the add/mul forms. -/
theorem sub_val_of_no_underflow (a b : BoundedNat bound)
    (h : b.val ≤ a.val) : (a - b).val = a.val - b.val := sub_val a b h

/-- Width-specialized conditional `add_val`/`val` lemmas, used by
loop-termination/`decreasing_by` macros (side conditions discharged by the
macros' `omega` discharger). -/
@[simp] theorem val_one_u64 : (1 : BoundedNat (2^64)).val = 1 := by decide
@[simp] theorem add_val_u64 (a b : BoundedNat (2^64)) (h : a.val + b.val < 2^64) :
    (a + b).val = a.val + b.val := add_val a b h
@[simp] theorem add_val_u32 (a b : BoundedNat (2^32)) (h : a.val + b.val < 2^32) :
    (a + b).val = a.val + b.val := add_val a b h
@[simp] theorem add_val_u8 (a b : BoundedNat (2^8)) (h : a.val + b.val < 2^8) :
    (a + b).val = a.val + b.val := add_val a b h

/-- Multiplication extracts to Nat multiplication when it does not overflow. -/
@[simp] theorem mul_val (a b : BoundedNat bound) (h : a.val * b.val < bound) :
    (a * b).val = a.val * b.val := by
  show (BoundedNat.mul a b).val = _
  simp only [BoundedNat.mul, h, ↓reduceDIte]

/-- Alias of `mul_val` kept for proof-surface compatibility. -/
theorem mul_val_of_no_overflow (a b : BoundedNat bound)
    (h : a.val * b.val < bound) : (a * b).val = a.val * b.val := mul_val a b h

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

/-- Convert when value fits in target bound. Generic over the positivity
witness `hb` so it matches whatever proof term the call site elaborated. -/
theorem convert_val_of_lt {bound_from bound_to : Nat} (a : BoundedNat bound_from)
    {hb : 0 < bound_to} (h : a.val < bound_to) :
    (convert a hb : BoundedNat bound_to).val = a.val := by
  simp only [convert, h, ↓reduceDIte]

/-- Convert is identity when value already fits -/
theorem convert_val_eq_of_lt {bound_from bound_to : Nat} (a : BoundedNat bound_from)
    {hb : 0 < bound_to} (h : a.val < bound_to) :
    (convert a hb : BoundedNat bound_to).val = a.val :=
  convert_val_of_lt a h

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
