import Prelude.BoundedNat

-- ============================================================================
-- Homogeneous bitwise operator instances for all UInt types
-- Following Move semantics: bitwise operations require same-type operands
-- ============================================================================

instance : AndOp UInt8 := ⟨fun a b => UInt8.land a b⟩
instance : OrOp UInt8 := ⟨fun a b => UInt8.lor a b⟩
instance : XorOp UInt8 := ⟨fun a b => UInt8.xor a b⟩
instance : HShiftLeft UInt8 UInt8 UInt8 := ⟨fun a b => UInt8.shiftLeft a b⟩
instance : HShiftRight UInt8 UInt8 UInt8 := ⟨fun a b => UInt8.shiftRight a b⟩

instance : AndOp UInt16 := ⟨fun a b => UInt16.land a b⟩
instance : OrOp UInt16 := ⟨fun a b => UInt16.lor a b⟩
instance : XorOp UInt16 := ⟨fun a b => UInt16.xor a b⟩
instance : HShiftLeft UInt16 UInt8 UInt16 := ⟨fun a b => UInt16.shiftLeft a b.toUInt16⟩
instance : HShiftRight UInt16 UInt8 UInt16 := ⟨fun a b => UInt16.shiftRight a b.toUInt16⟩

instance : AndOp UInt32 := ⟨fun a b => UInt32.land a b⟩
instance : OrOp UInt32 := ⟨fun a b => UInt32.lor a b⟩
instance : XorOp UInt32 := ⟨fun a b => UInt32.xor a b⟩
instance : HShiftLeft UInt32 UInt8 UInt32 := ⟨fun a b => UInt32.shiftLeft a b.toUInt32⟩
instance : HShiftRight UInt32 UInt8 UInt32 := ⟨fun a b => UInt32.shiftRight a b.toUInt32⟩

instance : AndOp UInt64 := ⟨fun a b => UInt64.land a b⟩
instance : OrOp UInt64 := ⟨fun a b => UInt64.lor a b⟩
instance : XorOp UInt64 := ⟨fun a b => UInt64.xor a b⟩
instance : HShiftLeft UInt64 UInt8 UInt64 := ⟨fun a b => UInt64.shiftLeft a b.toUInt64⟩
instance : HShiftRight UInt64 UInt8 UInt64 := ⟨fun a b => UInt64.shiftRight a b.toUInt64⟩

-- Vec type (used for Move vector)
def Vec (α : Type) : Type := List α

-- BEq instance for Vec (required for is_equal_vec)
instance [BEq α] : BEq (Vec α) := inferInstanceAs (BEq (List α))

-- Address type (used for Move address)
structure Address where
    bytes : BoundedNat (2^256)
    deriving BEq, Repr, DecidableEq
instance : Inhabited Address where default := ⟨default⟩
instance : LawfulBEq Address where
  rfl := by intro a; cases a; rename_i b; exact (beq_self_eq_true b : (b == b) = true)
  eq_of_beq := by
    intro a b h; cases a; cases b; rename_i x y
    have : x = y := eq_of_beq (h : (x == y) = true)
    simp [this]
instance (n : Nat) [Decidable (n < 2^256)] : OfNat Address n where ofNat := ⟨OfNat.ofNat n⟩

-- Coercion from Bool to Prop: allows Bool struct field values to be used
-- in Prop contexts automatically (if conditions, logical operators, etc.)
instance : Coe Bool Prop where
  coe b := b = true







/-! Structural recomposition combinators for generated `.ensures` obligation
bundles and equation lemmas (unified-backend design §5.1/§5.3, Phase 3): the
generator emits `<fn>.ensures*_of` theorems and `<fn>.eq_then`/`eq_else`
branch equations whose proofs are direct terms built from these — no tactics
in the generated proof, checked linearly. -/

namespace SpecEnsures

/-- Bool-conjunction postcondition split: both conjuncts hold. -/
theorem and_of {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  simp [ha, hb]

/-- Prop-branched `if (c : Bool) then P else Q`: both arms discharged under
their guard fact. -/
theorem ite_of {c : Bool} {P Q : Prop} (ht : c = true → P) (he : c = false → Q) :
    if c then P else Q := by
  cases c
  · simpa using he rfl
  · simpa using ht rfl

universe u

/-- Terminal-`if` equation lemma (then branch), used by the generated
`<fn>.eq_then` lemmas under the `irreducible_defs` gate. -/
theorem ite_then {c : Bool} {α : Sort u} {t e : α} (h : c = true) :
    (if c then t else e) = t := by
  simp [h]

/-- Terminal-`if` equation lemma (else branch: `<fn>.eq_else`). -/
theorem ite_else {c : Bool} {α : Sort u} {t e : α} (h : c = false) :
    (if c then t else e) = e := by
  simp [h]

end SpecEnsures

/-- Bool-valued ite under `= true` (ensures faces let-bind their conditionals
as Bool before the Prop lift): both arms discharged under their guard fact. -/
theorem SpecEnsures.bite_eq_true_of {c a b : Bool}
    (ht : c = true → a = true) (he : c = false → b = true) :
    (if c then a else b) = true := by
  cases c
  · simpa using he rfl
  · simpa using ht rfl
