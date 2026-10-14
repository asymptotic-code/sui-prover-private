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
    deriving DecidableEq, Repr
instance : Inhabited Address where default := ⟨default⟩
instance (n : Nat) [Decidable (n < 2^256)] : OfNat Address n where ofNat := ⟨OfNat.ofNat n⟩

namespace Address
/-- `Address.ofNat n`: explicit-name constructor used by the new-pipeline
renderer for address-literal constants (`@0x42` -> `Address.ofNat 66`).
The instance-method spelling (`@OfNat.ofNat Address n _`) works too, but
the renderer emits the bare dot form so an explicit def is required for
name resolution. -/
def ofNat (n : Nat) [Decidable (n < 2^256)] : Address :=
  Address.mk (OfNat.ofNat n)

/-- Big-endian 32-byte address serialisation -- the ONE encoder behind every
Move native that BCS-serialises an address: `address::to_bytes`
(`Sui/AddressNatives.lean`) and `object::{id_to_bytes, uid_to_bytes}`
(`Sui/ObjectNatives.lean`). All three Move bodies are `bcs::to_bytes` of the
same `address`, so they must be the same list.

It lives HERE, next to the `Address` structure, rather than in
`AddressNatives`, for one structural reason: `ObjectNatives` already imports
`Prelude.Helpers`, so routing the encoder through this module costs nothing,
whereas `import Sui.AddressNatives` from `ObjectNatives` would drag ~20
further modules (`MoveStdlib.Ascii`, `MoveStdlib.MoveString`, their natives,
`Generated.ObjType`, ...) into the transitive closure of EVERY file that
imports `ObjectNatives` -- which is nearly every native model and every
generated module. Those modules' `@[simp]` lemmas would then join the simp
set of all of them. That import does type-check and introduces no cycle
(nothing reachable from `AddressNatives` imports `ObjectNatives`), and the
one corpus it was tried on stayed green -- but it is a fleet-wide simp-set
change bought for a one-line convenience, and this route buys the same
sharing for nothing.

Nothing here is `@[simp]`, deliberately: `Prelude.Helpers` is imported by
every generated file in every client, so a simp lemma added here is a
fleet-wide rewrite. -/
private def toBytesBEAux : Nat -> Nat -> List (BoundedNat (2^8)) -> List (BoundedNat (2^8))
  | 0, _, acc => acc
  | Nat.succ k, x, acc =>
    let byte_val := x % 256
    let byte : BoundedNat (2^8) := ⟨byte_val, Nat.mod_lt _ (by decide)⟩
    toBytesBEAux k (x / 256) (byte :: acc)

def toBytesBE (a : Address) : List (BoundedNat (2^8)) :=
  toBytesBEAux 32 a.bytes.val []

private theorem length_toBytesBEAux (k : Nat) :
    ∀ (n : Nat) (acc : List (BoundedNat (2^8))),
      (toBytesBEAux k n acc).length = k + acc.length := by
  induction k with
  | zero => intro n acc; simp [toBytesBEAux]
  | succ k ih =>
    intro n acc
    simp only [toBytesBEAux, ih, List.length_cons]
    omega

/-- An address serialises to EXACTLY 32 bytes. This is the fact the `object`
byte natives' length pins delegate to, and the one a spec comparing an
`id_to_bytes` result against an `address::to_bytes` result needs. -/
theorem length_toBytesBE (a : Address) : (toBytesBE a).length = 32 := by
  show (toBytesBEAux 32 a.bytes.val []).length = 32
  have h := length_toBytesBEAux 32 a.bytes.val []
  simpa using h
end Address

-- Coercion from Bool to Prop: allows Bool struct field values to be used
-- in Prop contexts automatically (if conditions, logical operators, etc.)
instance : Coe Bool Prop where
  coe b := b = true

-- ============================================================================
-- Funds-accumulator value reconstruction
-- ============================================================================
-- `funds_accumulator::redeem<T>` returns the funds previously withdrawn into a
-- `Withdrawal<T>`. The withdrawal already carries the exact amount in its
-- `limit` field (`withdraw_from_object` packs `Withdrawal { owner, limit }`), so
-- redeem can reconstruct a value-carrying `T` -- in practice `balance::Balance<C>`
-- -- without modelling an accumulator ledger. The `redeem` native does this
-- through `FromAccumValue.ofValue`.
--
-- The universal fallback (low priority) keeps EVERY redeem call site compiling
-- regardless of `T`, falling back to the value-blind default. A per-type
-- instance the struct renderer emits for `balance::Balance` (default priority)
-- wins at concrete-`Balance` call sites and carries the real value, fixing the
-- `assert!(value > 0)` over-aborts on redeemed balances.
class FromAccumValue (T : Type) where
  ofValue : BoundedNat (2^256) → T

instance (priority := 100) {T : Type} [Inhabited T] : FromAccumValue T where
  ofValue _ := default

-- Dual of `FromAccumValue` for the deposit direction. `add_impl<T>` and
-- `add_to_accumulator_address<T>` push a `T` (in practice
-- `balance::Balance<C>`) into the accumulator; `toValue` projects the
-- deposited amount so the World ledger can track a running balance per
-- accumulator key. The universal fallback (low priority) keeps EVERY
-- deposit call site compiling regardless of `T`, contributing a
-- value-blind 0. The struct renderer emits a per-type instance for
-- `balance::Balance` (default priority) that reads the real `value`
-- field, so genuine balance deposits are tracked faithfully.
class ToAccumValue (T : Type) where
  toValue : T → BoundedNat (2^256)

instance (priority := 100) {T : Type} : ToAccumValue T where
  toValue _ := (0 : BoundedNat (2^256))

theorem prop_eq_true_eq_true_of (p : Prop) (hp : p) :
    p = (true = true) :=
  propext (Iff.intro (fun _ => by trivial) (fun _ => hp))

theorem beq_true_symm {α : Type} [BEq α] [LawfulBEq α] {a b : α}
    (h : (a == b) = true) : (b == a) = true := by
  rw [LawfulBEq.eq_of_beq h]
  simp

theorem address_beq_comm (a b : Address) : (a == b) = (b == a) := by
  by_cases h : a = b
  · subst b
    simp [BEq.beq]
  · have h' : b ≠ a := by
      intro hb
      exact h hb.symm
    simp [BEq.beq, h, h']

theorem address_bne_comm (a b : Address) : (a != b) = (b != a) := by
  unfold bne
  rw [address_beq_comm a b]

theorem address_beq_self (a : Address) : (a == a) = true := by
  simp [BEq.beq]

/-! ## Shared `List` frame lemmas

Container natives model their backing as a `List` and their mutators as
`List.filter`/`List.map` rewrites, so "the read at another key is unchanged"
obligations bottom out in the four facts below. Every corpus had grown its own
copies (bluefin alone under 10 distinct names); they live here so a client
proof cites them instead. Namespaced per the standing rule in
`plans/lean-pipeline/shared-proof-infra.md`: a root-namespace helper here is a
latent compile break for every overlay that picks the same obvious name. -/

namespace ListFacts

/-- Dropping elements the predicate rejects anyway leaves `any` unchanged. -/
theorem any_filter_not_of_disjoint {α : Type} (remove keep : α → Bool)
    (xs : List α) (h_disjoint : ∀ x, remove x = true → keep x = false) :
    (xs.filter (fun x => !remove x)).any keep = xs.any keep := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h_remove : remove x
      · simp [h_remove, ih]
      · have h_keep := h_disjoint x h_remove
        simp [h_remove, h_keep, ih]

/-- `findSome?` frame lemma in the `filter (!remove)` shape emitted by the
`Table`/`Dynamic_field` upsert models. -/
theorem findSome?_filter_not_of_removed_none {α β : Type}
    (remove : α → Bool) (find : α → Option β) (xs : List α)
    (h_none : ∀ x, remove x = true → find x = none) :
    List.findSome? find (xs.filter (fun x => !remove x)) =
      List.findSome? find xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h_remove : remove x
      · cases h_find : find x <;> simp [List.findSome?, h_remove, h_find, ih]
      · have h_find := h_none x h_remove
        simp [List.findSome?, h_remove, h_find, ih]

/-- Same frame lemma in the positive `filter keep` shape. -/
theorem findSome?_filter_of_dropped_none {α β : Type} (xs : List α)
    (keep : α → Bool) (read : α → Option β)
    (h_irrelevant : ∀ x, keep x = false → read x = none) :
    (xs.filter keep).findSome? read = xs.findSome? read := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases h_keep : keep x = true
      · cases h_read : read x <;>
          simp [List.filter, h_keep, h_read, ih]
      · have h_keep_false : keep x = false := Bool.eq_false_iff.mpr h_keep
        have h_read : read x = none := h_irrelevant x h_keep_false
        simp [List.filter, h_keep_false, h_read, ih]

/-- `MoveVector.borrow` on a mapped vector, in range. -/
theorem getD_map_of_lt {A B : Type} [Inhabited A] [Inhabited B]
    (f : A → B) (xs : List A) (i : Nat) (h : i < xs.length) :
    (xs.map f).getD i default = f (xs.getD i default) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h]
  simp [List.getD, h]

/-- Filtering out a predicate that matches at least one element strictly
shrinks the list. The strict-decrease core of every container's
"remove at a contained key" length lemma (`Table`/`ObjectTable`/`Bag`/
`ObjectBag`/`VecMap`/`VecSet` each carried a private copy; consolidated
here by the lemma-wave landing). -/
theorem length_filter_lt_of_any {A : Type} (l : List A) (p : A → Bool)
    (h_any : l.any p = true) :
    (l.filter (fun x => !p x)).length < l.length := by
  induction l with
  | nil => simp at h_any
  | cons x rest ih =>
      rw [List.any_cons] at h_any
      cases hx : p x with
      | true =>
          have h_le := List.length_filter_le (fun x => !p x) rest
          have h_eq : List.filter (fun x => !p x) (x :: rest) =
              List.filter (fun x => !p x) rest := by
            simp [hx]
          rw [h_eq, List.length_cons]
          omega
      | false =>
          rw [hx, Bool.false_or] at h_any
          have h_lt := ih h_any
          have h_eq : List.filter (fun x => !p x) (x :: rest) =
              x :: List.filter (fun x => !p x) rest := by
            simp [hx]
          rw [h_eq, List.length_cons, List.length_cons]
          omega

end ListFacts



