-- Closed-universe type representation for heterogeneous typed storage.
--
-- Background: Sui's `bag::*` / `object_bag::*` / `dynamic_field::*` /
-- `dynamic_object_field::*` storage is heterogeneous — one `Bag` can
-- hold entries of arbitrary `(K, V)` pairs. Modeling such storage by
-- baking per-(K, V) ghost fields into the framework's `Bag.Bag`
-- struct breaks the import graph: the ghost fields would reference
-- user types, but `Sui.Bag` lives in a framework file that cannot
-- import a user package without forming a cycle.
--
-- This file provides the project-independent infrastructure for
-- representing heterogeneous values via a per-project closed
-- inductive `TyCode` (declared in `<project>/TyCode.lean`, emitted by
-- the renderer). The two key abstractions:
--
--   * `Universe U` — typeclass witness that `U` is a finite type
--     universe with decidable equality, type-interpretation function,
--     and equality instances for every interpreted type.
--   * `HasCode U T` — typeclass instance saying "Lean type `T` is in
--     universe `U`", with the witnessing `code : U` and a `proof`
--     that `Universe.interp code = T`. Every per-project instance is
--     `proof := rfl` — *no axioms anywhere*.
--
-- `Entry U` is the heterogeneous key-value pair: a key type-code
-- plus the key value (at the interpreted type), and similarly for
-- the value. `DecidableEq (Entry U)` is hand-written because Lean's
-- deriving machinery can't synthesize across the dependent types.
--
-- `Dyn U` + `Dyn.getT?` are the type-safe wrappers user code rarely
-- touches directly; `Bag.borrow` / `Bag.add` etc. (defined in
-- `lemmas/natives/Sui/BagNatives.lean`) project through the
-- universe via `HasCode` dispatch.
--
-- See `plans/lean-pipeline/dynamic-typing-via-repr-design.md` for
-- full design.

import Prelude.BoundedNat

/-- Little-endian fixed-width BCS bytes of an unsigned integer: BCS
serializes `uN` as `N/8` LE bytes. Used by the generated
`<Universe>.serialize` arms for primitive codes. -/
def bcsUIntLe (width : Nat) (v : Nat) : List (BoundedNat (2^8)) :=
  (List.range width).map fun i =>
    ⟨(v >>> (8 * i)) % (2^8), Nat.mod_lt _ (by decide)⟩

/-- Big-endian fixed-width bytes: a Move `address` serializes as its 32
canonical bytes, i.e. the big-endian digits of the 256-bit value. -/
def bcsUIntBe (width : Nat) (v : Nat) : List (BoundedNat (2^8)) :=
  ((List.range width).reverse).map fun i =>
    ⟨(v >>> (8 * i)) % (2^8), Nat.mod_lt _ (by decide)⟩

/-- Unsigned LEB128 (ULEB128): BCS encodes every length prefix (vectors,
strings) and every enum variant index this way. Little-endian, 7 payload
bits per byte, high bit set on all but the final byte. Total (well-founded
on `n`, no `partial def`): each step recurses on `n / 128 < n`. Used by the
generated `<Universe>.serialize` arms for vector / string / option / struct
fields. -/
def bcsUleb128 (n : Nat) : List (BoundedNat (2^8)) :=
  if h : n < 128 then
    [⟨n % (2^8), Nat.mod_lt _ (by decide)⟩]
  else
    ⟨(n % 128 + 128) % (2^8), Nat.mod_lt _ (by decide)⟩ :: bcsUleb128 (n / 128)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

class Universe (U : Type) where
  decEq     : DecidableEq U
  interp    : U → Type
  -- `decEqInterp` lets generated wrapper types derive `DecidableEq`
  -- recursively through the closed universe. The corresponding `BEq`
  -- and `LawfulBEq` instances are then synthesized by Lean from
  -- `DecidableEq`.
  decEqInterp : ∀ u, DecidableEq (interp u)
  -- `typeName` gives each code's Move fully-qualified type name
  -- (`<64hex-addr>::<module>::<Type>`, with `<...>` type-args for
  -- generic wrappings). `std::type_name::get<T>` returns these bytes,
  -- so byte-comparing two `type_name`s (coin canonical ordering in
  -- `create_pool`) matches Move's order. Emitted per-constructor by
  -- the renderer in `Generated/TyCodeInterp.lean` /
  -- `Generated/ObjTypeInterp.lean`.
  typeName  : U → String
  -- `serialize` gives each value its BCS bytes at its type code.
  -- Used by `move_stdlib::bcs::to_bytes<X>` when `X` is GENERIC (e.g.
  -- `comparator::compare<X>` -> `compare_u8_vector(bcs(v1), bcs(v2))`),
  -- where the concrete type isn't known at the call site so the
  -- renderer can't route to a per-type serializer. Default is `[]`
  -- (the pre-typeclass stub) so ObjType and any universe that doesn't
  -- need value serialization is unaffected; the per-project TyCode
  -- instance overrides it (`Generated/TyCodeInterp.lean`).
  serialize : (u : U) → interp u → List (BoundedNat (2^8)) := fun _ _ => []

attribute [reducible] Universe.decEq
attribute [reducible] Universe.decEqInterp
attribute [instance]  Universe.decEq
attribute [instance]  Universe.decEqInterp

class HasCode (U : Type) [Universe U] (T : Type) where
  code  : U
  proof : Universe.interp code = T

-- Note: `Entry U` lives in `lemmas/natives/Sui/BagNatives.lean` (not
-- here) so it can use a packed `univ : Universe U` field instead of
-- a class constraint. This avoids the import cycle that would arise
-- if `Bag (U : Type) [Universe U]` were used as a field type inside
-- user `_Types.lean` files (which don't import `TyCodeInterp`).
