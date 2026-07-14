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
-- representing heterogeneous values via per-project closed
-- inductives (declared in `Generated/`, emitted by the renderer).
-- Two universes are emitted per project (the DfU/BagU split from the
-- unified-backend design, §3.2):
--
--   * `TyCode` (the "DfU" universe) — every heterogeneous-storage
--     type, INCLUDING structs that (transitively) contain a `Bag`.
--   * `BagU` (the bag universe) — the types that flow into
--     `bag::*` / `object_bag::*` operations, excluding bag-containing
--     structs (a Bag cannot be a member of its own universe without a
--     file-level import cycle). `Bag` is parameterized by `BagU`.
--
-- Key abstractions:
--
--   * `Universe U` — typeclass witness that `U` is a finite type
--     universe with decidable equality of codes, a type-interpretation
--     function, and DECIDABLE equality at every interpreted type
--     (`decEqInterp`). Deciding equality (rather than packing a bare
--     `BEq`) makes `BEq`/`LawfulBEq` at `Entry U`, `KeyEntry U` /
--     `ValEntry U` (Prelude/World.lean) and `DfKey` synthesizable —
--     retiring the hand-written `BEq (Entry U)` and the client-side
--     `UniverseReflBEq` shims.
--   * `HasCode U T` — typeclass instance saying "Lean type `T` is in
--     universe `U`", with the witnessing `code : U` and a `proof`
--     that `Universe.interp code = T`. Every per-project instance is
--     `proof := rfl` — *no axioms anywhere*.
--
-- `Entry U` is the heterogeneous key-value pair used by bag storage.
-- It lives here (not in `natives/Sui/BagNatives.lean`) so the World
-- prelude can reference it without importing the natives tree.

import Prelude.BoundedNat

class Universe (U : Type) where
  decEq     : DecidableEq U
  interp    : U → Type
  -- Decidable equality at `Universe.interp u` for any code `u`.
  -- Required by the `DecidableEq (Entry U)` instance below (which has
  -- to compare transported values after dispatching on `decEq`) and
  -- by the typed-view key machinery in `Prelude/World.lean`.
  decEqInterp : ∀ u, DecidableEq (interp u)
  -- `typeName` gives each code's Move fully-qualified type name
  -- (`<64hex-addr>::<module>::<Type>`, with `<...>` type-args for
  -- generic wrappings). `std::type_name::get<T>` returns these bytes,
  -- so byte-comparing two `type_name`s (coin canonical ordering in
  -- `create_pool`) matches Move's order. Emitted per-constructor by
  -- the renderer in `Generated/TyCodeInterp.lean` /
  -- `Generated/BagUInterp.lean`.
  typeName  : U → String
  -- `serialize` gives each value its BCS bytes at its type code.
  -- Used by `move_stdlib::bcs::to_bytes<X>` when `X` is GENERIC (e.g.
  -- `comparator::compare<X>` -> `compare_u8_vector(bcs(v1), bcs(v2))`),
  -- where the concrete type isn't known at the call site so the
  -- renderer can't route to a per-type serializer. Default is `[]`
  -- (the pre-typeclass stub) so any universe that doesn't need value
  -- serialization is unaffected; the per-project instance overrides it.
  serialize : (u : U) → interp u → List (BoundedNat (2^8)) := fun _ _ => []
  -- `uidNat` gives a value its object-UID as a `Nat` key, for `key` types
  -- (whose field 0 is a `sui::object::UID`). Used by world-mode to key a
  -- GENERIC object into the `World` object store (`transfer::*` /
  -- `test_scenario::return_*` over a bare type param `T: key`), where the
  -- concrete type isn't known so the transfer lowering can't project field 0
  -- structurally. Emitted per-constructor by the renderer
  -- (`Generated/*Interp.lean`): `.dummy` and non-`key` codes get `0`; a `key`
  -- struct gets `fun o => o.<uid-field>.id.bytes.bytes.val`. The `Object.UID`
  -- type lives in the Sui natives tree (which imports this Prelude), so this
  -- method can only speak in terms of the underlying `Nat`; the generated
  -- World-view wraps it back into an `Object.UID`. Default `0` keeps universes
  -- that never carry `key` objects unaffected.
  uidNat : (u : U) → interp u → Nat := fun _ _ => 0

attribute [reducible] Universe.decEq
attribute [reducible] Universe.decEqInterp
attribute [instance]  Universe.decEq
attribute [instance]  Universe.decEqInterp

class HasCode (U : Type) [Universe U] (T : Type) where
  code  : U
  proof : Universe.interp code = T

/-- The universe code of a `HasCode` member type. -/
abbrev Universe.codeOf (U : Type) [Universe U] (T : Type) [h : HasCode U T] : U :=
  h.code

/-- Object-UID-as-`Nat` of a member value, dispatching through its code's
`uidNat`. World-mode's generic `key`-object keying (`transfer::*` /
`test_scenario::return_*` over `T: key`) uses this: it can't project the UID
field of an abstract `T` structurally, so it routes through the per-constructor
`Universe.uidNat`. The `cast` transports `obj : T` to `interp code` along the
`HasCode.proof` (which is `rfl` in every generated instance). -/
def Universe.uidNatOf (U : Type) [Universe U] (T : Type) [h : HasCode U T]
    (obj : T) : Nat :=
  Universe.uidNat h.code (cast h.proof.symm obj)

/-- Transport collapse: casting along an equation and back is the identity.
The only place double-`▸` transport is ever reasoned about; everything
downstream uses the typed-view lemmas. -/
theorem cast_symm_cancel {α β : Type} (h : α = β) (x : β) : h ▸ h.symm ▸ x = x := by
  cases h; rfl

theorem cast_inj {α β : Type} (h : α = β) {x y : β}
    (hx : h.symm ▸ x = h.symm ▸ y) : x = y := by
  cases h; exact hx

/-- One heterogeneous key/value pair (bag storage). -/
structure Entry (U : Type) [Universe U] where
  kc : U
  k  : Universe.interp kc
  vc : U
  v  : Universe.interp vc

instance {U : Type} [Universe U] : DecidableEq (Entry U) := fun e1 e2 => by
  cases e1 with | mk kc1 k1 vc1 v1 =>
  cases e2 with | mk kc2 k2 vc2 v2 =>
  cases Universe.decEq kc1 kc2 with
  | isFalse h => exact isFalse (fun he => by cases he; exact h rfl)
  | isTrue h =>
    subst h
    cases Universe.decEqInterp kc1 k1 k2 with
    | isFalse hk => exact isFalse (fun he => by cases he; exact hk rfl)
    | isTrue hk =>
      subst hk
      cases Universe.decEq vc1 vc2 with
      | isFalse hv => exact isFalse (fun he => by cases he; exact hv rfl)
      | isTrue hv =>
        subst hv
        cases Universe.decEqInterp vc1 v1 v2 with
        | isFalse hvv => exact isFalse (fun he => by cases he; exact hvv rfl)
        | isTrue hvv => subst hvv; exact isTrue rfl
