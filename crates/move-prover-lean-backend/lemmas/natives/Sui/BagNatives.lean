-- Native implementations for sui::bag.
--
-- Move source: `public struct Bag has key, store { id: UID,
-- size: u64 }`. Heterogeneous storage -- one Bag holds entries of
-- arbitrary `(K, V)` pairs.
--
-- ## Toy-faithful design (entries IN the bag struct, no axioms)
--
-- `Bag (U : Type) [Universe U]` with `storage : List (Entry U)`.
-- `Entry U` has `k : Universe.interp kc` and `v : Universe.interp vc`
-- (dependent on the per-entry codes). Every `bag::add k v |>.borrow k`
-- law is provable by `rfl` given the renderer-emitted HasCode
-- instances (`HasCode TyCode T := ⟨ctor, rfl⟩`).
--
-- The historical `Vault_Types -> TyCodeInterp -> Vault_Types` file
-- cycle that blocked this design is broken by splitting user
-- `_Types.lean` into:
--   * `<Mod>_Types_Skeleton.lean` -- Bag-FREE structs only,
--     imported by `Generated/TyCodeInterp.lean`.
--   * `<Mod>_Types.lean` -- Bag-CONTAINING structs, imports
--     `TyCodeInterp` for the `[Universe TyCode]` instance.
-- The renderer emits both files automatically for modules that
-- contain any Bag-containing struct.
--
-- Bag itself is also filtered out of TyCode -- including it would
-- force `TyCodeInterp.lean` to reference `Bag.Bag TyCode` in its
-- interp body before the Universe instance is declared (forward
-- ref). Move programs that store Bag values via dyn_field need a
-- separate renderer path; the modeling-via-TyCode path doesn't
-- support them.
--
-- See `plans/lean-pipeline/dynamic-typing-via-repr-design.md` and
-- `plans/lean-pipeline/dynamic-typing-toy.lean`.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.Universe
import Prelude.MoveAbort
import Sui.ObjectNatives

namespace Bag

-- `Entry U` (the heterogeneous key/value pair) lives in
-- `Prelude/Universe.lean`, with a `DecidableEq` instance (so `BEq` and
-- `LawfulBEq` synthesize — the hand-written `BEq (Entry U)` is retired).

/-- `Bag (U : Type) [Universe U]` -- typed storage IN the struct. The
constructor is named `ofParts`; `Bag.mk` below is a 2-argument smart
constructor matching the Move struct's two fields. -/
structure Bag (U : Type) [Universe U] where
  ofParts ::
  id      : Object.UID
  size    : BoundedNat (2^64)
  storage : List (Entry U)
deriving Inhabited, BEq

/-- Move's `Bag` has two fields (`id`, `size`); the closed-universe model adds
`storage`, which a freshly-constructed bag starts empty. `bag::new` translates
to `Bag.mk <id> <size>` (the renderer only knows the two Move fields), so this
2-argument `Bag.mk` defaults `storage := []`. The fresh `id` and the `TxContext`
threading are produced by the generated `bag::new` body via `object::new`; only
the empty initial storage is supplied here. -/
@[reducible]
def Bag.mk {U : Type} [Universe U]
    (id : Object.UID) (size : BoundedNat (2^64)) : Bag U :=
  Bag.ofParts id size []

-- `bag::new` is generated from Move source (it threads the `TxContext` through
-- `object::new` to mint the fresh `id`, then builds the bag via the two-argument
-- `Bag.mk` above). Its abort companion, however, would otherwise re-emit the bag
-- construction as a dead `let` whose `[Universe U]` is unconstrained (the value
-- is discarded), leaving a stuck instance. `bag::new` cannot abort —
-- `object::new` reduces to `tx_context::fresh_object_address`, which never
-- aborts — so we shadow `new.aborts` with the constant `none`. `Ctx` is generic
-- to avoid naming the generated `Tx_context.TxContext` type here.
def new.aborts {Ctx : Type} (_ctx : Ctx) : Option MoveAbort :=
  Option.none

def Entry.keyMatches {U : Type} [Universe U] {K : Type}
    [hkc : HasCode U K] [BEq K] (e : Entry U) (k : K) : Bool :=
  if h : e.kc = hkc.code then
    let lifted : K := hkc.proof ▸ h ▸ e.k
    lifted == k
  else
    false

def add {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [BEq K]
    (self : Bag U) (k : K) (v : V) : Bag U :=
  let entry : Entry U :=
    { kc := hkc.code, k  := hkc.proof.symm ▸ k
    , vc := hvc.code, v  := hvc.proof.symm ▸ v }
  let filtered := self.storage.filter (fun e => ! Entry.keyMatches e k)
  { self with size := self.size + 1, storage := entry :: filtered }

def add.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K]
    (_self : Bag U) (_k : K) (_v : V) : Bool := false

/-- `Bag.set` — overwrites the value at key `k`, preserving size when
the key already exists (semantically the writeback companion of
`borrow_mut`). If the key is absent, behaves like `add` (size + 1).
The renderer emits `Bag.set` at writeback sites for
`let sa = bag::borrow_mut(bag, k); <mutate sa>` patterns so the
mutation propagates back into the bag's storage. -/
def set {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [BEq K]
    (self : Bag U) (k : K) (v : V) : Bag U :=
  let entry : Entry U :=
    { kc := hkc.code, k  := hkc.proof.symm ▸ k
    , vc := hvc.code, v  := hvc.proof.symm ▸ v }
  let had_key := self.storage.any (fun e => Entry.keyMatches e k)
  let filtered := self.storage.filter (fun e => ! Entry.keyMatches e k)
  let new_size := if had_key then self.size else self.size + 1
  { self with size := new_size, storage := entry :: filtered }

def remove {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [BEq K] [Inhabited V]
    (self : Bag U) (k : K) : V × Bag U :=
  let found? : Option V :=
    self.storage.findSome? (fun e =>
      if Entry.keyMatches e k then
        if hv : e.vc = hvc.code then
          some (hvc.proof ▸ hv ▸ e.v)
        else none
      else none)
  let v := found?.getD default
  let filtered := self.storage.filter (fun e => ! Entry.keyMatches e k)
  (v, { self with size := self.size - 1, storage := filtered })

def remove.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K] [Inhabited V]
    (_self : Bag U) (_k : K) : Bool := false

def borrow {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [BEq K] [Inhabited V]
    (self : Bag U) (k : K) : V :=
  let found? : Option V :=
    self.storage.findSome? (fun e =>
      if Entry.keyMatches e k then
        if hv : e.vc = hvc.code then
          some (hvc.proof ▸ hv ▸ e.v)
        else none
      else none)
  found?.getD default

def borrow.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K] [Inhabited V]
    (_self : Bag U) (_k : K) : Bool := false

/-- `bag::borrow_mut` — read-modify-write access to a bag value. The Mutable's
reconstruct writes the new value back via `set` (same key, same bag), so the
caller's `Mutable.apply` writeback lands in `Bag.storage`. Without this def the
Move-source lowering fell through to the `borrow_child_object_mut` default stub
and every bag read-modify-write was silently dropped (staking_pool
FungibleStakedSuiData supply/principal updates). -/
def borrow_mut {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K] [Inhabited V]
    (self : Bag U) (k : K) : (Mutable V (Bag U)) × Bag U :=
  (Mutable.mk (borrow K V self k) (fun v => set K V self k v), self)

def borrow_mut.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K] [Inhabited V]
    (_self : Bag U) (_k : K) : Bool := false

def contains {U : Type} [Universe U] (K : Type)

    [HasCode U K] [BEq K]
    (self : Bag U) (k : K) : Bool :=
  self.storage.any (fun e => Entry.keyMatches e k)

def contains.aborts {U : Type} [Universe U] (K : Type)
    [HasCode U K] [BEq K]
    (_self : Bag U) (_k : K) : Bool := false

def contains_with_type {U : Type} [Universe U] (K V : Type)
    [hkc : HasCode U K] [hvc : HasCode U V] [BEq K]
    (self : Bag U) (k : K) : Bool :=
  self.storage.any (fun e =>
    Entry.keyMatches e k && (e.vc = hvc.code))

def contains_with_type.aborts {U : Type} [Universe U] (K V : Type)
    [HasCode U K] [HasCode U V] [BEq K]
    (_self : Bag U) (_k : K) : Bool := false

def length {U : Type} [Universe U] (self : Bag U) : BoundedNat (2^64) := self.size
def length.aborts {U : Type} [Universe U] (_self : Bag U) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def is_empty {U : Type} [Universe U] (self : Bag U) : Bool :=
  self.size == (0 : BoundedNat (2^64))
def is_empty.aborts {U : Type} [Universe U] (_self : Bag U) : Option MoveAbort := if false then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def destroy_empty {U : Type} [Universe U] (_self : Bag U) : Unit := ()
def destroy_empty.aborts {U : Type} [Universe U] (self : Bag U) : Option MoveAbort :=
  if !(self.size == (0 : BoundedNat (2^64))) then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

end Bag
