-- Native struct definitions for std::type_name

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.Universe
import Prelude.World
import MoveStdlib.Ascii

namespace Type_name

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

structure TypeName where
  name : Ascii.MoveString
deriving DecidableEq
instance : Inhabited TypeName where default := ⟨default⟩

-- Encode a Lean `String` as a list of `BoundedNat (2^8)` bytes.
-- We compute the character code modulo 256; for ASCII (which is
-- what `Repr` for our `TyCode` produces) the modulo is a no-op,
-- but it keeps the function total for arbitrary chars.
private def stringToBytes (s : String) : List (BoundedNat (2^8)) :=
  s.toList.map (fun c =>
    ⟨c.toNat % (2^8), Nat.mod_lt _ (by decide)⟩)

-- Build a `TypeName` whose bytes are the Move fully-qualified type
-- name (`<64hex-addr>::<module>::<Type>`) of `T`, supplied per code by
-- `Universe.typeName`. This makes `bcs::to_bytes(type_name X)` order
-- the same as Move's (coin canonical ordering in `create_pool` sorts
-- coins by these bytes), and remains distinct per type (distinct Move
-- types have distinct FQNs). `[Repr U]` is retained as an (unused)
-- constraint so the renderer's existing per-typeparam constraint
-- plumbing is untouched.
private def fromCode {U : Type} [Universe U] [Repr U] (T : Type) [hc : HasCode U T] : TypeName :=
  { name := { bytes := stringToBytes (Universe.typeName hc.code) } }

def get {U : Type} [Universe U] [Repr U] (T : Type) [BEq T] [Inhabited T] [HasCode U T] : TypeName :=
  fromCode (U := U) T

-- `bcs::to_bytes(tn : TypeName)`. `std::bcs::to_bytes` of a struct is
-- the concatenation of its fields' BCS; `TypeName { name : String }`
-- serializes to `ULEB128(len) ++ name.bytes`. The generic
-- `Bcs.to_bytes` is a `[]` stub (BCS is value-dependent and unmodeled),
-- so the renderer routes `bcs::to_bytes<TypeName>` here. The ULEB128
-- length prefix is load-bearing for coin ordering: Move compares the
-- prefixed bytes, so a SHORTER type name sorts first regardless of
-- content (e.g. `..::WAL` (len 82) < `..::USDC` (len 83)). Type names
-- are < 128 bytes in practice, so the single-byte form (`[len]`) is the
-- exact ULEB128 encoding; `% 2^8` keeps it total.
--
-- Audited 2026-08-02. Where this model and real BCS part company:
--   len < 128   byte-exact (real ULEB128 is also one byte).
--   128..255    NOT byte-exact -- real BCS emits `[len, 1]`, this emits
--               `[len]` -- but ORDER-equivalent, which is all the coin
--               ordering needs: the first byte still decides whenever the
--               lengths differ, and when they are equal both sides fall
--               through to the name bytes in the same order.
--   >= 256      genuinely divergent: `% 2^8` WRAPS (len 300 -> first byte
--               44) where real ULEB128 gives `[172, 2]`, so a comparison
--               against a short name can flip. The `% 2^8` is a totality
--               shim, NOT an unreachable branch.
-- Every type name in every corpus we generate is well inside the exact
-- range (longest measured: momentum 106 bytes, cetus 110), so the model is
-- byte-exact on all verified ground. The residual caveat is a DEPLOYED call
-- at a type name >= 256 bytes -- reachable in principle via nested generic
-- coin types (an LP-of-LP), instantiated by no corpus. Do not widen this to
-- `bcsUleb128` casually: the single byte is load-bearing in existing proofs.
def to_bytes (tn : TypeName) : List (BoundedNat (2^8)) :=
  let b := tn.name.bytes
  ⟨b.length % (2^8), Nat.mod_lt _ (by decide)⟩ :: b

def with_defining_ids {U : Type} [Universe U] [Repr U] (T : Type) [BEq T] [Inhabited T] [HasCode U T] : TypeName :=
  fromCode (U := U) T

def get_with_original_ids {U : Type} [Universe U] [Repr U] (T : Type) [BEq T] [Inhabited T] [HasCode U T] : TypeName :=
  fromCode (U := U) T

def with_original_ids {U : Type} [Universe U] [Repr U] (T : Type) [BEq T] [Inhabited T] [HasCode U T] : TypeName :=
  fromCode (U := U) T

@[reducible] def is_primitive (_t : TypeName) : Bool :=
  false

def is_primitive.aborts (_t : TypeName) : Bool :=
  False

-- Stub: real address depends on runtime type info. Returns a default address.
def defining_id (_tv0 : Type) [BEq _tv0] [Inhabited _tv0] : Address :=
  default

def original_id (_tv0 : Type) [BEq _tv0] [Inhabited _tv0] : Address :=
  default

-- `type_name::address_string` / `::module_string` extract substrings of
-- the FQN `TypeName.name` (`<64hex-addr>::<module>::<Type...>`). The
-- address is segment 0, the module is segment 2 (see `splitColon`).
-- Each aborts in Move iff `self.is_primitive()`; captured by the
-- `.aborts` companion, no global world effect -> PurePartial.
--
-- Split a byte list on single `:` (0x3A = 58). An FQN
-- `<addr>::<module>::<Type...>` splits to `[addr, "", module, "", Type...]`
-- because each `::` is two colons with an empty segment between. So
-- segment 0 is the address and segment 2 is the module. (Type args can
-- carry further `::`, but they sit in segment >= 4, so address/module
-- extraction is unaffected.) Previously these returned the WHOLE name,
-- making `package::from_module`/`from_package` comparisons (a Publisher's
-- stored package vs a type's address) always fail -- e.g. cetus
-- `set_display`'s EPublisherNotMatchWithModule (code 26).
private def splitColon : List (BoundedNat (2^8)) → List (List (BoundedNat (2^8)))
  | [] => [[]]
  | b :: rest =>
    let segs := splitColon rest
    if b.val == 58 then
      [] :: segs
    else
      match segs with
      | [] => [[b]]
      | s :: ss => (b :: s) :: ss

private def fqnSegment (bs : List (BoundedNat (2^8))) (i : Nat) : List (BoundedNat (2^8)) :=
  (splitColon bs).getD i []

def address_string (self : TypeName) : Ascii.MoveString :=
  { bytes := fqnSegment self.name.bytes 0 }

def address_string.aborts (_self : TypeName) : Bool := false

/-- `std::type_name::get_address` -- same projection as
`address_string` (the Move source delegates to it). Partial like its
sibling: aborts (per the `.aborts` companion pattern) when the name
carries no address segment; the stub itself is total. -/
def get_address (self : TypeName) : Ascii.MoveString :=
  address_string self

def get_address.aborts (self : TypeName) : Bool :=
  address_string.aborts self

def module_string (self : TypeName) : Ascii.MoveString :=
  { bytes := fqnSegment self.name.bytes 2 }

def module_string.aborts (_self : TypeName) : Bool := false

def datatype_string (self : TypeName) : Ascii.MoveString :=
  self.name

def datatype_string.aborts (_self : TypeName) : Bool := false

def as_string (self : TypeName) : Ascii.MoveString :=
  self.name

-- `type_name::into_string(name: TypeName): ascii::String` -- destroys
-- the TypeName and returns the underlying ascii string. The Lean
-- model just returns the inner name; Lean's GC handles the "destroy"
-- side. Total.
def into_string (self : TypeName) : Ascii.MoveString :=
  self.name

def into_string.aborts (_self : TypeName) : Bool := false

end Type_name
