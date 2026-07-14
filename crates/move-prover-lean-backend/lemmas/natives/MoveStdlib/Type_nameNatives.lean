-- Native struct definitions for std::type_name

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.MoveAbort
import Prelude.Universe
import MoveStdlib.Ascii

namespace Type_name

structure TypeName where
  name : Ascii.MoveString
deriving BEq
instance : Inhabited TypeName where default := ⟨default⟩

-- Encode a Lean `String` as a list of `BoundedNat (2^8)` bytes.
private def stringToBytes (s : String) : List (BoundedNat (2^8)) :=
  s.toList.map (fun c => ⟨c.toNat % (2^8), Nat.mod_lt _ (by decide)⟩)

-- Build a `TypeName` whose bytes are the Move fully-qualified type name of
-- `T`, supplied per code by `Universe.typeName`. Distinct Move types have
-- distinct FQNs, so `type_name::get<A> ≠ type_name::get<B>` for `A ≠ B` — the
-- property coin canonical ordering (`is_right_order`) and type-keyed lookups
-- rely on. The old `:= default` collapsed every type to one name (sound for
-- uninterpreted spec verification, wrong for concrete execution). The universe
-- `U` is NOT inferable from the trailing `[HasCode U T]` (Lean resolves
-- `[Universe U]` left-to-right first and stalls on the metavariable), so the
-- renderer pins it explicitly at every call site as `Type_name.get (U := BagU)`.
private def fromCode {U : Type} [Universe U] [Repr U] (T : Type) [hc : HasCode U T] : TypeName :=
  { name := { bytes := stringToBytes (Universe.typeName hc.code) } }

def get {U : Type} [Universe U] [Repr U] (T : Type) [BEq T] [Inhabited T] [HasCode U T] :
    TypeName :=
  fromCode (U := U) T

def with_defining_ids {U : Type} [Universe U] [Repr U] (T : Type) [BEq T] [Inhabited T]
    [HasCode U T] : TypeName :=
  fromCode (U := U) T

def get_with_original_ids {U : Type} [Universe U] [Repr U] (T : Type) [BEq T] [Inhabited T]
    [HasCode U T] : TypeName :=
  fromCode (U := U) T

def with_original_ids {U : Type} [Universe U] [Repr U] (T : Type) [BEq T] [Inhabited T]
    [HasCode U T] : TypeName :=
  fromCode (U := U) T

@[reducible] def is_primitive (_t : TypeName) : Bool :=
  false

def is_primitive.aborts (_t : TypeName) : Option MoveAbort :=
  if False then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

-- Stub: real address depends on runtime type info. Returns a default address.
def defining_id (_tv0 : Type) [BEq _tv0] [Inhabited _tv0] : Address :=
  default

def original_id (_tv0 : Type) [BEq _tv0] [Inhabited _tv0] : Address :=
  default

end Type_name
