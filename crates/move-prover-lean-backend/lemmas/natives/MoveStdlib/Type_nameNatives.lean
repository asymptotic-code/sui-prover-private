-- Native struct definitions for std::type_name

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.MoveAbort
import MoveStdlib.Ascii

namespace Type_name

structure TypeName where
  name : Ascii.MoveString
deriving BEq
instance : Inhabited TypeName where default := ⟨default⟩

def get (tv0 : Type) [BEq tv0] [Inhabited tv0] : TypeName :=
  default

def with_defining_ids (tv0 : Type) [BEq tv0] [Inhabited tv0] : TypeName :=
  default

def get_with_original_ids (tv0 : Type) [BEq tv0] [Inhabited tv0] : TypeName :=
  default

def with_original_ids (tv0 : Type) [BEq tv0] [Inhabited tv0] : TypeName :=
  default

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
