-- Native struct definitions for sui::table

import Prelude.BoundedNat
import Prelude.Helpers
import Sui.ObjectNatives

namespace Table

structure Table (tv0 : Type) (tv1 : Type) where
  id : Object.UID
  size : BoundedNat (2^64)
  dynamic_fields : List (tv0 × tv1)
deriving BEq
instance [Inhabited tv0] [Inhabited tv1] : Inhabited (Table tv0 tv1) where default := ⟨default, default, default⟩

end Table
