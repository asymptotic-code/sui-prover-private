-- Native struct definitions for sui::vec_map

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.ProgramState
import MoveStdlib.MoveVector
import MoveStdlib.MoveOption

namespace Vec_map

structure Entry (tv0 : Type) (tv1 : Type) where
  key : tv0
  value : tv1
deriving BEq
instance [Inhabited tv0] [Inhabited tv1] : Inhabited (Entry tv0 tv1) where default := ⟨default, default⟩

structure VecMap (tv0 : Type) (tv1 : Type) where
  contents : List (Entry tv0 tv1)
deriving BEq
instance [Inhabited tv0] [Inhabited tv1] : Inhabited (VecMap tv0 tv1) where default := ⟨default⟩

end Vec_map
