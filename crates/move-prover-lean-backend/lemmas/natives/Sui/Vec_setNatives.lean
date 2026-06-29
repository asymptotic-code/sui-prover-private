-- Native struct definitions for sui::vec_set

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.ProgramState
import MoveStdlib.MoveVector

namespace Vec_set

structure VecSet (tv0 : Type) where
  contents : List tv0
deriving BEq
instance [Inhabited tv0] : Inhabited (VecSet tv0) where default := ⟨default⟩

end Vec_set
