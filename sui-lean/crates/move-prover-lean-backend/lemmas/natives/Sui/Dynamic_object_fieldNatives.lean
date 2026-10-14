-- Native struct definitions for sui::dynamic_object_field

import Prelude.BoundedNat
import Prelude.Helpers

namespace Dynamic_object_field

structure Wrapper (tv0 : Type) where
  name : tv0
deriving BEq
instance [Inhabited tv0] : Inhabited (Wrapper tv0) where default := ⟨default⟩

end Dynamic_object_field
