-- Native implementations for sui::balance (Supply)

import Prelude.BoundedNat
import Prelude.Helpers

namespace Balance_M

structure Supply (tv0 : Type) where
  value : BoundedNat (2^64)
deriving BEq
instance [Inhabited tv0] : Inhabited (Supply tv0) where default := ⟨default⟩

end Balance_M
