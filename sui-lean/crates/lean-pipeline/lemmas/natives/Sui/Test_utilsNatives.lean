import Prelude.Helpers
import Prelude.World

namespace Test_utils

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

def create_one_time_witness
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (world : World) : (tv0 × World) :=
  (default, world)

end Test_utils
