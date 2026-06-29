-- Native implementations for sui::config

import Prelude.BoundedNat
import Prelude.Helpers
import MoveStdlib.MoveOption

namespace Config

def read_setting_impl (_tv0 : Type) [BEq _tv0] [Inhabited _tv0] (_tv1 : Type) [BEq _tv1] [Inhabited _tv1] (_tv2 : Type) [BEq _tv2] [Inhabited _tv2] (tv3 : Type) [BEq tv3] [Inhabited tv3] (_config_id : Address) (_setting_df : Address) (_epoch : BoundedNat (2^64)) : MoveOption.MoveOption tv3 :=
  default

end Config
