-- Native implementations for sui::funds_accumulator

import Prelude.BoundedNat
import Prelude.Helpers

namespace Funds_accumulator

def withdraw_from_accumulator_address (_tv0 : Type) [BEq _tv0] [Inhabited _tv0] (_accumulator : Address) (_owner : Address) (_value : BoundedNat (2^256)) : _tv0 :=
  default

def add_to_accumulator_address (tv0 : Type) [BEq tv0] [Inhabited tv0] (_accumulator : Address) (_recipient : Address) (_value : tv0) : Unit :=
  ()

end Funds_accumulator
