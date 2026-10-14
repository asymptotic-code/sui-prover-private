-- Native implementations for sui::event

import Prelude.BoundedNat
import Prelude.Helpers

namespace Event

def emit (tv0 : Type) [BEq tv0] [Inhabited tv0] (_event : tv0) : Unit :=
  ()

def emit_authenticated_impl (tv0 : Type) [BEq tv0] [Inhabited tv0] (tv1 : Type) [BEq tv1] [Inhabited tv1] (_addr : Address) (_stream_id : Address) (_event : tv1) : Unit :=
  ()

def num_events : BoundedNat (2^32) := 0

def events_by_type (tv0 : Type) [BEq tv0] [Inhabited tv0] : List tv0 := []

end Event
