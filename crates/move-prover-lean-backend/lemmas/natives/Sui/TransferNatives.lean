-- Native implementations for sui::transfer

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.MoveAbort
import Prelude.MoveType
import Sui.ObjectNatives

namespace Transfer

def receive_impl (tv0 : Type) [BEq tv0] [Inhabited tv0] (_parent : Address) (_id : Object.ID)
    (_version : BoundedNat (2^64)) : tv0 :=
  MoveAbort.raiseAbortNoModule 0 MoveAbort.AbortSource.userAssert

def freeze_object_impl (tv0 : Type) [BEq tv0] [Inhabited tv0] (_obj : tv0) : Unit :=
  ()

def share_object_impl (tv0 : Type) [BEq tv0] [Inhabited tv0] (_obj : tv0) : Unit :=
  ()

def transfer_impl (tv0 : Type) [BEq tv0] [Inhabited tv0] (_obj : tv0) (_recipient : Address) : Unit :=
  ()

-- Ghost-augmented variant: the generator routes a ghost-threaded
-- `transfer_impl` call here (see `analysis/ghost_threading.rs`). Trailing
-- slots are the threaded ghost markers, positional, sorted by marker
-- struct name: SpecTransferAddress (Address), SpecTransferAddressExists
-- (Bool). Incoming values are overwritten per `transfer_impl_spec`'s
-- ensures (last transfer wins).
def transfer_impl__ghost (tv0 : Type) [BEq tv0] [Inhabited tv0] (_obj : tv0) (recipient : Address)
    (_ghost_addr : Address) (_ghost_exists : Bool) : (Address × Bool) :=
  (recipient, true)

def party_transfer_impl (tv0 : Type) [BEq tv0] [Inhabited tv0] (_obj : tv0) (_default : BoundedNat (2^64)) (_addresses : List Address) (_permissions : List (BoundedNat (2^64))) : Unit :=
  ()

end Transfer
