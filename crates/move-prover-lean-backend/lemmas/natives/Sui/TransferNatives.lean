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

def party_transfer_impl (tv0 : Type) [BEq tv0] [Inhabited tv0] (_obj : tv0) (_default : BoundedNat (2^64)) (_addresses : List Address) (_permissions : List (BoundedNat (2^64))) : Unit :=
  ()

end Transfer
