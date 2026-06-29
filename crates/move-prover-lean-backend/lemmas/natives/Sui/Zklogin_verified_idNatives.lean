-- Native definitions for sui::zklogin_verified_id

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.MoveAbort
import MoveStdlib.MoveString
import Sui.Tx_context

namespace Zklogin_verified_id

def check_zklogin_id (_address : Address) (_key_claim_name : MoveString.MoveString) (_key_claim_value : MoveString.MoveString) (_issuer : MoveString.MoveString) (_audience : MoveString.MoveString) (_pin_hash : BoundedNat (2^256)) : Bool :=
  false

def check_zklogin_id.aborts (_address : Address) (_key_claim_name : MoveString.MoveString) (_key_claim_value : MoveString.MoveString) (_issuer : MoveString.MoveString) (_audience : MoveString.MoveString) (_pin_hash : BoundedNat (2^256)) : Option MoveAbort :=
  if False then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def check_zklogin_id_internal (_address : Address) (_key_claim_name : List (BoundedNat (2^8))) (_key_claim_value : List (BoundedNat (2^8))) (_issuer : List (BoundedNat (2^8))) (_audience : List (BoundedNat (2^8))) (_pin_hash : BoundedNat (2^256)) : Bool :=
  false

def check_zklogin_id_internal.aborts (_address : Address) (_key_claim_name : List (BoundedNat (2^8))) (_key_claim_value : List (BoundedNat (2^8))) (_issuer : List (BoundedNat (2^8))) (_audience : List (BoundedNat (2^8))) (_pin_hash : BoundedNat (2^256)) : Option MoveAbort :=
  if False then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

def verify_zklogin_id (_key_claim_name : MoveString.MoveString) (_key_claim_value : MoveString.MoveString) (_issuer : MoveString.MoveString) (_audience : MoveString.MoveString) (_pin_hash : BoundedNat (2^256)) (_ctx : Tx_context.TxContext) : Tx_context.TxContext :=
  _ctx

def verify_zklogin_id.aborts (_key_claim_name : MoveString.MoveString) (_key_claim_value : MoveString.MoveString) (_issuer : MoveString.MoveString) (_audience : MoveString.MoveString) (_pin_hash : BoundedNat (2^256)) (_ctx : Tx_context.TxContext) : Option MoveAbort :=
  if False then Option.some { source := MoveAbort.AbortSource.userAssert, code := 0 } else Option.none

end Zklogin_verified_id
