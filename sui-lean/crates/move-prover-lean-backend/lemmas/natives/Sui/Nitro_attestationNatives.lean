-- Native implementations for sui::nitro_attestation

import Prelude.BoundedNat
import Prelude.Helpers
import MoveStdlib.MoveOption

namespace Nitro_attestation

structure PCREntry where
  index : BoundedNat (2^8)
  value : List (BoundedNat (2^8))
deriving BEq
instance : Inhabited PCREntry where default := ⟨default, default⟩

structure NitroAttestationDocument where
  module_id : List (BoundedNat (2^8))
  timestamp : BoundedNat (2^64)
  digest : List (BoundedNat (2^8))
  pcrs : List PCREntry
  public_key : MoveOption.MoveOption (List (BoundedNat (2^8)))
  user_data : MoveOption.MoveOption (List (BoundedNat (2^8)))
  nonce : MoveOption.MoveOption (List (BoundedNat (2^8)))
deriving BEq
instance : Inhabited NitroAttestationDocument where default := ⟨default, default, default, default, default, default, default⟩

def load_nitro_attestation_internal (_attestation : List (BoundedNat (2^8))) (_timestamp_ms : BoundedNat (2^64)) : NitroAttestationDocument :=
  default

end Nitro_attestation
