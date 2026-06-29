-- Native implementations for sui::ecdsa_r1
-- Secp256r1 elliptic curve operations

import Prelude.BoundedNat
import Prelude.Helpers

namespace Ecdsa_r1Natives

def secp256r1_ecrecover (_signature : List (BoundedNat (2^8))) (_msg : List (BoundedNat (2^8))) (_hash : BoundedNat (2^8)) : List (BoundedNat (2^8)) := []

def secp256r1_verify (signature : List (BoundedNat (2^8))) (public_key : List (BoundedNat (2^8))) (msg : List (BoundedNat (2^8))) (_hash : BoundedNat (2^8)) : Bool :=
  !signature.isEmpty && !public_key.isEmpty && !msg.isEmpty

end Ecdsa_r1Natives
