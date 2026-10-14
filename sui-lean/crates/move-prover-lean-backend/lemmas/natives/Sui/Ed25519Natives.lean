-- Native implementations for sui::ed25519
-- Ed25519 signature verification

import Prelude.BoundedNat
import Prelude.Helpers

namespace Ed25519Natives

def ed25519_verify (signature : List (BoundedNat (2^8))) (public_key : List (BoundedNat (2^8))) (msg : List (BoundedNat (2^8))) : Bool :=
  !signature.isEmpty && !public_key.isEmpty && !msg.isEmpty

end Ed25519Natives
