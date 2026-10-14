-- Native implementations for sui::zklogin_verified_issuer

import Prelude.BoundedNat
import Prelude.Helpers

namespace Zklogin_verified_issuer

def check_zklogin_issuer_internal (_address : Address) (_address_seed : BoundedNat (2^256)) (issuer_bytes : List (BoundedNat (2^8))) : Bool :=
  !issuer_bytes.isEmpty

end Zklogin_verified_issuer
