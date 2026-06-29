-- Native implementations for sui::ecvrf
-- ECVRF (Elliptic Curve Verifiable Random Function) operations

import Prelude.BoundedNat
import Prelude.Helpers

namespace EcvrfNatives

def ecvrf_verify (hash : List (BoundedNat (2^8))) (alpha_string : List (BoundedNat (2^8))) (public_key : List (BoundedNat (2^8))) (proof : List (BoundedNat (2^8))) : Bool :=
  !hash.isEmpty && !alpha_string.isEmpty && !public_key.isEmpty && !proof.isEmpty

end EcvrfNatives
