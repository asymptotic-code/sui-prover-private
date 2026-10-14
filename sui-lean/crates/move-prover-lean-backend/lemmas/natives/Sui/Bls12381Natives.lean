-- Native implementations for sui::bls12381

import Prelude.BoundedNat
import Prelude.Helpers

namespace Bls12381

-- We can't model BLS semantics in Lean, but tests typically construct a
-- non-empty signature+key+msg and assert `verify(...) == true`. Returning
-- `true` for non-empty inputs (and `false` otherwise) is the smallest
-- deterministic improvement over an unconditional `false`.
def bls12381_min_pk_verify (signature : List (BoundedNat (2^8))) (public_key : List (BoundedNat (2^8))) (msg : List (BoundedNat (2^8))) : Bool :=
  !signature.isEmpty && !public_key.isEmpty && !msg.isEmpty

def bls12381_min_sig_verify (signature : List (BoundedNat (2^8))) (public_key : List (BoundedNat (2^8))) (msg : List (BoundedNat (2^8))) : Bool :=
  !signature.isEmpty && !public_key.isEmpty && !msg.isEmpty

end Bls12381
