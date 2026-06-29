-- Native implementations for sui::vdf
-- Cryptographic VDF (Verifiable Delay Function) operations

import Prelude.BoundedNat
import Prelude.Helpers

namespace VdfNatives

private def mixByte (acc : Nat) (b : BoundedNat (2^8)) : Nat :=
  (acc * 1099511628211 + b.val + 1) % (2^256)

private def natTo32Bytes (n : Nat) : List (BoundedNat (2^8)) :=
  (List.range 32).map (fun i =>
    ⟨(n >>> (i * 8)) % (2^8), Nat.mod_lt _ (by decide)⟩)

def hash_to_input_internal (message : List (BoundedNat (2^8))) : List (BoundedNat (2^8)) :=
  let seed := 14695981039346656037 * 1099511628211 + (message.length % (2^64))
  natTo32Bytes (message.foldl mixByte (seed % (2^256)))

def vdf_verify_internal (input : List (BoundedNat (2^8))) (output : List (BoundedNat (2^8))) (proof : List (BoundedNat (2^8))) (iterations : BoundedNat (2^64)) : Bool :=
  !input.isEmpty && !output.isEmpty && !proof.isEmpty && iterations.val > 0

end VdfNatives
