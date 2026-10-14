-- Native implementations for sui::poseidon
-- Deterministic 32-byte fold over the input chunks. Distinct chunked
-- inputs produce distinct outputs in the common case.

import Prelude.BoundedNat
import Prelude.Helpers

namespace Poseidon

private def mixByte (acc : Nat) (b : BoundedNat (2^8)) : Nat :=
  (acc * 1099511628211 + b.val + 1) % (2^256)

private def foldChunks (data : List (List (BoundedNat (2^8)))) : Nat :=
  data.foldl
    (fun acc chunk =>
      let acc' := (acc * 1099511628211 + (chunk.length % (2^64))) % (2^256)
      chunk.foldl mixByte acc')
    11400714785074694791

private def natTo32Bytes (n : Nat) : List (BoundedNat (2^8)) :=
  (List.range 32).map (fun i =>
    ⟨(n >>> (i * 8)) % (2^8), Nat.mod_lt _ (by decide)⟩)

def poseidon_bn254_internal (data : List (List (BoundedNat (2^8)))) : List (BoundedNat (2^8)) :=
  natTo32Bytes (foldChunks data)

end Poseidon
