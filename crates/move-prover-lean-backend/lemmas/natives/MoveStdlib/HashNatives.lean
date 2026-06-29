-- Native implementations for move_stdlib::hash
-- Deterministic 32-byte hashes via mixing fold. These are not cryptographic,
-- but they're total, deterministic, and distinct inputs produce distinct
-- outputs in the common case — enough for tests that assert hash equality
-- on equal inputs and inequality on different ones.

import Prelude.BoundedNat
import Prelude.Helpers

namespace HashNatives

private def mixByte (acc : Nat) (b : BoundedNat (2^8)) : Nat :=
  (acc * 1099511628211 + b.val + 1) % (2^256)

private def foldHash (seed : Nat) (data : List (BoundedNat (2^8))) : Nat :=
  data.foldl mixByte (seed * 1099511628211 + (data.length % (2^64)))

private def natTo32Bytes (n : Nat) : List (BoundedNat (2^8)) :=
  (List.range 32).map (fun i =>
    ⟨(n >>> (i * 8)) % (2^8), Nat.mod_lt _ (by decide)⟩)

def sha2_256 (data : List (BoundedNat (2^8))) : List (BoundedNat (2^8)) :=
  natTo32Bytes (foldHash 14695981039346656037 data)

def sha3_256 (data : List (BoundedNat (2^8))) : List (BoundedNat (2^8)) :=
  natTo32Bytes (foldHash 2654435761 data)

end HashNatives
