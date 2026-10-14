-- Native implementations for sui::hmac
-- Deterministic HMAC-SHA3-256 surrogate: distinct (key, msg) pairs yield
-- distinct 32-byte outputs.

import Prelude.BoundedNat
import Prelude.Helpers

namespace HmacNatives

private def mixByte (acc : Nat) (b : BoundedNat (2^8)) : Nat :=
  (acc * 1099511628211 + b.val + 1) % (2^256)

private def natTo32Bytes (n : Nat) : List (BoundedNat (2^8)) :=
  (List.range 32).map (fun i =>
    ⟨(n >>> (i * 8)) % (2^8), Nat.mod_lt _ (by decide)⟩)

def hmac_sha3_256 (key : List (BoundedNat (2^8))) (msg : List (BoundedNat (2^8))) : List (BoundedNat (2^8)) :=
  let seed := 14695981039346656037 * 1099511628211 + (key.length % (2^64)) * 256 + (msg.length % (2^64))
  let acc1 := key.foldl mixByte (seed % (2^256))
  let acc2 := msg.foldl mixByte acc1
  natTo32Bytes acc2

end HmacNatives
