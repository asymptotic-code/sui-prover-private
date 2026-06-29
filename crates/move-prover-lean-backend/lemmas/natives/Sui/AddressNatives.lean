-- Native implementations for sui::address

import Prelude.BoundedNat
import Prelude.Helpers

namespace Address

-- Fold the byte list (big-endian) into a 256-bit address. Bytes after the
-- 32nd are ignored (Sui addresses are 32 bytes); missing bytes are treated
-- as zero. Round-trips with `to_bytes` for canonical 32-byte inputs.
private def bytesToNat (bytes : List (BoundedNat (2^8))) : Nat :=
  bytes.foldl (fun acc b => (acc * 256 + b.val) % (2^256)) 0

def from_bytes (bytes : List (BoundedNat (2^8))) : Address :=
  Address.mk ⟨bytesToNat bytes % (2^256), Nat.mod_lt _ (by decide)⟩

def from_u256 (n : BoundedNat (2^256)) : Address :=
  Address.mk n

def to_u256 (a : Address) : BoundedNat (2^256) :=
  a.bytes

end Address
