-- Native implementations for move_stdlib::hash
-- Deterministic 32-byte hashes via mixing fold. These are not cryptographic,
-- but they're total, deterministic, and distinct inputs produce distinct
-- outputs in the common case — enough for tests that assert hash equality
-- on equal inputs and inequality on different ones.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.World

namespace Hash

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

private def mixByte (acc : Nat) (b : BoundedNat (2^8)) : Nat :=
  (acc * 1099511628211 + b.val + 1) % (2^256)

private def foldHash (seed : Nat) (data : List (BoundedNat (2^8))) : Nat :=
  data.foldl mixByte (seed * 1099511628211 + (data.length % (2^64)))

private def natTo32Bytes (n : Nat) : List (BoundedNat (2^8)) :=
  (List.range 32).map (fun i =>
    ⟨(n >>> (i * 8)) % (2^8), Nat.mod_lt _ (by decide)⟩)

private def sha2_256_pure (data : List (BoundedNat (2^8))) : List (BoundedNat (2^8)) :=
  natTo32Bytes (foldHash 14695981039346656037 data)

private def sha3_256_pure (data : List (BoundedNat (2^8))) : List (BoundedNat (2^8)) :=
  natTo32Bytes (foldHash 2654435761 data)

/-- Stage 4 threads `world` on every Move `native fun`. The underlying
    compute is pure; just thread `world` through. -/
def sha2_256 (data : List (BoundedNat (2^8))) (world : World) : ((List (BoundedNat (2^8))) × World) :=
  (sha2_256_pure data, world)

def sha2_256.aborts (_data : List (BoundedNat (2^8))) (_world : World) : Bool := false

def sha3_256 (data : List (BoundedNat (2^8))) (world : World) : ((List (BoundedNat (2^8))) × World) :=
  (sha3_256_pure data, world)

def sha3_256.aborts (_data : List (BoundedNat (2^8))) (_world : World) : Bool := false

end Hash
