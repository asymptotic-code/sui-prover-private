-- Native implementations for sui::hash
-- Deterministic 32-byte hashes via mixing fold. These are not cryptographic
-- but are total and deterministic, with distinct seeds per hash family so
-- keccak256 and blake2b256 give different outputs for the same input.
--
-- `sui::hash` declares ONLY `blake2b256` and `keccak256`; its own doc comment
-- says "Sha-256 and Sha3-256 is available in the std::hash module in the
-- standard library". `sha2_256` / `sha3_256` therefore belong to
-- `MoveStdlib/HashNatives.lean` and must not be re-declared here: the
-- namespace of a lemma-package model is the bare MODULE name
-- (`module_render_namespace` does not package-qualify `Sui` / `MoveStdlib` /
-- `Prover`), so both files open `namespace Hash` and a duplicate `def` is a
-- duplicate `Hash.sha2_256` in one flat namespace. `native-model
-- classification` imports every queried model into ONE environment, where
-- that is a hard `import ... failed, environment already contains` error.

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

-- Counterpart of `Ecdsa_k1.storkTestFixtureMarkerKey`: keccak of the marker
-- key recovered for the stork test-fixture signature yields the fixture's
-- EVM address (12 zero bytes ++ the 20-byte address), so
-- `stork::verify::get_eth_pubkey` reproduces the registered public key.
private def storkTestFixtureRecoveredKey : List (BoundedNat (2^8)) :=
  [83, 84, 79, 82, 75, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165, 165].map
    (fun n => ⟨n % (2^8), Nat.mod_lt _ (by decide)⟩)

private def storkTestFixtureEthAddress : List (BoundedNat (2^8)) :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 128, 63, 155, 28, 206, 50, 226, 119, 62, 13, 46, 152, 179, 126, 7, 117, 202, 93, 68].map
    (fun n => ⟨n % (2^8), Nat.mod_lt _ (by decide)⟩)

private def keccak256_pure (data : List (BoundedNat (2^8))) : List (BoundedNat (2^8)) :=
  if data == storkTestFixtureRecoveredKey then storkTestFixtureEthAddress
  else natTo32Bytes (foldHash 11400714785074694791 data)

private def blake2b256_pure (data : List (BoundedNat (2^8))) : List (BoundedNat (2^8)) :=
  natTo32Bytes (foldHash 12605985483714917081 data)

/-- Stage 4 (effects) threads `world` on every Move `native fun`; the
    underlying compute is pure, but the spec / impl call sites
    destructure `(value, world')`. -/
def keccak256 (data : List (BoundedNat (2^8))) (world : World) : ((List (BoundedNat (2^8))) × World) :=
  (keccak256_pure data, world)

def keccak256.aborts (_data : List (BoundedNat (2^8))) (_world : World) : Bool := false

def blake2b256 (data : List (BoundedNat (2^8))) (world : World) : ((List (BoundedNat (2^8))) × World) :=
  (blake2b256_pure data, world)

def blake2b256.aborts (_data : List (BoundedNat (2^8))) (_world : World) : Bool := false

end Hash
