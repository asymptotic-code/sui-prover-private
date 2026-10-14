-- Native implementations for move_stdlib::bcs
-- Binary Canonical Serialization
--
-- BCS serialization is value-dependent. Full BCS is not modeled in pure
-- Lean, but the encoding must be value-DISTINGUISHING where object identity
-- depends on it: `test_scenario` derives each transaction's tx_hash from
-- `bcs::to_bytes(txn_number)` (`dummy_tx_hash_with_hint`), and
-- `fresh_object_address` = `derive_id(tx_hash, ids_created)`. A constant
-- stub made every tx share one tx_hash, so the k-th object of ANY tx got
-- the same uid and the World store silently clobbered earlier objects
-- (`putOwned` replace-on-collision) — reward mints overwrote stakers'
-- StakedSui. `BcsBytes` dispatches on the value type: u64 gets a real
-- little-endian encoding (covers the tx-hash path); everything else keeps
-- the empty stub, so tests that assert specific byte patterns of other
-- types still fail loudly rather than pass on fabricated bytes.

import Prelude.BoundedNat
import Prelude.Helpers

namespace BcsNatives

class BcsBytes (α : Type) where
  bytes : α → List (BoundedNat (2^8))

instance (priority := low) (α : Type) : BcsBytes α := ⟨fun _ => []⟩

instance : BcsBytes (BoundedNat (2^64)) :=
  ⟨fun v =>
    [0, 8, 16, 24, 32, 40, 48, 56].map (fun s =>
      ⟨(v.val >>> s) % 2 ^ 8, Nat.mod_lt _ (by decide)⟩)⟩

def to_bytes (_tv0 : Type) [BEq _tv0] [Inhabited _tv0] [BcsBytes _tv0] (_v : _tv0) :
    List (BoundedNat (2^8)) :=
  BcsBytes.bytes _v

end BcsNatives
