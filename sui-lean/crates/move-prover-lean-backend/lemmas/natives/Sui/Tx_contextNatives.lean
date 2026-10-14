-- Native implementations for sui::tx_context
-- These reflect runtime transaction-context state. In a real prover deployment
-- they would be modeled as opaque axioms; for test execution we return
-- `default` of each type so test bodies can evaluate without hitting `sorry`.
-- Tests that exercise actual transaction-context semantics use the
-- `TxContext` struct's own fields (sender / tx_hash / epoch / ...), which are
-- explicit struct fields, not these natives.

import Prelude.BoundedNat
import Prelude.Helpers

namespace Tx_contextNatives

def native_sender : Address := default
def native_epoch : BoundedNat (2^64) := default
def native_epoch_timestamp_ms : BoundedNat (2^64) := default
def native_rgp : BoundedNat (2^64) := default
def native_gas_price : BoundedNat (2^64) := default
def native_ids_created : BoundedNat (2^64) := default
def native_gas_budget : BoundedNat (2^64) := default
def native_sponsor : List Address := []
def fresh_id : Address := default
def last_created_id : Address := default
def derive_id (tx_hash : List (BoundedNat (2^8))) (ids_created : BoundedNat (2^64)) : Address :=
  let h := tx_hash.foldl (fun acc b => acc * 257 + b.val + 1) 1
  Address.mk ⟨(2 ^ 160 + h % 2 ^ 64 * 2 ^ 64 + ids_created.val) % 2 ^ 256, Nat.mod_lt _ (by decide)⟩
def replace (_sender : Address) (_tx_hash : List (BoundedNat (2^8))) (_epoch : BoundedNat (2^64)) (_epoch_timestamp_ms : BoundedNat (2^64)) (_ids_created : BoundedNat (2^64)) (_rgp : BoundedNat (2^64)) (_gas_price : BoundedNat (2^64)) (_gas_budget : BoundedNat (2^64)) (_sponsor : List Address) : Unit := ()

end Tx_contextNatives
