-- Hand-written Lean implementation of the `pending_values_specs` native
-- `vecmap_get_or_default`, replacing the translator's placeholder.
--
-- Move declaration:
--   public native fun vecmap_get_or_default(v: &VecMap<u64,u64>, k: &u64, d: u64): u64;
-- Semantics: look up key `k` in the VecMap; return its value, or the default `d`
-- if the key is absent.

import Prelude.BoundedNat
import Prelude.Helpers
import MoveStdlib.MoveOption
import Sui.Vec_mapNatives

namespace Pending_values

def vecmap_get_or_default
    (v : (Vec_map.VecMap (BoundedNat (2^64)) (BoundedNat (2^64))))
    (k : BoundedNat (2^64)) (d : BoundedNat (2^64)) : BoundedNat (2^64) :=
  match v.contents.find? (fun e => e.key == k) with
  | some e => e.value
  | none => d

end Pending_values
