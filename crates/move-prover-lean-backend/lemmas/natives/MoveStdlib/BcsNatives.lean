-- Native implementations for move_stdlib::bcs
-- Binary Canonical Serialization
--
-- BCS serialization is value-dependent and not modeled in pure Lean. Tests
-- that don't actually inspect the byte output just need this to evaluate.
-- Returning an empty list lets such tests run; tests that verify specific
-- serialization byte patterns will fail their assertions, which is the
-- correct outcome for a stub.

import Prelude.BoundedNat
import Prelude.Helpers

namespace BcsNatives

def to_bytes (_tv0 : Type) [BEq _tv0] [Inhabited _tv0] (_v : _tv0) : List (BoundedNat (2^8)) := []

end BcsNatives
