-- Native: sui::random::RandomInner, split into its own leaf file.
-- `versioned::Versioned` carries a ghost dynamic-field type that
-- references `RandomInner`; keeping `RandomInner` here (Prelude-only
-- imports) lets the generated `Versioned` import just this leaf instead
-- of `RandomNatives.lean`, which imports `Sui.Versioned` for
-- `Random.inner` and would otherwise form a Random<->Versioned cycle.

import Prelude.BoundedNat
import Prelude.Helpers

namespace Random

-- Move source: `public struct RandomInner has store {
--   version: u64, epoch: u64, randomness_round: u64,
--   random_bytes: vector<u8> }`.
structure RandomInner where
  version          : BoundedNat (2^64)
  epoch            : BoundedNat (2^64)
  randomness_round : BoundedNat (2^64)
  random_bytes     : List (BoundedNat (2^8))
deriving DecidableEq
instance : Inhabited RandomInner where
  default := ⟨default, default, default, []⟩

end Random
