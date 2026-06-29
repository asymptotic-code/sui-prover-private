-- Native implementations for sui::random

import Prelude.BoundedNat
import Prelude.Helpers

namespace Random

-- 32 zero bytes — deterministic and unobservable for tests that don't
-- depend on cryptographic randomness.
def generate_rand_seed_for_testing : List (BoundedNat (2^8)) :=
  List.replicate 32 ⟨0, by decide⟩

end Random
