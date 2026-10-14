-- Native implementations for std::unit_test.
-- These are #[test_only] Move-native functions that exist for the
-- unit-test framework: `poison` is a link-check pill the Move
-- compiler injects into every test-mode module (see
-- `move-compiler/src/unit_test/filter_test_members.rs::create_test_poison`)
-- and `destroy` is a black-hole that drops any value in test mode.
-- Stage 4 (effects) augments both with a World-threading param.
--
-- Lean has nothing to enforce here: poison is a no-op (we don't
-- model VM publish-link safety) and destroy just discards the value
-- (Lean's GC handles the rest). Both thread `world` unchanged.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.World

namespace Unit_test

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

def poison (world : World) : World := world

def destroy (_tv0 : Type) [BEq _tv0] [Inhabited _tv0] (_v : _tv0) (world : World) : World :=
  world

end Unit_test
