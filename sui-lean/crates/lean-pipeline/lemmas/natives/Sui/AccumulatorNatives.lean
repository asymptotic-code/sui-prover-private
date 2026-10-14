import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.World

namespace Accumulator

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

def emit_deposit_event
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (_accumulator : Address) (_recipient : Address) (_amount : BoundedNat (2^64))
    (world : World) : World :=
  world

def emit_withdraw_event
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (_accumulator : Address) (_owner : Address) (_amount : BoundedNat (2^64))
    (world : World) : World :=
  world


-- ============================================================================
-- Lemma layer (world-writers wave).
--
-- MODEL HONESTY: the accumulator event emitters are PURE PASS-THROUGHS, and
-- that is the FAITHFUL model, not a shortcut. In the VM
-- (`sui-execution/latest/sui-move-natives/src/accumulator.rs`) both forward to
-- `ObjectRuntime::emit_accumulator_event`, which appends to
-- `state.accumulator_events` and updates the accumulator merge/split totals.
-- It never touches `state.events` -- the vector `take_user_events` returns and
-- `test_scenario` counts into `num_user_events` -- so, unlike `event::emit`,
-- these must NOT bump `tx_user_events`. `test_scenario::end_transaction`
-- discards `accumulator_events` outright, so no Move-level observation the
-- World models can see them. They do not touch the world's `accumulator`
-- ledger either (those writes live in the `funds_accumulator` natives via
-- `World.accum_add` / `accum_sub`). One identity frame each states all of that
-- at once.
--
-- DISCLOSED GAP: `emit_accumulator_event` can raise `ARITHMETIC_ERROR` when a
-- key's cumulative merges/splits overflow `u64` within one transaction. There
-- is no `.aborts` companion here, so that abort is not modeled -- the same
-- shape `event::emit` already carries (`max_num_event_emit`). Unreachable at
-- this framework vintage: both are `public(package)` in `sui::accumulator`
-- with no caller anywhere in the framework.
-- ============================================================================

@[simp] theorem emit_deposit_event_world
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (accumulator recipient : Address) (amount : BoundedNat (2^64))
    (world : World) :
    emit_deposit_event tv0 accumulator recipient amount world = world := rfl

@[simp] theorem emit_withdraw_event_world
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (accumulator owner : Address) (amount : BoundedNat (2^64))
    (world : World) :
    emit_withdraw_event tv0 accumulator owner amount world = world := rfl

end Accumulator
