-- Native implementations for sui::event.
-- Per stage 4 (effects), `event::emit<T>` takes a world and returns
-- a world. The body threads the world through and bumps the world's
-- per-transaction user-event counter (`tx_user_events`) so that
-- `test_scenario::next_tx(...).num_user_events()` reports the right
-- count. The typed event payload is not recorded in the world's
-- `events` log (the generic native cannot inject `tv0` into the
-- per-package `Event` universe); only the count is tracked.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.World
import Sui.Tx_contextNatives

namespace Event

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

/-- `event::emit<T>(e)` -- threads `world` per stage 4 and bumps the
    current transaction's user-event counter so
    `test_scenario::next_tx(...).num_user_events()` reports it. The
    typed payload is not recorded (the generic native cannot inject
    `tv0` into the per-package `Event` universe); only the count is
    tracked, which is what `num_user_events` observes. -/
def emit (tv0 : Type) [BEq tv0] [Inhabited tv0] (_event : tv0) (world : World) : World :=
  Prover.World.World.bump_user_events world

/-- `event::emit_authenticated_impl<T1, T2>(...)` -- threads `world`. -/
def emit_authenticated_impl
    (tv0 : Type) [BEq tv0] [Inhabited tv0]
    (tv1 : Type) [BEq tv1] [Inhabited tv1]
    (_addr : Address) (_stream_id : Address) (_event : tv1) (world : World) : World :=
  Prover.World.World.bump_user_events world

def num_events : BoundedNat (2^32) := 0

def events_by_type (tv0 : Type) [BEq tv0] [Inhabited tv0] : List tv0 := []


-- ============================================================================
-- Lemma layer: emit faces and frames (world-writers wave).
--
-- MODEL HONESTY: `event::emit` does NOT append the payload to the world's
-- `events` log -- the generic native cannot inject `tv0` into the per-package
-- `Event` universe (see the header above), so the model records ONLY the
-- per-transaction count (`tx_user_events`). The pretty lemma "emit appends to
-- the event log" is FALSE in this model; the true faces are below: `events`
-- is a FRAME of `emit`, and the transition face is the counter bump.
-- `@[simp]` only on rfl-class faces/frames per the lemma-wave discipline.
-- ============================================================================

section EmitLemmas

-- NOTE: the `World` local notation does not resolve the outer `__World*`
-- variables when used in a nested section's `variable` declaration (the
-- notation-expanded identifiers elaborate to `sorry` there), so the world
-- binder spells the type out. Direct theorem binders would also work.
variable (tv0 : Type) [BEq tv0] [Inhabited tv0] (e : tv0)
variable (world : Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry)

/-- Transition face: `emit` bumps the current transaction's user-event
    counter (the only field it touches). -/
@[simp] theorem emit_tx_user_events :
    (emit tv0 e world).tx_user_events
      = BoundedNat.add world.tx_user_events (1 : BoundedNat (2^64)) := rfl

/-- FRAME (and honesty face): the cumulative `events` log is untouched --
    the typed payload is not recorded, only counted. -/
@[simp] theorem emit_events :
    (emit tv0 e world).events = world.events := rfl

@[simp] theorem emit_owned :
    (emit tv0 e world).owned = world.owned := rfl
@[simp] theorem emit_shared :
    (emit tv0 e world).shared = world.shared := rfl
@[simp] theorem emit_frozen :
    (emit tv0 e world).frozen = world.frozen := rfl
@[simp] theorem emit_deleted :
    (emit tv0 e world).deleted = world.deleted := rfl
@[simp] theorem emit_received :
    (emit tv0 e world).received = world.received := rfl
@[simp] theorem emit_gas_used :
    (emit tv0 e world).gas_used = world.gas_used := rfl
@[simp] theorem emit_bag_entries :
    (emit tv0 e world).bag_entries = world.bag_entries := rfl
@[simp] theorem emit_df_entries :
    (emit tv0 e world).df_entries = world.df_entries := rfl
@[simp] theorem emit_df_bag_entries :
    (emit tv0 e world).df_bag_entries = world.df_bag_entries := rfl
@[simp] theorem emit_tx_created :
    (emit tv0 e world).tx_created = world.tx_created := rfl
@[simp] theorem emit_allocated_ids :
    (emit tv0 e world).allocated_ids = world.allocated_ids := rfl
@[simp] theorem emit_accumulator :
    (emit tv0 e world).accumulator = world.accumulator := rfl

/-- Head bridge to the World-level op (citation-only). -/
theorem emit_eq_bump_user_events :
    emit tv0 e world = Prover.World.World.bump_user_events world := rfl

variable (tv1 : Type) [BEq tv1] [Inhabited tv1]
variable (addr stream_id : Address) (ev : tv1)

/-- Transition face: `emit_authenticated_impl` bumps the same counter. -/
@[simp] theorem emit_authenticated_impl_tx_user_events :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).tx_user_events
      = BoundedNat.add world.tx_user_events (1 : BoundedNat (2^64)) := rfl

/-- FRAME (and honesty face): the cumulative `events` log is untouched. -/
@[simp] theorem emit_authenticated_impl_events :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).events
      = world.events := rfl

@[simp] theorem emit_authenticated_impl_owned :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).owned = world.owned := rfl
@[simp] theorem emit_authenticated_impl_shared :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).shared = world.shared := rfl
@[simp] theorem emit_authenticated_impl_frozen :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).frozen = world.frozen := rfl
@[simp] theorem emit_authenticated_impl_deleted :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).deleted = world.deleted := rfl
@[simp] theorem emit_authenticated_impl_received :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).received = world.received := rfl
@[simp] theorem emit_authenticated_impl_gas_used :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).gas_used = world.gas_used := rfl
@[simp] theorem emit_authenticated_impl_bag_entries :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).bag_entries = world.bag_entries := rfl
@[simp] theorem emit_authenticated_impl_df_entries :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).df_entries = world.df_entries := rfl
@[simp] theorem emit_authenticated_impl_df_bag_entries :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).df_bag_entries = world.df_bag_entries := rfl
@[simp] theorem emit_authenticated_impl_tx_created :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).tx_created = world.tx_created := rfl
@[simp] theorem emit_authenticated_impl_allocated_ids :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).allocated_ids = world.allocated_ids := rfl
@[simp] theorem emit_authenticated_impl_accumulator :
    (emit_authenticated_impl tv0 tv1 addr stream_id ev world).accumulator = world.accumulator := rfl

theorem emit_authenticated_impl_eq_bump_user_events :
    emit_authenticated_impl tv0 tv1 addr stream_id ev world
      = Prover.World.World.bump_user_events world := rfl

end EmitLemmas

end Event
