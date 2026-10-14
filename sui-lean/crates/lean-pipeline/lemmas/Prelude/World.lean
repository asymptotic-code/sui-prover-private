-- World prelude for Move's implicit side-effect state.
--
-- See `plans/lean-pipeline/stage-04-effects.md` for the design.
-- The prelude is **abstract over `Event` and `Object`** -- the
-- per-package generator emits `AnyEvent` / `AnyObject` inductives
-- that fill the parameters for each translated package via the
-- per-package `Generated/World.lean` file:
--
--   abbrev World := Prover.World.World AnyEvent AnyObject
--
-- Stage 4 of the lean-pipeline (`stage_04_effects`) augments every
-- function classified as needing world (`compute_needs_world`) with
-- a trailing `world : World` parameter and a `(R, World)` return.
-- Call sites get rewritten to thread the world value through each
-- Impure callee. The Lean prelude defines stub semantics; real
-- per-native behavior is in the natives files
-- (`lemmas/natives/Sui/{EventNatives,TransferNatives,ObjectNatives}.lean`).

import Prelude.Helpers
import Prelude.BoundedNat

set_option linter.unusedVariables false

namespace Prover.World

/-- The implicit state threaded through every Impure function.
    Stores observable side effects in flat lists -- v1 prioritises
    structural simplicity over operational efficiency.

    `DfEntry` and `BagEntry` are the two per-project type-erased
    heterogeneous entry types, kept SEPARATE so bag-containing structs
    can be dynamic-field values without an import cycle. The
    renderer-emitted `Generated/World.lean` instantiates
    `DfEntry := Bag.Entry TyCode` (the df universe, carrying df
    keys + values) and `BagEntry := Bag.Entry BagU` (the bag universe,
    carrying the contents of any `Bag`/`ObjectBag`). A struct's `Bag`
    field is typed over `BagU` while the struct itself is a `TyCode`
    (df) value -- `BagU` and `TyCode` live in different files and
    `BagU`'s members never hold bags, so the import graph is a DAG.
    The prelude leaves both abstract so `Prelude.World` itself needs
    neither universe in scope. See
    `plans/lean-pipeline/split-bag-df-universes.md`. -/
structure World (Event : Type) (Object : Type) (DfEntry : Type) (BagEntry : Type) where
  /-- Event log in emit order (append-only). -/
  events      : List Event
  /-- Owned objects: `(owner, object id, object payload)` triples. -/
  owned       : List (Address × Nat × Object)
  /-- Shared objects: `(object id, payload)`. -/
  shared      : List (Nat × Object)
  /-- Frozen objects (immutable): `(object id, payload)`. -/
  frozen      : List (Nat × Object)
  /-- Tombstones for `object::delete`. -/
  deleted     : List Nat
  /-- `(received object id, recipient address)` for `transfer::receive`. -/
  received    : List (Nat × Address)
  /-- Gas counter. Wired lazily; bumped only by gas-charging natives. -/
  gas_used    : Nat
  /-- Heterogeneous bag storage. Keyed by `bag.id`'s low-64 bits
      (`Address` is `BoundedNat (2^256)`; the renderer guarantees
      monotonic UID assignment so 64-bit truncation is unique within
      a single test driver). Newest entries are cons-prepended. -/
  bag_entries : List (Nat × BagEntry)
  /-- Dynamic-field storage for `dynamic_field::*`. Separate slot from
      `bag_entries`. Each element is `(parent uid low-64 bits, typed
      (key, value) pair)`, where the pair is `Bag.Entry` over the
      project `TyCode` df universe (the `DfEntry` parameter). A
      lookup matches BOTH the parent uid AND the key; newest entries
      are cons-prepended so a re-`add`/`set` shadows older values once
      stale ones are `filter`ed out. Stored in `World` -- rather than
      moved onto the owning object struct -- so user `_Types.lean`
      never reference the universe, which dissolves the
      `_Types <-> TyCodeInterp` import cycle. See
      `plans/lean-pipeline/dynamic-fields-in-world.md`. -/
  df_entries : List (Nat × DfEntry)
  /-- Dynamic-field storage for `dynamic_field::*` whose VALUE is a
      `Bag` / `ObjectBag` (e.g. ember's `df<b"supported_assets", Bag>`).
      A `Bag` value is NOT representable in either closed universe
      (it IS a universe's own container), so it cannot ride in
      `df_entries` as a `DfEntry`. Instead store the bag's own `size`
      and `storage` (`List BagEntry` -- the bag's entries, over the
      `BagU` bag universe) keyed by `(parent uid low-64 bits,
      key-entry)`. The key-entry is `Bag.Entry` over the `TyCode` df
      universe (the `DfEntry` parameter) purely for key matching; its
      value slot is unused. See
      `plans/lean-pipeline/split-bag-df-universes.md`. -/
  df_bag_entries : List (Nat × DfEntry × BoundedNat (2^64) × List BagEntry)
  /-- Number of `event::emit` calls observed in the CURRENT
      transaction. Bumped by `event::emit` (and
      `emit_authenticated_impl`); read into
      `test_scenario::TransactionEffects.num_user_events` and reset to
      0 by `test_scenario::end_transaction` (invoked from `next_tx`).
      Sui reports per-transaction user-event counts, so this is reset
      at each tx boundary rather than being cumulative like `events`. -/
  tx_user_events : BoundedNat (2^64)
  /-- Object ids committed (transferred / shared / frozen) in the
      CURRENT transaction, in commit order. Appended by the
      `transfer_to` / `share` / `freeze` helpers; read into
      `test_scenario::TransactionEffects.created` and reset to `[]` by
      `test_scenario::end_transaction` (invoked from `next_tx`).
      Mirrors `tx_user_events`: Sui reports `created` per transaction,
      so this resets at each tx boundary rather than accumulating like
      `owned` / `shared` / `frozen`. Allocation itself is tracked in
      `allocated_ids`; this field records only committed created objects. -/
  tx_created : List Nat
  /-- Object ids allocated by `object::new`. This includes uncommitted
      ids: Sui freshness is an allocation property, not only a transfer /
      share / freeze property. The list persists across transaction
      boundaries. -/
  allocated_ids : List Nat
  /-- Per-accumulator running balances for `funds_accumulator`.
      Association list `(accumulator key address, amount)`; the newest
      write shadows older ones once the stale key is `filter`ed out
      (same cons-prepend + filter discipline as `df_entries`). Deposits
      (`add_impl` / `add_to_accumulator_address`) increment the keyed
      entry; settlements (`redeem` / `withdraw_from_accumulator_address`)
      saturatingly decrement it. Persists across transactions like
      `owned` / `shared` (NOT reset by `end_transaction`). Currently
      write-only bookkeeping -- no function body branches on it yet; it
      exists so a future `.aborts` companion can model the
      insufficient-balance abort that lives inside the
      `withdraw_from_accumulator_address` native (no Move body to derive
      it from). -/
  accumulator : List (Address × BoundedNat (2^256))

/-- A pair result whose `partial_fixpoint` bottom preserves the World from
    the enclosing call. This is definitionally `Result × World`; the
    `FlatOrder` index only supplies the call-specific CCPO bottom. -/
noncomputable abbrev ReadOnlyWorldResult (World Result : Type)
    [Nonempty Result] (world0 : World) :=
  Lean.Order.FlatOrder ((Classical.ofNonempty, world0) : Result × World)

namespace World

variable {Event Object DfEntry BagEntry : Type}

/-- Starting world: every collection empty, gas at 0.
    Test drivers and top-level callers that synthesize a world use this. -/
def init : World Event Object DfEntry BagEntry :=
  { events := [], owned := [], shared := [], frozen := [],
    deleted := [], received := [], gas_used := 0, bag_entries := [],
    df_entries := [], df_bag_entries := [],
    tx_user_events := (0 : BoundedNat (2^64)), tx_created := [],
    allocated_ids := [], accumulator := [] }

/-- Inhabited via `init`. Required by the renderer's `default` fallback
    on `BlockTail::Abort` paths in regular function bodies. The renderer
    emits abort tails as `default` (rather than `sorry`) so the
    .aborts companion's hoisted let-bindings -- which call regular
    function bodies and would crash on `sorry` past their original
    if-guards -- complete without panic. The value at the abort path
    is never observed by the test runner (which gates on `.aborts`).
    See `cetus-stl-stage-d-borrow-mut-handoff.md`. -/
instance : Inhabited (World Event Object DfEntry BagEntry) := ⟨init⟩

/-- Append an event to the log. Used by `event::emit`. -/
def emit_event (w : World Event Object DfEntry BagEntry) (e : Event) : World Event Object DfEntry BagEntry :=
  { w with events := w.events ++ [e] }

/-- Read the current transaction's user-event count. Consumed by
    `test_scenario::end_transaction` to fill
    `TransactionEffects.num_user_events`. -/
def user_event_count (w : World Event Object DfEntry BagEntry) : BoundedNat (2^64) :=
  w.tx_user_events

/-- Increment the current transaction's user-event counter. Used by
    the `event::emit` natives (untyped count; the typed payload is not
    recorded since the generic native cannot inject into `Event`). -/
def bump_user_events (w : World Event Object DfEntry BagEntry) : World Event Object DfEntry BagEntry :=
  { w with tx_user_events := BoundedNat.add w.tx_user_events (1 : BoundedNat (2^64)) }

/-- Reset the current transaction's user-event counter to 0. Used by
    `test_scenario::end_transaction` (invoked from `next_tx`). -/
def reset_user_events (w : World Event Object DfEntry BagEntry) : World Event Object DfEntry BagEntry :=
  { w with tx_user_events := (0 : BoundedNat (2^64)) }

/-- Read the current transaction's committed-object ids (in commit
    order). Consumed by `test_scenario::end_transaction` to fill
    `TransactionEffects.created`. -/
def created_ids (w : World Event Object DfEntry BagEntry) : List Nat :=
  w.tx_created

/-- Reset the current transaction's committed-object list to `[]`.
    Used by `test_scenario::end_transaction` (invoked from `next_tx`). -/
def reset_created (w : World Event Object DfEntry BagEntry) : World Event Object DfEntry BagEntry :=
  { w with tx_created := [] }

/-- Append an owned-object record. Used by `transfer::transfer` /
    `public_transfer`. -/
def transfer_to (w : World Event Object DfEntry BagEntry) (id : Nat) (addr : Address) (obj : Object)
    : World Event Object DfEntry BagEntry :=
  { w with owned := w.owned ++ [(addr, id, obj)], tx_created := w.tx_created ++ [id] }

/-- Append a shared-object record. Used by `transfer::share_object` /
    `public_share_object`. -/
def share (w : World Event Object DfEntry BagEntry) (id : Nat) (obj : Object) : World Event Object DfEntry BagEntry :=
  { w with shared := w.shared ++ [(id, obj)], tx_created := w.tx_created ++ [id] }

/-- Append a frozen-object record. Used by `transfer::freeze_object` /
    `public_freeze_object`. -/
def freeze (w : World Event Object DfEntry BagEntry) (id : Nat) (obj : Object) : World Event Object DfEntry BagEntry :=
  { w with frozen := w.frozen ++ [(id, obj)], tx_created := w.tx_created ++ [id] }

/-- Record an `object::delete` tombstone. -/
def delete_object (w : World Event Object DfEntry BagEntry) (id : Nat) : World Event Object DfEntry BagEntry :=
  { w with deleted := w.deleted ++ [id] }

/-- Record a `transfer::receive` consumption. -/
def receive_record (w : World Event Object DfEntry BagEntry) (id : Nat) (parent : Address) : World Event Object DfEntry BagEntry :=
  { w with received := w.received ++ [(id, parent)] }

/-- Current ledger balance for an accumulator key (0 when absent).
    Used by `funds_accumulator` deposit/settlement helpers, and by a
    future `.aborts` companion to gate the insufficient-balance abort. -/
def accum_balance (w : World Event Object DfEntry BagEntry) (addr : Address) : BoundedNat (2^256) :=
  match w.accumulator.find? (fun p => p.fst == addr) with
  | some p => p.snd
  | none => (0 : BoundedNat (2^256))

/-- Deposit: add `v` to the keyed accumulator balance and reinstate the
    entry at the head (`BoundedNat.add` is wrapping, never fires for
    realistic amounts). -/
def accum_add (w : World Event Object DfEntry BagEntry) (addr : Address) (v : BoundedNat (2^256))
    : World Event Object DfEntry BagEntry :=
  { w with accumulator :=
      (addr, BoundedNat.add (accum_balance w addr) v) :: w.accumulator.filter (fun p => p.fst != addr) }

/-- Settlement: saturatingly subtract `v` from the keyed accumulator
    balance (`BoundedNat.sub` truncates at 0) and reinstate the entry at
    the head. -/
def accum_sub (w : World Event Object DfEntry BagEntry) (addr : Address) (v : BoundedNat (2^256))
    : World Event Object DfEntry BagEntry :=
  { w with accumulator :=
      (addr, BoundedNat.sub (accum_balance w addr) v) :: w.accumulator.filter (fun p => p.fst != addr) }

/-- All object-ish ids already represented in `World`. This intentionally
    includes dynamic-field and bag storage parent ids, not only committed
    owned/shared/frozen objects: a freshly allocated object must not already
    have storage hanging off its uid. -/
def id_list (w : World Event Object DfEntry BagEntry) : List Nat :=
  w.owned.map (fun e => e.2.1) ++
  w.shared.map (fun e => e.1) ++
  w.frozen.map (fun e => e.1) ++
  w.deleted ++
  w.received.map (fun e => e.1) ++
  w.tx_created ++
  w.allocated_ids ++
  w.bag_entries.map (fun e => e.1) ++
  w.df_entries.map (fun e => e.1) ++
  w.df_bag_entries.map (fun e => e.1)

/-- Boolean membership test for an object-ish id already represented in
    `World`. -/
def contains_id (w : World Event Object DfEntry BagEntry) (id : Nat) : Bool :=
  (id_list w).any (fun e => e == id)

def max_id_list : List Nat → Nat
  | [] => 0
  | x :: xs => max x (max_id_list xs)

def max_id (w : World Event Object DfEntry BagEntry) : Nat :=
  max_id_list (id_list w)

def fresh_id (w : World Event Object DfEntry BagEntry) : Nat :=
  max_id w + 1

theorem le_max_id_list_of_mem {id : Nat} :
    ∀ {ids : List Nat}, id ∈ ids → id ≤ max_id_list ids
  | [], h => by cases h
  | x :: xs, h => by
      simp [max_id_list] at h ⊢
      cases h with
      | inl h_eq =>
          subst id
          exact Nat.le_max_left x (max_id_list xs)
      | inr h_mem =>
          exact Nat.le_trans (le_max_id_list_of_mem h_mem)
            (Nat.le_max_right x (max_id_list xs))

theorem fresh_id_not_mem_id_list (w : World Event Object DfEntry BagEntry) :
    fresh_id w ∉ id_list w := by
  intro h
  have hle := le_max_id_list_of_mem (id := fresh_id w) h
  simp [fresh_id, max_id] at hle
  omega

@[simp] theorem contains_id_fresh_id_eq_false
    (w : World Event Object DfEntry BagEntry) :
    contains_id w (fresh_id w) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  rw [contains_id] at h
  rcases (List.any_eq_true.mp h) with ⟨id, hmem, hid⟩
  have heq : id = fresh_id w := beq_iff_eq.mp hid
  exact fresh_id_not_mem_id_list w (by simpa [heq] using hmem)

/-- Drop any state keyed by `id`. This is available to model explicit removal
    operations, but `object::new` does not use it: a new object id is fresh for
    reachable Sui worlds, so allocation should not mutate unrelated stores. -/
def clear_id (w : World Event Object DfEntry BagEntry) (id : Nat) : World Event Object DfEntry BagEntry :=
  { w with
    owned := w.owned.filter (fun e => e.2.1 != id),
    shared := w.shared.filter (fun e => e.1 != id),
    frozen := w.frozen.filter (fun e => e.1 != id),
    deleted := w.deleted.filter (fun e => e != id),
    received := w.received.filter (fun e => e.1 != id),
    tx_created := w.tx_created.filter (fun e => e != id),
    allocated_ids := w.allocated_ids.filter (fun e => e != id),
    bag_entries := w.bag_entries.filter (fun e => e.1 != id),
    df_entries := w.df_entries.filter (fun e => e.1 != id),
    df_bag_entries := w.df_bag_entries.filter (fun e => e.1 != id) }

/-- Reserve a freshly-created object id. Freshness is exposed separately via
    `validForNewId`; allocation records the id without changing object or
    dynamic-field storage. -/
def allocate_id (w : World Event Object DfEntry BagEntry) (id : Nat) : World Event Object DfEntry BagEntry :=
  { w with allocated_ids := id :: w.allocated_ids }

/-- Allocation-frame pack (1/6): allocation does not touch dynamic-field
    storage. Every world-threading allocator (`object::new` and the four
    container constructors built on it) bottoms out here, so this is the
    root fact that lets a `dynamic_field` obligation see through an
    arbitrarily deep allocation chain. `@[simp]` because it is a pure
    frame rewrite toward the smaller term and can never loop.

    The retired `Sui/WorldFrameLemmas.lean` island stated the same fact per
    world field, but that module was imported by nobody (importing it from
    the always-import list would cycle: it imported the Sui natives that
    would import it). Its whole battery now lives here and beside the
    definitions it framed, where every generated module already has it in
    scope. -/
@[simp] theorem allocate_id_df_entries (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).df_entries = w.df_entries := rfl

/-- Bag-store twin of `allocate_id_df_entries`: allocation does not touch
    bag-valued dynamic-field storage either, so `store_bag_*` obligations
    see through an allocation chain the same way plain-df ones do. -/
@[simp] theorem allocate_id_df_bag_entries (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).df_bag_entries = w.df_bag_entries := rfl

/-- Transport face of `allocate_id`: the one field it DOES change, stated
    explicitly. Citation-only (the retired WorldFrameLemmas island's
    `allocate_id_allocated_ids` discipline): the cons on the
    right is not a smaller term, so it stays out of the simp set. -/
theorem allocate_id_allocated_ids (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).allocated_ids = id :: w.allocated_ids := rfl

-- ---------------------------------------------------------------------------
-- Pass 2: world-frame completeness. Every writer in this file gets the frame
-- pair for BOTH dynamic-field stores (the fields every df observer reads),
-- and `allocate_id` -- the allocator every world-threading constructor
-- bottoms out in -- gets its full per-field frame set (every field except
-- the one it writes). All rfl-class one-directional frames, so `@[simp]`
-- per the pack discipline. (The retired `Sui/WorldFrameLemmas.lean` island
-- stated many of these; see the note on `allocate_id_df_entries`.)
-- ---------------------------------------------------------------------------

@[simp] theorem allocate_id_events (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).events = w.events := rfl
@[simp] theorem allocate_id_owned (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).owned = w.owned := rfl
@[simp] theorem allocate_id_shared (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).shared = w.shared := rfl
@[simp] theorem allocate_id_frozen (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).frozen = w.frozen := rfl
@[simp] theorem allocate_id_deleted (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).deleted = w.deleted := rfl
@[simp] theorem allocate_id_received (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).received = w.received := rfl
@[simp] theorem allocate_id_gas_used (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).gas_used = w.gas_used := rfl
@[simp] theorem allocate_id_bag_entries (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).bag_entries = w.bag_entries := rfl
@[simp] theorem allocate_id_tx_user_events (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).tx_user_events = w.tx_user_events := rfl
@[simp] theorem allocate_id_tx_created (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).tx_created = w.tx_created := rfl
@[simp] theorem allocate_id_accumulator (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (allocate_id w id).accumulator = w.accumulator := rfl

@[simp] theorem emit_event_df_entries (w : World Event Object DfEntry BagEntry) (e : Event) :
    (emit_event w e).df_entries = w.df_entries := rfl
@[simp] theorem emit_event_df_bag_entries (w : World Event Object DfEntry BagEntry) (e : Event) :
    (emit_event w e).df_bag_entries = w.df_bag_entries := rfl
@[simp] theorem bump_user_events_df_entries (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).df_entries = w.df_entries := rfl
@[simp] theorem bump_user_events_df_bag_entries (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).df_bag_entries = w.df_bag_entries := rfl
@[simp] theorem reset_user_events_df_entries (w : World Event Object DfEntry BagEntry) :
    (reset_user_events w).df_entries = w.df_entries := rfl
@[simp] theorem reset_user_events_df_bag_entries (w : World Event Object DfEntry BagEntry) :
    (reset_user_events w).df_bag_entries = w.df_bag_entries := rfl
@[simp] theorem reset_created_df_entries (w : World Event Object DfEntry BagEntry) :
    (reset_created w).df_entries = w.df_entries := rfl
@[simp] theorem reset_created_df_bag_entries (w : World Event Object DfEntry BagEntry) :
    (reset_created w).df_bag_entries = w.df_bag_entries := rfl
@[simp] theorem transfer_to_df_entries (w : World Event Object DfEntry BagEntry)
    (id : Nat) (addr : Address) (obj : Object) :
    (transfer_to w id addr obj).df_entries = w.df_entries := rfl
@[simp] theorem transfer_to_df_bag_entries (w : World Event Object DfEntry BagEntry)
    (id : Nat) (addr : Address) (obj : Object) :
    (transfer_to w id addr obj).df_bag_entries = w.df_bag_entries := rfl
@[simp] theorem share_df_entries (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (share w id obj).df_entries = w.df_entries := rfl
@[simp] theorem share_df_bag_entries (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (share w id obj).df_bag_entries = w.df_bag_entries := rfl
@[simp] theorem freeze_df_entries (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (freeze w id obj).df_entries = w.df_entries := rfl
@[simp] theorem freeze_df_bag_entries (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (freeze w id obj).df_bag_entries = w.df_bag_entries := rfl
@[simp] theorem delete_object_df_entries (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (delete_object w id).df_entries = w.df_entries := rfl
@[simp] theorem delete_object_df_bag_entries (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (delete_object w id).df_bag_entries = w.df_bag_entries := rfl
@[simp] theorem receive_record_df_entries (w : World Event Object DfEntry BagEntry)
    (id : Nat) (parent : Address) :
    (receive_record w id parent).df_entries = w.df_entries := rfl
@[simp] theorem receive_record_df_bag_entries (w : World Event Object DfEntry BagEntry)
    (id : Nat) (parent : Address) :
    (receive_record w id parent).df_bag_entries = w.df_bag_entries := rfl
@[simp] theorem accum_add_df_entries (w : World Event Object DfEntry BagEntry)
    (addr : Address) (v : BoundedNat (2^256)) :
    (accum_add w addr v).df_entries = w.df_entries := rfl
@[simp] theorem accum_add_df_bag_entries (w : World Event Object DfEntry BagEntry)
    (addr : Address) (v : BoundedNat (2^256)) :
    (accum_add w addr v).df_bag_entries = w.df_bag_entries := rfl
@[simp] theorem accum_sub_df_entries (w : World Event Object DfEntry BagEntry)
    (addr : Address) (v : BoundedNat (2^256)) :
    (accum_sub w addr v).df_entries = w.df_entries := rfl
@[simp] theorem accum_sub_df_bag_entries (w : World Event Object DfEntry BagEntry)
    (addr : Address) (v : BoundedNat (2^256)) :
    (accum_sub w addr v).df_bag_entries = w.df_bag_entries := rfl

-- ---------------------------------------------------------------------------
-- Full per-field frames for the ownership writers and the event counter --
-- the four World ops every transfer/share/freeze/emit native bottoms out in
-- (the world-writers wave states its frames at the NATIVE heads; these are
-- the World-level twins its per-op lists factor through, and they subsume
-- the retired `Sui/WorldFrameLemmas.lean` `bump_user_events_*` battery).
-- `transfer_to`/`share`/`freeze` each write their own store plus
-- `tx_created`; `bump_user_events` writes only `tx_user_events`.
-- ---------------------------------------------------------------------------

@[simp] theorem transfer_to_events (w : World Event Object DfEntry BagEntry)
    (id : Nat) (addr : Address) (obj : Object) :
    (transfer_to w id addr obj).events = w.events := rfl
@[simp] theorem transfer_to_shared (w : World Event Object DfEntry BagEntry)
    (id : Nat) (addr : Address) (obj : Object) :
    (transfer_to w id addr obj).shared = w.shared := rfl
@[simp] theorem transfer_to_frozen (w : World Event Object DfEntry BagEntry)
    (id : Nat) (addr : Address) (obj : Object) :
    (transfer_to w id addr obj).frozen = w.frozen := rfl
@[simp] theorem transfer_to_deleted (w : World Event Object DfEntry BagEntry)
    (id : Nat) (addr : Address) (obj : Object) :
    (transfer_to w id addr obj).deleted = w.deleted := rfl
@[simp] theorem transfer_to_received (w : World Event Object DfEntry BagEntry)
    (id : Nat) (addr : Address) (obj : Object) :
    (transfer_to w id addr obj).received = w.received := rfl
@[simp] theorem transfer_to_gas_used (w : World Event Object DfEntry BagEntry)
    (id : Nat) (addr : Address) (obj : Object) :
    (transfer_to w id addr obj).gas_used = w.gas_used := rfl
@[simp] theorem transfer_to_bag_entries (w : World Event Object DfEntry BagEntry)
    (id : Nat) (addr : Address) (obj : Object) :
    (transfer_to w id addr obj).bag_entries = w.bag_entries := rfl
@[simp] theorem transfer_to_tx_user_events (w : World Event Object DfEntry BagEntry)
    (id : Nat) (addr : Address) (obj : Object) :
    (transfer_to w id addr obj).tx_user_events = w.tx_user_events := rfl
@[simp] theorem transfer_to_allocated_ids (w : World Event Object DfEntry BagEntry)
    (id : Nat) (addr : Address) (obj : Object) :
    (transfer_to w id addr obj).allocated_ids = w.allocated_ids := rfl
@[simp] theorem transfer_to_accumulator (w : World Event Object DfEntry BagEntry)
    (id : Nat) (addr : Address) (obj : Object) :
    (transfer_to w id addr obj).accumulator = w.accumulator := rfl

@[simp] theorem share_events (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (share w id obj).events = w.events := rfl
@[simp] theorem share_owned (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (share w id obj).owned = w.owned := rfl
@[simp] theorem share_frozen (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (share w id obj).frozen = w.frozen := rfl
@[simp] theorem share_deleted (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (share w id obj).deleted = w.deleted := rfl
@[simp] theorem share_received (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (share w id obj).received = w.received := rfl
@[simp] theorem share_gas_used (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (share w id obj).gas_used = w.gas_used := rfl
@[simp] theorem share_bag_entries (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (share w id obj).bag_entries = w.bag_entries := rfl
@[simp] theorem share_tx_user_events (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (share w id obj).tx_user_events = w.tx_user_events := rfl
@[simp] theorem share_allocated_ids (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (share w id obj).allocated_ids = w.allocated_ids := rfl
@[simp] theorem share_accumulator (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (share w id obj).accumulator = w.accumulator := rfl

@[simp] theorem freeze_events (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (freeze w id obj).events = w.events := rfl
@[simp] theorem freeze_owned (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (freeze w id obj).owned = w.owned := rfl
@[simp] theorem freeze_shared (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (freeze w id obj).shared = w.shared := rfl
@[simp] theorem freeze_deleted (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (freeze w id obj).deleted = w.deleted := rfl
@[simp] theorem freeze_received (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (freeze w id obj).received = w.received := rfl
@[simp] theorem freeze_gas_used (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (freeze w id obj).gas_used = w.gas_used := rfl
@[simp] theorem freeze_bag_entries (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (freeze w id obj).bag_entries = w.bag_entries := rfl
@[simp] theorem freeze_tx_user_events (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (freeze w id obj).tx_user_events = w.tx_user_events := rfl
@[simp] theorem freeze_allocated_ids (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (freeze w id obj).allocated_ids = w.allocated_ids := rfl
@[simp] theorem freeze_accumulator (w : World Event Object DfEntry BagEntry)
    (id : Nat) (obj : Object) :
    (freeze w id obj).accumulator = w.accumulator := rfl

@[simp] theorem bump_user_events_events (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).events = w.events := rfl
@[simp] theorem bump_user_events_owned (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).owned = w.owned := rfl
@[simp] theorem bump_user_events_shared (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).shared = w.shared := rfl
@[simp] theorem bump_user_events_frozen (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).frozen = w.frozen := rfl
@[simp] theorem bump_user_events_deleted (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).deleted = w.deleted := rfl
@[simp] theorem bump_user_events_received (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).received = w.received := rfl
@[simp] theorem bump_user_events_gas_used (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).gas_used = w.gas_used := rfl
@[simp] theorem bump_user_events_bag_entries (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).bag_entries = w.bag_entries := rfl
@[simp] theorem bump_user_events_tx_created (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).tx_created = w.tx_created := rfl
@[simp] theorem bump_user_events_allocated_ids (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).allocated_ids = w.allocated_ids := rfl
@[simp] theorem bump_user_events_accumulator (w : World Event Object DfEntry BagEntry) :
    (bump_user_events w).accumulator = w.accumulator := rfl

-- `clear_id` filters both df stores (it IS a df writer); its frames are the
-- four fields it leaves untouched.
@[simp] theorem clear_id_events (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (clear_id w id).events = w.events := rfl
@[simp] theorem clear_id_gas_used (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (clear_id w id).gas_used = w.gas_used := rfl
@[simp] theorem clear_id_tx_user_events (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (clear_id w id).tx_user_events = w.tx_user_events := rfl
@[simp] theorem clear_id_accumulator (w : World Event Object DfEntry BagEntry) (id : Nat) :
    (clear_id w id).accumulator = w.accumulator := rfl

/-- Freshness side condition for an object id produced by the current
    transaction. `object::new` records the allocation in `allocated_ids`; this
    predicate is available for proofs that need to talk about pre-allocation
    freshness. -/
def validForNewId (id : Nat) (w : World Event Object DfEntry BagEntry) : Bool :=
  ! contains_id w id

@[simp] theorem validForNewId_allocate_id_self_eq_false
    (w : World Event Object DfEntry BagEntry) (id : Nat) :
    validForNewId id (allocate_id w id) = false := by
  simp [validForNewId, contains_id, id_list, allocate_id]

@[simp] theorem validForNewId_fresh_id_eq_true
    (w : World Event Object DfEntry BagEntry) :
    validForNewId (fresh_id w) w = true := by
  simp [validForNewId]

end World

end Prover.World
