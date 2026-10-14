-- Native implementations for sui::object_table.
--
-- Move source: `public struct ObjectTable<phantom K, phantom V> has
-- key, store { id: UID, size: u64 }`. The Move-level value constraint
-- `V: key + store` (values must be Sui objects) isn't carried at the
-- Lean level. Storage is modelled exactly like `TableNatives.lean`:
-- a ghost `dynamic_fields : List (K x V)` field that the natives
-- read/write directly. This lets `borrow_mut(t, k); *v = new` actually
-- update the table state via the renderer's writeback chain
-- (writeBackMapKey + Object_table.set), instead of dropping the
-- mutation on the floor.
--
-- Per natives.rs purity, ordinary mutators are PurePartial; `new`
-- threads world because it allocates an object UID. Reads/queries are PureTotal. Stage 3 mut-to-let
-- rewrites &mut params to value-form let-rebinds. The natives below
-- take and return value-form `ObjectTable K V`; callers strip `.val`
-- from the surrounding `Mutation` per the renderer's
-- `callee_is_native` auto-unwrap.

import Prelude.BoundedNat
import Prelude.Helpers
import MoveStdlib.MoveVectorNatives
import Sui.ObjectNatives
import Sui.Tx_contextNatives

namespace Object_table

-- The Move struct only carries `id` + `size`; `dynamic_fields` is a
-- ghost field added so the natives have a place to store the (K, V)
-- associations. Same shape as `Table.Table`.
structure ObjectTable (tv0 : Type) (tv1 : Type) where
  id : Object.UID
  size : BoundedNat (2^64)
  dynamic_fields : List (tv0 × tv1)
deriving DecidableEq
instance [Inhabited tv0] [Inhabited tv1] : Inhabited (ObjectTable tv0 tv1) where default := ⟨default, default, default⟩

/-- `object_table::new<K, V>(ctx: &mut TxContext): ObjectTable<K, V>`.
Stage 3 augments the `&mut TxContext` return slot and stage 4 threads
the allocation world. -/
def new {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V] (ctx : Tx_context.TxContext)
    (world : Prover.World.World Ev Ob Df Be) :
    ObjectTable K V × Tx_context.TxContext × Prover.World.World Ev Ob Df Be :=
  let created := Object.new ctx world
  (⟨created.1, (0 : BoundedNat (2^64)), []⟩, created.2.1, created.2.2)

/-- Allocation-frame pack (5/6): `object_table::new` delegates its UID
    allocation to `object::new`, so dynamic-field storage survives the
    hop. Same statement and same one-line proof as
    `Table.new_world_df_entries`; shipped together so the next client to
    hit an `ObjectTable` allocation chain does not hand-roll a variant. -/
@[simp] theorem new_world_df_entries {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    ((new K V ctx world).2.2).df_entries = world.df_entries := rfl

/-- Bag-store twin of `new_world_df_entries` (see
    `Table.new_world_df_bag_entries`). -/
@[simp] theorem new_world_df_bag_entries {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    ((new K V ctx world).2.2).df_bag_entries = world.df_bag_entries := rfl

/-- Pass 2: see `Table.new_world` / `Table.new_ctx`. -/
@[simp] theorem new_world {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (new K V ctx world).2.2 = (Object.new ctx world).2.2 := rfl

@[simp] theorem new_ctx {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (new K V ctx world).2.1 = (Object.new ctx world).2.1 := rfl

/-- `object_table::add<K, V>(t: &mut ObjectTable<K, V>, k: K, v: V)`.
Move return is `()`; stage 3 augments to return the new ObjectTable. -/
def add (K V : Type) [BEq K] [Inhabited V]
    (t : ObjectTable K V) (k : K) (v : V) : ObjectTable K V :=
  { t with size := BoundedNat.add t.size (1 : BoundedNat (2^64)),
           dynamic_fields := t.dynamic_fields ++ [(k, v)] }

/-- `object_table::borrow<K, V>(t: &ObjectTable<K, V>, k: K): &V`. Immutable
borrow: no Mutation involved, just a value lookup. Aborts in Move
when the key is missing; here we fall back to `default` so non-aborting
test bodies evaluate without `sorry`. -/
def borrow (K V : Type) [BEq K] [Inhabited V] (t : ObjectTable K V) (k : K) : V :=
  match t.dynamic_fields.find? (fun kv => kv.1 == k) with
  | some kv => kv.2
  | none    => default

/-- `object_table::borrow_mut<K, V>(t: &mut ObjectTable<K, V>, k: K): &mut V`.
Stage 3 augments: returns `(V, ObjectTable K V)`. -/
def borrow_mut (K V : Type) [BEq K] [Inhabited V]
    (t : ObjectTable K V) (k : K) : (V × ObjectTable K V) :=
  match t.dynamic_fields.find? (fun kv => kv.1 == k) with
  | some kv => (kv.2, t)
  | none    => (default, t)

/-- `object_table::remove<K, V>(t: &mut ObjectTable<K, V>, k: K): V`.
Stage 3 augments: returns `(V, ObjectTable K V)`. -/
def remove (K V : Type) [BEq K] [Inhabited V]
    (t : ObjectTable K V) (k : K) : (V × ObjectTable K V) :=
  match t.dynamic_fields.find? (fun kv => kv.1 == k) with
  | some kv =>
    (kv.2,
     { t with size := BoundedNat.sub t.size (1 : BoundedNat (2^64)),
              dynamic_fields := t.dynamic_fields.filter (fun e => !(e.1 == k)) })
  | none    => (default, t)

/-- `object_table::contains<K, V>(t: &ObjectTable<K, V>, k: K): bool`. -/
def contains (K V : Type) [BEq K] [Inhabited V] (t : ObjectTable K V) (k : K) : Bool :=
  (t.dynamic_fields.find? (fun kv => kv.1 == k)).isSome

/-- `object_table::length<K, V>(t: &ObjectTable<K, V>): u64`. DERIVED
from the map (one source of truth; the tracked `size` stays maintained
but unread) -- see container-df-unification.md "size/contains". -/
def length (K V : Type) [BEq K] [Inhabited V] (t : ObjectTable K V) : BoundedNat (2^64) :=
  ⟨t.dynamic_fields.length % (2^64), Nat.mod_lt _ (by decide)⟩

/-- `object_table::is_empty<K, V>(t: &ObjectTable<K, V>): bool`. Derived. -/
def is_empty (K V : Type) [BEq K] [Inhabited V] (t : ObjectTable K V) : Bool :=
  t.dynamic_fields.isEmpty

/-- `object_table::destroy_empty<K, V>(t: ObjectTable<K, V>)`. Aborts iff
non-empty; the stub consumes by value and returns `()`. -/
def destroy_empty (K V : Type) [BEq K] [Inhabited V] (_t : ObjectTable K V) : Unit := ()

/-- `object_table::value_id<K, V>(t: &ObjectTable<K, V>, k: K): Option<ID>`.
Stub: returns the type default; modelling the real id mapping requires
plumbing Object.UID per stored value which we don't currently track. -/
def value_id (K V : Type) [BEq K] [Inhabited V] (_t : ObjectTable K V) (_k : K) : Object.ID :=
  default

/-- **NOT a Move source function** -- a writeback primitive added so
the new-pipeline renderer can express `*object_table::borrow_mut(t, k) = v`
without peeking into `ObjectTable`'s internal `dynamic_fields`
representation. Replaces the value at `k` with `v`; size unchanged
(this is an update, not an add). Idempotent / no-op when `k` is
missing -- in that case Move's preceding `borrow_mut` would have
aborted before this set fires, so the no-op branch is unreachable
along `AbortResult.NoAbort` paths. Mirrors `Table.set`. -/
def set (K V : Type) [BEq K] [Inhabited V] (t : ObjectTable K V) (k : K) (v : V) : ObjectTable K V :=
  let new_fields := t.dynamic_fields.map (fun kv => if kv.1 == k then (kv.1, v) else kv)
  { t with dynamic_fields := new_fields }

-- ---------------------------------------------------------------------------
-- `.aborts` companions for the partial ObjectTable operations.
--
-- Same pattern as `TableNatives.lean`: precise companions follow
-- Move semantics so stage 7's spec_extract doesn't default the abort
-- predicate to `Bool(true)` for every transitive caller.
--
-- Aborts conditions:
--   - `borrow` / `borrow_mut` / `remove` / `value_id` -- abort iff key is missing.
--   - `add` -- abort iff key is already present.
--   - `destroy_empty` -- abort iff the table is non-empty.
--   - `new` / `contains` / `length` / `is_empty` -- total.
def new.aborts {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V] (_ctx : Tx_context.TxContext)
    (_world : Prover.World.World Ev Ob Df Be) : Bool := false
def add.aborts (K V : Type) [BEq K] [Inhabited V] (t : ObjectTable K V) (k : K) (_v : V) : Bool :=
  (t.dynamic_fields.find? (fun kv => kv.1 == k)).isSome
def borrow.aborts (K V : Type) [BEq K] [Inhabited V] (t : ObjectTable K V) (k : K) : Bool :=
  (t.dynamic_fields.find? (fun kv => kv.1 == k)).isNone
def borrow_mut.aborts (K V : Type) [BEq K] [Inhabited V] (t : ObjectTable K V) (k : K) : Bool :=
  (t.dynamic_fields.find? (fun kv => kv.1 == k)).isNone
def remove.aborts (K V : Type) [BEq K] [Inhabited V] (t : ObjectTable K V) (k : K) : Bool :=
  (t.dynamic_fields.find? (fun kv => kv.1 == k)).isNone
def contains.aborts (K V : Type) [BEq K] [Inhabited V] (_t : ObjectTable K V) (_k : K) : Bool := false
def length.aborts (K V : Type) [BEq K] [Inhabited V] (_t : ObjectTable K V) : Bool := false
def is_empty.aborts (K V : Type) [BEq K] [Inhabited V] (_t : ObjectTable K V) : Bool := false
def destroy_empty.aborts (K V : Type) [BEq K] [Inhabited V] (t : ObjectTable K V) : Bool :=
  -- Read `dynamic_fields` (the single source of truth, matching `is_empty`),
  -- not the maintained-but-unread `size` field which no invariant ties to it.
  !t.dynamic_fields.isEmpty
def value_id.aborts (K V : Type) [BEq K] [Inhabited V] (t : ObjectTable K V) (k : K) : Bool :=
  (t.dynamic_fields.find? (fun kv => kv.1 == k)).isNone

/-- Spec-only total helpers (see natives.rs). Same shapes as their
non-`_pure` / `_or_unknown` counterparts, but classified PureTotal
so the prover knows they never abort. -/
def borrow_or_unknown (K V : Type) [BEq K] [Inhabited V] (t : ObjectTable K V) (k : K) : V :=
  borrow K V t k

def borrow_or_unknown.aborts (K V : Type) [BEq K] [Inhabited V]
    (_t : ObjectTable K V) (_k : K) : Bool := false

def add_pure (K V : Type) [BEq K] [Inhabited V]
    (t : ObjectTable K V) (k : K) (v : V) : ObjectTable K V :=
  add K V t k v

def add_pure.aborts (K V : Type) [BEq K] [Inhabited V]
    (_t : ObjectTable K V) (_k : K) (_v : V) : Bool := false

def remove_pure (K V : Type) [BEq K] [Inhabited V]
    (t : ObjectTable K V) (k : K) : (V × ObjectTable K V) :=
  remove K V t k

def remove_pure.aborts (K V : Type) [BEq K] [Inhabited V]
    (_t : ObjectTable K V) (_k : K) : Bool := false

end Object_table

-- ---------------------------------------------------------------------------
-- Observer x writer matrix for ObjectTable, mirroring `TableNatives.lean`
-- (the storage model is identical: a ghost `dynamic_fields : List (K x V)`).
-- Attribute discipline: `@[simp]` only on rfl-class / unconditional
-- one-directional frames (the `BagNatives` bridge style -- this file carries
-- no `move_effect` precedent); conditional and if-carrying lemmas are
-- citation-only.
-- ---------------------------------------------------------------------------

-- Abort-face bridges.

@[simp] theorem object_table_add_aborts_eq_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) (value : V) :
    _root_.Object_table.add.aborts K V table key value =
      _root_.Object_table.contains K V table key := rfl

@[simp] theorem object_table_borrow_aborts_eq_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    _root_.Object_table.borrow.aborts K V table key =
      !_root_.Object_table.contains K V table key := by
  unfold _root_.Object_table.borrow.aborts _root_.Object_table.contains
  cases List.find? (fun kv => kv.1 == key) table.dynamic_fields <;> rfl

@[simp] theorem object_table_borrow_mut_aborts_eq_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    _root_.Object_table.borrow_mut.aborts K V table key =
      !_root_.Object_table.contains K V table key := by
  unfold _root_.Object_table.borrow_mut.aborts _root_.Object_table.contains
  cases List.find? (fun kv => kv.1 == key) table.dynamic_fields <;> rfl

@[simp] theorem object_table_remove_aborts_eq_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    _root_.Object_table.remove.aborts K V table key =
      !_root_.Object_table.contains K V table key := by
  unfold _root_.Object_table.remove.aborts _root_.Object_table.contains
  cases List.find? (fun kv => kv.1 == key) table.dynamic_fields <;> rfl

@[simp] theorem object_table_value_id_aborts_eq_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    _root_.Object_table.value_id.aborts K V table key =
      !_root_.Object_table.contains K V table key := by
  unfold _root_.Object_table.value_id.aborts _root_.Object_table.contains
  cases List.find? (fun kv => kv.1 == key) table.dynamic_fields <;> rfl

@[simp] theorem object_table_destroy_empty_aborts_eq_not_is_empty
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) :
    _root_.Object_table.destroy_empty.aborts K V table =
      !_root_.Object_table.is_empty K V table := rfl

-- Total faces.

@[simp] theorem object_table_new_aborts_eq_false
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    _root_.Object_table.new.aborts K V ctx world = false := rfl

@[simp] theorem object_table_contains_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    _root_.Object_table.contains.aborts K V table key = false := rfl

@[simp] theorem object_table_length_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) :
    _root_.Object_table.length.aborts K V table = false := rfl

@[simp] theorem object_table_is_empty_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) :
    _root_.Object_table.is_empty.aborts K V table = false := rfl

@[simp] theorem object_table_borrow_or_unknown_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    _root_.Object_table.borrow_or_unknown.aborts K V table key = false := rfl

@[simp] theorem object_table_add_pure_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) (value : V) :
    _root_.Object_table.add_pure.aborts K V table key value = false := rfl

@[simp] theorem object_table_remove_pure_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    _root_.Object_table.remove_pure.aborts K V table key = false := rfl

-- No-abort corollaries (citation-only; conditional).

theorem object_table_borrow_no_abort_of_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K)
    (h_contains : _root_.Object_table.contains K V table key = true) :
    _root_.Object_table.borrow.aborts K V table key = false := by
  simp only [object_table_borrow_aborts_eq_not_contains, h_contains, Bool.not_true]

theorem object_table_borrow_mut_no_abort_of_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K)
    (h_contains : _root_.Object_table.contains K V table key = true) :
    _root_.Object_table.borrow_mut.aborts K V table key = false := by
  simp only [object_table_borrow_mut_aborts_eq_not_contains, h_contains, Bool.not_true]

theorem object_table_remove_no_abort_of_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K)
    (h_contains : _root_.Object_table.contains K V table key = true) :
    _root_.Object_table.remove.aborts K V table key = false := by
  simp only [object_table_remove_aborts_eq_not_contains, h_contains, Bool.not_true]

theorem object_table_add_no_abort_of_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) (value : V)
    (h_not_contains : _root_.Object_table.contains K V table key = false) :
    _root_.Object_table.add.aborts K V table key value = false := by
  simp only [object_table_add_aborts_eq_contains, h_not_contains]

-- Spec-alias transports (the `_pure` / `_or_unknown` faces ARE the base ops).

@[simp] theorem object_table_borrow_or_unknown_eq_borrow
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    _root_.Object_table.borrow_or_unknown K V table key =
      _root_.Object_table.borrow K V table key := rfl

@[simp] theorem object_table_add_pure_eq_add
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) (value : V) :
    _root_.Object_table.add_pure K V table key value =
      _root_.Object_table.add K V table key value := rfl

@[simp] theorem object_table_remove_pure_eq_remove
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    _root_.Object_table.remove_pure K V table key =
      _root_.Object_table.remove K V table key := rfl

-- Constructor faces.

@[simp] theorem object_table_contains_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (key : K) :
    _root_.Object_table.contains K V (_root_.Object_table.new K V ctx world).1 key =
      false := rfl

@[simp] theorem object_table_borrow_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (key : K) :
    _root_.Object_table.borrow K V (_root_.Object_table.new K V ctx world).1 key =
      default := rfl

@[simp] theorem object_table_length_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    _root_.Object_table.length K V (_root_.Object_table.new K V ctx world).1 =
      (0 : BoundedNat (2^64)) := rfl

@[simp] theorem object_table_is_empty_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    _root_.Object_table.is_empty K V (_root_.Object_table.new K V ctx world).1 =
      true := rfl

@[simp] theorem object_table_add_aborts_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be)
    (key : K) (value : V) :
    _root_.Object_table.add.aborts K V (_root_.Object_table.new K V ctx world).1
      key value = false := rfl

@[simp] theorem object_table_borrow_aborts_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (key : K) :
    _root_.Object_table.borrow.aborts K V
      (_root_.Object_table.new K V ctx world).1 key = true := rfl

@[simp] theorem object_table_borrow_mut_aborts_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (key : K) :
    _root_.Object_table.borrow_mut.aborts K V
      (_root_.Object_table.new K V ctx world).1 key = true := rfl

@[simp] theorem object_table_remove_aborts_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (key : K) :
    _root_.Object_table.remove.aborts K V
      (_root_.Object_table.new K V ctx world).1 key = true := rfl

@[simp] theorem object_table_value_id_aborts_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (key : K) :
    _root_.Object_table.value_id.aborts K V
      (_root_.Object_table.new K V ctx world).1 key = true := rfl

@[simp] theorem object_table_destroy_empty_aborts_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    _root_.Object_table.destroy_empty.aborts K V
      (_root_.Object_table.new K V ctx world).1 = false := rfl

-- `borrow_mut` transports.

@[simp] theorem object_table_borrow_mut_fst_eq_borrow
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    (_root_.Object_table.borrow_mut K V table key).1 =
      _root_.Object_table.borrow K V table key := by
  unfold _root_.Object_table.borrow_mut _root_.Object_table.borrow
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields <;>
    simp

@[simp] theorem object_table_borrow_mut_snd
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    (_root_.Object_table.borrow_mut K V table key).2 = table := by
  unfold _root_.Object_table.borrow_mut
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields <;>
    simp

@[simp] theorem object_table_remove_fst_eq_borrow
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    (_root_.Object_table.remove K V table key).1 =
      _root_.Object_table.borrow K V table key := by
  unfold _root_.Object_table.remove _root_.Object_table.borrow
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields <;>
    simp

-- Same-key transports.

@[simp] theorem object_table_contains_add_same
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) (value : V) :
    _root_.Object_table.contains K V
      (_root_.Object_table.add K V table key value) key = true := by
  unfold _root_.Object_table.contains _root_.Object_table.add
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | some kv => simp [h_find]
  | none => simp [h_find]

theorem object_table_borrow_add_same_of_not_contains
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) (value : V)
    (h_not_contains : _root_.Object_table.contains K V table key = false) :
    _root_.Object_table.borrow K V
      (_root_.Object_table.add K V table key value) key = value := by
  unfold _root_.Object_table.contains at h_not_contains
  unfold _root_.Object_table.borrow _root_.Object_table.add
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | some kv => simp [h_find] at h_not_contains
  | none => simp [h_find]

@[simp] theorem object_table_contains_remove_same
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    _root_.Object_table.contains K V
      (_root_.Object_table.remove K V table key).2 key = false := by
  unfold _root_.Object_table.contains _root_.Object_table.remove
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | none => simp [h_find]
  | some kv => simp [List.find?_filter]

@[simp] theorem object_table_borrow_remove_same
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    _root_.Object_table.borrow K V
      (_root_.Object_table.remove K V table key).2 key = default := by
  unfold _root_.Object_table.borrow _root_.Object_table.remove
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | none => simp [h_find]
  | some kv =>
      simp only [h_find, List.find?_filter]
      have h_none :
          List.find? (fun _ : K × V => false) table.dynamic_fields = none := by
        exact List.find?_eq_none.mpr (by simp)
      have h_pred :
          (fun a : K × V =>
            decide ((!(a.1 == key)) = true ∧ (a.1 == key) = true)) =
            (fun _ : K × V => false) := by
        funext a
        cases h_match : (a.1 == key) <;> rfl
      rw [h_pred]
      rw [h_none]

-- Private `find?`-under-`set` helpers, mirrored from `TableNatives.lean`
-- (identical storage shape; the originals are `private` there).

private theorem object_table_set_find_same_of_contains
    {K V : Type} [BEq K] [LawfulBEq K]
    (fields : List (K × V)) (key : K) (value : V)
    (h_contains :
      (List.find? (fun kv : K × V => kv.1 == key) fields).isSome = true) :
    List.find? (fun kv : K × V => kv.1 == key)
        (fields.map fun kv => if kv.1 == key then (kv.1, value) else kv) =
      some (key, value) := by
  induction fields with
  | nil =>
      simp at h_contains
  | cons kv rest ih =>
      by_cases h_match : kv.1 = key
      · subst key
        simp
      · have h_beq : (kv.1 == key) = false := by
          exact Bool.eq_false_iff.mpr (fun h => h_match (LawfulBEq.eq_of_beq h))
        have h_find_cons :
            List.find? (fun kv : K × V => kv.1 == key) (kv :: rest) =
              List.find? (fun kv : K × V => kv.1 == key) rest := by
          exact List.find?_cons_of_neg (by simp [h_beq])
        rw [h_find_cons] at h_contains
        let p : K × V → Bool := fun kv => kv.1 == key
        let f : K × V → K × V :=
          fun kv => if kv.1 == key then (kv.1, value) else kv
        change List.find? p (f kv :: rest.map f) = some (key, value)
        have hfkv : f kv = kv := by
          simp [f, h_beq]
        rw [hfkv]
        have h_not : ¬ p kv = true := by
          simp [p, h_beq]
        rw [List.find?_cons_of_neg h_not]
        exact ih h_contains

private theorem object_table_set_find_ne
    {K V : Type} [BEq K] [LawfulBEq K]
    (fields : List (K × V)) (updated key : K) (value : V)
    (h_ne : key ≠ updated) :
    List.find? (fun kv : K × V => kv.1 == key)
        (fields.map fun kv => if kv.1 == updated then (kv.1, value) else kv) =
      List.find? (fun kv : K × V => kv.1 == key) fields := by
  induction fields with
  | nil =>
      rfl
  | cons kv rest ih =>
      simp only [List.map]
      by_cases h_updated : (kv.1 == updated) = true
      · rw [if_pos h_updated]
        have h_key : ¬(kv.1 == key) = true := by
          intro h_key
          exact h_ne <|
            (LawfulBEq.eq_of_beq h_key).symm.trans
              (LawfulBEq.eq_of_beq h_updated)
        rw [List.find?_cons_of_neg
          (p := fun kv : K × V => kv.1 == key)
          (a := (kv.1, value)) h_key]
        rw [List.find?_cons_of_neg
          (p := fun kv : K × V => kv.1 == key) (a := kv) h_key]
        exact ih
      · rw [if_neg h_updated]
        by_cases h_key : (kv.1 == key) = true
        · rw [List.find?_cons_of_pos
            (p := fun kv : K × V => kv.1 == key) h_key]
          rw [List.find?_cons_of_pos
            (p := fun kv : K × V => kv.1 == key) h_key]
        · rw [List.find?_cons_of_neg
            (p := fun kv : K × V => kv.1 == key) h_key]
          rw [List.find?_cons_of_neg
            (p := fun kv : K × V => kv.1 == key) h_key]
          exact ih

private theorem object_table_set_find_isSome_same
    {K V : Type} [BEq K]
    (fields : List (K × V)) (key : K) (value : V) :
    (List.find? (fun kv : K × V => kv.1 == key)
        (fields.map fun kv => if kv.1 == key then (kv.1, value) else kv)).isSome =
      (List.find? (fun kv : K × V => kv.1 == key) fields).isSome := by
  induction fields with
  | nil =>
      rfl
  | cons kv rest ih =>
      by_cases h_match : (kv.1 == key) = true
      · simp [h_match]
      · simp only [List.map, if_neg h_match]
        rw [List.find?_cons_of_neg
          (p := fun kv : K × V => kv.1 == key) (a := kv) h_match]
        rw [List.find?_cons_of_neg
          (p := fun kv : K × V => kv.1 == key) (a := kv) h_match]
        exact ih

-- `set` (the borrow_mut writeback) transports.

/-- Same-key `contains`/`set` frame. -/
@[simp] theorem object_table_contains_set_same
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) (value : V) :
    _root_.Object_table.contains K V
      (_root_.Object_table.set K V table key value) key =
      _root_.Object_table.contains K V table key := by
  unfold _root_.Object_table.contains _root_.Object_table.set
  exact object_table_set_find_isSome_same table.dynamic_fields key value

theorem object_table_contains_set_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (updated key : K) (value : V)
    (h_ne : key ≠ updated) :
    _root_.Object_table.contains K V
      (_root_.Object_table.set K V table updated value) key =
      _root_.Object_table.contains K V table key := by
  unfold _root_.Object_table.contains _root_.Object_table.set
  rw [object_table_set_find_ne table.dynamic_fields updated key value h_ne]

/-- Unconditional `contains`/`set` frame: `set` rewrites values in place and
never changes the key set, so presence is invariant at EVERY key. -/
theorem object_table_contains_set
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (updated key : K) (value : V) :
    _root_.Object_table.contains K V
      (_root_.Object_table.set K V table updated value) key =
      _root_.Object_table.contains K V table key := by
  by_cases h_same : key = updated
  · subst h_same
    exact object_table_contains_set_same K V table key value
  · exact object_table_contains_set_ne K V table updated key value h_same

theorem object_table_borrow_set_same_of_contains
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) (value : V)
    (h_contains : _root_.Object_table.contains K V table key = true) :
    _root_.Object_table.borrow K V
      (_root_.Object_table.set K V table key value) key = value := by
  unfold _root_.Object_table.contains at h_contains
  unfold _root_.Object_table.borrow _root_.Object_table.set
  have h_find := object_table_set_find_same_of_contains
    table.dynamic_fields key value h_contains
  simp [h_find]

theorem object_table_borrow_set_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (updated key : K) (value : V)
    (h_ne : key ≠ updated) :
    _root_.Object_table.borrow K V
      (_root_.Object_table.set K V table updated value) key =
      _root_.Object_table.borrow K V table key := by
  unfold _root_.Object_table.borrow _root_.Object_table.set
  rw [object_table_set_find_ne table.dynamic_fields updated key value h_ne]

-- Distinct-key transports for `add` / `remove`.

theorem object_table_contains_add_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (added key : K) (value : V)
    (h_ne : key ≠ added) :
    _root_.Object_table.contains K V
      (_root_.Object_table.add K V table added value) key =
      _root_.Object_table.contains K V table key := by
  unfold _root_.Object_table.contains _root_.Object_table.add
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | some kv => simp [h_find]
  | none =>
      have h_beq : (added == key) = false := by
        apply Bool.eq_false_iff.mpr
        intro h_true
        exact h_ne ((LawfulBEq.eq_of_beq h_true).symm)
      simp [h_find, h_beq]

theorem object_table_borrow_add_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (added key : K) (value : V)
    (h_ne : key ≠ added) :
    _root_.Object_table.borrow K V
      (_root_.Object_table.add K V table added value) key =
      _root_.Object_table.borrow K V table key := by
  unfold _root_.Object_table.borrow _root_.Object_table.add
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | some kv => simp [h_find]
  | none =>
      have h_beq : (added == key) = false := by
        apply Bool.eq_false_iff.mpr
        intro h_true
        exact h_ne ((LawfulBEq.eq_of_beq h_true).symm)
      simp [h_find, h_beq]

theorem object_table_contains_remove_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (removed key : K)
    (h_ne : key ≠ removed) :
    _root_.Object_table.contains K V
      (_root_.Object_table.remove K V table removed).2 key =
      _root_.Object_table.contains K V table key := by
  unfold _root_.Object_table.contains _root_.Object_table.remove
  cases h_find_removed :
      List.find? (fun kv => kv.1 == removed) table.dynamic_fields with
  | none =>
      simp [h_find_removed]
  | some kv =>
      simp [h_find_removed, List.find?_filter]
      have h_pred :
          (fun a : K × V => (!(a.1 == removed)) && (a.1 == key)) =
            (fun a : K × V => a.1 == key) := by
        funext a
        by_cases h_key : a.1 = key
        · subst key
          have h_not_removed : (a.1 == removed) = false := by
            apply Bool.eq_false_iff.mpr
            intro h_true
            exact h_ne (LawfulBEq.eq_of_beq h_true)
          simp [h_not_removed]
        · have h_key_beq : (a.1 == key) = false := by
            apply Bool.eq_false_iff.mpr
            intro h_true
            exact h_key (LawfulBEq.eq_of_beq h_true)
          simp [h_key_beq]
      simp [h_pred]

theorem object_table_borrow_remove_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (removed key : K)
    (h_ne : key ≠ removed) :
    _root_.Object_table.borrow K V
      (_root_.Object_table.remove K V table removed).2 key =
      _root_.Object_table.borrow K V table key := by
  unfold _root_.Object_table.borrow _root_.Object_table.remove
  cases h_find_removed :
      List.find? (fun kv => kv.1 == removed) table.dynamic_fields with
  | none =>
      simp [h_find_removed]
  | some kv =>
      have h_pred :
          (fun a : K × V => (!(a.1 == removed)) && (a.1 == key)) =
            (fun a : K × V => a.1 == key) := by
        funext a
        by_cases h_key : a.1 = key
        · subst key
          have h_not_removed : (a.1 == removed) = false := by
            apply Bool.eq_false_iff.mpr
            intro h_true
            exact h_ne (LawfulBEq.eq_of_beq h_true)
          simp [h_not_removed]
        · have h_key_beq : (a.1 == key) = false := by
            apply Bool.eq_false_iff.mpr
            intro h_true
            exact h_key (LawfulBEq.eq_of_beq h_true)
          simp [h_key_beq]
      simp [h_find_removed, List.find?_filter, h_pred]

-- Unified same/distinct-key if-forms (citation-only).

theorem object_table_contains_add
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (added key : K) (value : V) :
    _root_.Object_table.contains K V
      (_root_.Object_table.add K V table added value) key =
      if key == added then true
      else _root_.Object_table.contains K V table key := by
  by_cases h_same : (key == added) = true
  · rw [if_pos h_same]
    have h_eq : key = added := LawfulBEq.eq_of_beq h_same
    subst key
    exact object_table_contains_add_same K V table added value
  · rw [if_neg h_same]
    have h_ne : key ≠ added := by
      intro h_eq
      subst key
      exact h_same (beq_self_eq_true added)
    exact object_table_contains_add_ne K V table added key value h_ne

theorem object_table_borrow_add
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (added key : K) (value : V)
    (h_not_contains : _root_.Object_table.contains K V table added = false) :
    _root_.Object_table.borrow K V
      (_root_.Object_table.add K V table added value) key =
      if key == added then value
      else _root_.Object_table.borrow K V table key := by
  by_cases h_same : (key == added) = true
  · rw [if_pos h_same]
    have h_eq : key = added := LawfulBEq.eq_of_beq h_same
    subst key
    exact object_table_borrow_add_same_of_not_contains K V table added value
      h_not_contains
  · rw [if_neg h_same]
    have h_ne : key ≠ added := by
      intro h_eq
      subst key
      exact h_same (beq_self_eq_true added)
    exact object_table_borrow_add_ne K V table added key value h_ne

theorem object_table_borrow_set
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (updated key : K) (value : V)
    (h_contains : _root_.Object_table.contains K V table updated = true) :
    _root_.Object_table.borrow K V
      (_root_.Object_table.set K V table updated value) key =
      if key == updated then value
      else _root_.Object_table.borrow K V table key := by
  by_cases h_same : (key == updated) = true
  · rw [if_pos h_same]
    have h_eq : key = updated := LawfulBEq.eq_of_beq h_same
    subst key
    exact object_table_borrow_set_same_of_contains K V table updated value
      h_contains
  · rw [if_neg h_same]
    have h_ne : key ≠ updated := by
      intro h_eq
      subst key
      exact h_same (beq_self_eq_true updated)
    exact object_table_borrow_set_ne K V table updated key value h_ne

theorem object_table_contains_remove
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (removed key : K) :
    _root_.Object_table.contains K V
      (_root_.Object_table.remove K V table removed).2 key =
      if key == removed then false
      else _root_.Object_table.contains K V table key := by
  by_cases h_same : (key == removed) = true
  · have h_eq : key = removed := LawfulBEq.eq_of_beq h_same
    subst key
    rw [if_pos h_same]
    exact object_table_contains_remove_same K V table removed
  · rw [if_neg h_same]
    have h_ne : key ≠ removed := by
      intro h_eq
      subst key
      exact h_same (beq_self_eq_true removed)
    exact object_table_contains_remove_ne K V table removed key h_ne

theorem object_table_borrow_remove
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (removed key : K) :
    _root_.Object_table.borrow K V
      (_root_.Object_table.remove K V table removed).2 key =
      if key == removed then default
      else _root_.Object_table.borrow K V table key := by
  by_cases h_same : (key == removed) = true
  · have h_eq : key = removed := LawfulBEq.eq_of_beq h_same
    subst key
    rw [if_pos h_same]
    exact object_table_borrow_remove_same K V table removed
  · rw [if_neg h_same]
    have h_ne : key ≠ removed := by
      intro h_eq
      subst key
      exact h_same (beq_self_eq_true removed)
    exact object_table_borrow_remove_ne K V table removed key h_ne

-- Size / emptiness transports.

@[simp] theorem object_table_length_set
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) (value : V) :
    _root_.Object_table.length K V
      (_root_.Object_table.set K V table key value) =
      _root_.Object_table.length K V table := by
  apply BoundedNat.ext
  show (table.dynamic_fields.map _).length % (2^64) =
    table.dynamic_fields.length % (2^64)
  rw [List.length_map]

@[simp] theorem object_table_is_empty_set
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) (value : V) :
    _root_.Object_table.is_empty K V
      (_root_.Object_table.set K V table key value) =
      _root_.Object_table.is_empty K V table := by
  unfold _root_.Object_table.is_empty _root_.Object_table.set
  cases table.dynamic_fields <;> rfl

@[simp] theorem object_table_is_empty_add
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) (value : V) :
    _root_.Object_table.is_empty K V
      (_root_.Object_table.add K V table key value) = false := by
  unfold _root_.Object_table.is_empty _root_.Object_table.add
  cases table.dynamic_fields <;> rfl

/-- See `table_length_add_val` for why this is stated at `.val` and
    citation-only. -/
theorem object_table_length_add_val
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) (value : V) :
    (_root_.Object_table.length K V
      (_root_.Object_table.add K V table key value)).val =
      (_root_.Object_table.length K V table).val + 1 := by
  have h_bound := MoveVector.list_length_bounded_pred (K × V) table.dynamic_fields
  show (table.dynamic_fields ++ [(key, value)]).length % (2^64) =
    table.dynamic_fields.length % (2^64) + 1
  rw [List.length_append]
  simp only [List.length_cons, List.length_nil]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

-- ---------------------------------------------------------------------------
-- Pass 2: the size x remove row (see the TableNatives twin for why the
-- "length - 1" equality would be dishonest under duplicate keys).
-- ---------------------------------------------------------------------------

-- (strict-decrease core consolidated into `ListFacts.length_filter_lt_of_any`
-- in `Prelude/Helpers.lean` by the lemma-wave landing.)

theorem object_table_remove_snd_of_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K)
    (h_not_contains : _root_.Object_table.contains K V table key = false) :
    (_root_.Object_table.remove K V table key).2 = table := by
  unfold _root_.Object_table.contains at h_not_contains
  unfold _root_.Object_table.remove
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | some kv =>
      rw [h_find] at h_not_contains
      simp at h_not_contains
  | none => simp [h_find]

theorem object_table_length_remove_le
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K) :
    (_root_.Object_table.length K V
      (_root_.Object_table.remove K V table key).2).val ≤
      (_root_.Object_table.length K V table).val := by
  have h_bound := MoveVector.list_length_bounded (K × V) table.dynamic_fields
  unfold _root_.Object_table.length _root_.Object_table.remove
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | none => simp
  | some kv =>
      have h_le := List.length_filter_le
        (fun e : K × V => !(e.1 == key)) table.dynamic_fields
      simp only [h_find]
      show (table.dynamic_fields.filter _).length % (2^64) ≤
        table.dynamic_fields.length % (2^64)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h_bound]
      exact h_le

theorem object_table_length_remove_lt_of_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V) (key : K)
    (h_contains : _root_.Object_table.contains K V table key = true) :
    (_root_.Object_table.length K V
      (_root_.Object_table.remove K V table key).2).val <
      (_root_.Object_table.length K V table).val := by
  have h_bound := MoveVector.list_length_bounded (K × V) table.dynamic_fields
  unfold _root_.Object_table.contains at h_contains
  unfold _root_.Object_table.length _root_.Object_table.remove
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | none =>
      rw [h_find] at h_contains
      simp at h_contains
  | some kv =>
      have h_pred := List.find?_some h_find
      have h_mem := List.mem_of_find?_eq_some h_find
      have h_any : table.dynamic_fields.any (fun kv => kv.1 == key) = true :=
        List.any_eq_true.mpr ⟨kv, h_mem, h_pred⟩
      have h_lt := ListFacts.length_filter_lt_of_any table.dynamic_fields
        (fun kv => kv.1 == key) h_any
      simp only [h_find]
      show (table.dynamic_fields.filter _).length % (2^64) <
        table.dynamic_fields.length % (2^64)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h_bound]
      exact h_lt

-- Pass 2: cross-container mirror of `Table.length_lt_u64_max_pred` (the M2
-- Boogie-parity corollary; same statement, same proof, same consumer shape).

theorem object_table_length_lt_u64_max_pred
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Object_table.ObjectTable K V)
    (m : BoundedNat (2^64)) (hm : m.val = 18446744073709551615) :
    BoundedNat.lt (_root_.Object_table.length K V table) m = true := by
  unfold _root_.Object_table.length BoundedNat.lt
  have h := MoveVector.list_length_bounded_pred (K × V) table.dynamic_fields
  apply nat_blt_eq_true
  rw [hm]
  show table.dynamic_fields.length % (2^64) < 18446744073709551615
  have hmod : table.dynamic_fields.length % (2^64) =
      table.dynamic_fields.length :=
    Nat.mod_eq_of_lt (by omega)
  omega
