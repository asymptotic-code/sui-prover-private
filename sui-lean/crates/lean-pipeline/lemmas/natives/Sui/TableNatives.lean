-- Native implementations for sui::table.
-- Ordinary `table::*` mutators are `PurePartial`: they mutate via
-- `&mut Table`, which stage 3 (mut-to-let) rewrites to value-form
-- let-rebinds. `table::new` is `TotalDetGlobalMut` because allocating its
-- UID threads world. The natives below take and return value-form
-- `Table K V`; callers strip `.val` from the surrounding
-- `Mutation (Table K V)` per the renderer's `callee_is_native`
-- auto-unwrap in `render::expr::render_call`.

import Prelude.BoundedNat
import Prelude.Helpers
import MoveStdlib.MoveVectorNatives
import Prover.MoveAutoAttr
import Sui.ObjectNatives
import Sui.Tx_contextNatives

namespace Table

-- Move source: `public struct Table<phantom K, phantom V> has key,
-- store { id: UID, size: u64 }`. The renderer carries the type params
-- positionally; `dynamic_fields` is a ghost field we keep so the
-- natives can store the key-value associations.
structure Table (tv0 : Type) (tv1 : Type) where
  id : Object.UID
  size : BoundedNat (2^64)
  dynamic_fields : List (tv0 × tv1)
deriving DecidableEq
instance [Inhabited tv0] [Inhabited tv1] : Inhabited (Table tv0 tv1) where default := ⟨default, default, default⟩

/-- `table::new<K, V>(ctx: &mut TxContext): Table<K, V>`. Stage 3
augments the `&mut TxContext` return; stage 4 threads the allocation world. -/
def new {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    Table K V × Tx_context.TxContext × Prover.World.World Ev Ob Df Be :=
  let created := Object.new ctx world
  (⟨created.1, (0 : BoundedNat (2^64)), []⟩, created.2.1, created.2.2)

/-- Allocation-frame pack (3/6): `table::new` allocates its UID through
    `object::new` and does nothing else to the world, so dynamic-field
    storage survives the hop. Without this a `dynamic_field` obligation
    taken over a world threaded through a `table::new` cannot be related
    to the base world at all except by unfolding the native, which
    materialises the whole `Table` literal. -/
@[simp] theorem new_world_df_entries {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    ((new K V ctx world).2.2).df_entries = world.df_entries := rfl

/-- Bag-store twin of `new_world_df_entries`: the constructor's one world
    action (`object::new`'s `allocate_id`) leaves bag-valued dynamic-field
    storage untouched too. -/
@[simp] theorem new_world_df_bag_entries {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    ((new K V ctx world).2.2).df_bag_entries = world.df_bag_entries := rfl

/-- Pass 2: the constructor's world and ctx ARE `object::new`'s (the struct
    literal only reorders the tuple). With `Object.new`'s per-field frames
    these subsume any remaining field frame at this constructor. -/
@[simp] theorem new_world {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (new K V ctx world).2.2 = (Object.new ctx world).2.2 := rfl

@[simp] theorem new_ctx {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (new K V ctx world).2.1 = (Object.new ctx world).2.1 := rfl

/-- Raw struct-field faces of the fresh table (WorldFrameLemmas migration:
    formerly `WorldFrame.table_new_id`/`_size`/`_dynamic_fields`). For proofs
    that project the record directly rather than go through an observer --
    the observer faces (`table_length_new`, ...) do not fire once a caller
    has already projected `.1.size` out of the tuple. -/
@[simp] theorem new_id {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (new K V ctx world).1.id = (Object.new ctx world).1 := rfl

@[simp] theorem new_size {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (new K V ctx world).1.size = (0 : BoundedNat (2^64)) := rfl

@[simp] theorem new_dynamic_fields {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    (new K V ctx world).1.dynamic_fields = ([] : List (K × V)) := rfl

/-- `table::add<K, V>(t: &mut Table<K, V>, k: K, v: V)`. Stage 3
rewrites the `&mut Table` body to value-form: caller passes the
unwrapped `Table K V` (via `.val`) and rebinds it with the result. -/
def add (K V : Type) [BEq K] [Inhabited V]
    (t : Table K V) (k : K) (v : V) : Table K V :=
  { t with size := BoundedNat.add t.size (1 : BoundedNat (2^64)),
           dynamic_fields := t.dynamic_fields ++ [(k, v)] }

/-- `table::borrow<K, V>(t: &Table<K, V>, k: K): &V`. Immutable
borrow: no Mutation involved on either side, just a value lookup.
Aborts in Move when the key is missing; here we fall back to
`default` so non-aborting test bodies evaluate without `sorry`. -/
def borrow (K V : Type) [BEq K] [Inhabited V] (t : Table K V) (k : K) : V :=
  match t.dynamic_fields.find? (fun kv => kv.1 == k) with
  | some kv => kv.2
  | none    => default

/-- `table::remove<K, V>(t: &mut Table<K, V>, k: K): V`. Stage 3
augments the return: caller destructures `(removed_value, new_table)`. -/
def remove (K V : Type) [BEq K] [Inhabited V]
    (t : Table K V) (k : K) : (V × Table K V) :=
  match t.dynamic_fields.find? (fun kv => kv.1 == k) with
  | some kv =>
    (kv.2,
     { t with size := BoundedNat.sub t.size (1 : BoundedNat (2^64)),
              dynamic_fields := t.dynamic_fields.filter (fun e => !(e.1 == k)) })
  | none    => (default, t)

/-- `table::contains<K, V>(t: &Table<K, V>, k: K): bool`. -/
def contains (K V : Type) [BEq K] [Inhabited V] (t : Table K V) (k : K) : Bool :=
  (t.dynamic_fields.find? (fun kv => kv.1 == k)).isSome

/-- `table::length<K, V>(t: &Table<K, V>): u64`. DERIVED from the map
(one source of truth; the tracked `size` field stays maintained for
struct-shape fidelity but is never read) -- see
plans/lean-pipeline/container-df-unification.md "size/contains". -/
def length (K V : Type) [BEq K] [Inhabited V] (t : Table K V) : BoundedNat (2^64) :=
  ⟨t.dynamic_fields.length % (2^64), Nat.mod_lt _ (by decide)⟩

/-- `table::is_empty<K, V>(t: &Table<K, V>): bool`. Derived. -/
def is_empty (K V : Type) [BEq K] [Inhabited V] (t : Table K V) : Bool :=
  t.dynamic_fields.isEmpty

/-- `table::destroy_empty<K, V>(t: Table<K, V>)`. -/
def destroy_empty (K V : Type) [BEq K] [Inhabited V] (_t : Table K V) : Unit := ()

/-- `table::drop<K, V>(t: Table<K, V>)`. -/
def drop (K V : Type) [BEq K] [Inhabited V] (_t : Table K V) : Unit := ()

/-- Spec-only key observer for the new pipeline's value-local Table model. -/
def spec_keys {World : Type} (K V : Type) [DecidableEq K]
    (table : Table K V) (world : World) : List K × World :=
  ((table.dynamic_fields.map (·.1)).eraseDups, world)

/-- Spec-only VALUE observer: every entry's value, in `dynamic_fields` order and
    multiplicity (no `eraseDups`). Returned by reference on the Move side
    (`&vector<V>`) so store-only value types need no `drop`; the reference is
    erased here. `all!(t.spec_values(), P)` is definitionally `dynamic_fields.all
    (fun e => P e.2)`, i.e. ALL entries, unlike `spec_keys`' distinct-key view. -/
def spec_values {World : Type} (K V : Type) [DecidableEq K]
    (table : Table K V) (world : World) : List V × World :=
  (table.dynamic_fields.map (·.2), world)

@[simp] theorem spec_values_world_passthrough {World : Type} (K V : Type)
    [DecidableEq K] (table : Table K V) (world : World) :
    (spec_values K V table world).2 = world := rfl

-- ---------------------------------------------------------------------------
-- `.aborts` companions for the partial Table operations.
--
-- Move's `table::new` is total at the VM layer. Its explicit false aborts
-- companion keeps that fact available independently of its world-mutating
-- effect classification and prevents transitive callers from acquiring a
-- spurious abort condition.
--
-- Aborts conditions follow Move semantics:
--   - `borrow` / `borrow_mut` / `remove` -- abort iff key is missing.
--   - `add` -- abort iff key is already present.
--   - `destroy_empty` -- abort iff the table is non-empty.
--   - `new` / `contains` / `length` / `is_empty` / `drop` -- total.
def new.aborts {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (_ctx : Tx_context.TxContext) (_world : Prover.World.World Ev Ob Df Be) : Bool := false
@[simp] theorem new_aborts_eq_false
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    new.aborts K V ctx world = false := rfl

def add.aborts (K V : Type) [BEq K] [Inhabited V] (t : Table K V) (k : K) (_v : V) : Bool :=
  (t.dynamic_fields.find? (fun kv => kv.1 == k)).isSome
def borrow.aborts (K V : Type) [BEq K] [Inhabited V] (t : Table K V) (k : K) : Bool :=
  (t.dynamic_fields.find? (fun kv => kv.1 == k)).isNone
def remove.aborts (K V : Type) [BEq K] [Inhabited V] (t : Table K V) (k : K) : Bool :=
  (t.dynamic_fields.find? (fun kv => kv.1 == k)).isNone
def contains.aborts (K V : Type) [BEq K] [Inhabited V] (_t : Table K V) (_k : K) : Bool := false
@[simp] theorem contains_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V] (t : Table K V) (k : K) :
    contains.aborts K V t k = false := rfl

def length.aborts (K V : Type) [BEq K] [Inhabited V] (_t : Table K V) : Bool := false
@[simp] theorem length_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V] (t : Table K V) :
    length.aborts K V t = false := rfl

/-- M2 corollary (Boogie parity): a well-formed `Table`'s length is strictly
below `u64::MAX = 2^64 - 1`. Consumed by specs carrying an explicit
`length() < 18446744073709551615` assert (the `size + 1` overflow guard that
Boogie discharges for free) -- e.g. `activate_staking_pool_spec`. Follows from
`MoveVector.list_length_bounded_pred` on the ghost `dynamic_fields`; the caller
supplies `m.val` since the generated bound is an opaque `large_uint_*` constant. -/
theorem length_lt_u64_max_pred (K V : Type) [BEq K] [Inhabited V] (t : Table K V)
    (m : BoundedNat (2^64)) (hm : m.val = 18446744073709551615) :
    BoundedNat.lt (length K V t) m = true := by
  unfold length BoundedNat.lt
  have h := MoveVector.list_length_bounded_pred (K × V) t.dynamic_fields
  apply nat_blt_eq_true
  rw [hm]
  show t.dynamic_fields.length % (2^64) < 18446744073709551615
  have hmod : t.dynamic_fields.length % (2^64) = t.dynamic_fields.length :=
    Nat.mod_eq_of_lt (by omega)
  omega

def is_empty.aborts (K V : Type) [BEq K] [Inhabited V] (_t : Table K V) : Bool := false
@[simp] theorem is_empty_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V] (t : Table K V) :
    is_empty.aborts K V t = false := rfl

def destroy_empty.aborts (K V : Type) [BEq K] [Inhabited V] (t : Table K V) : Bool :=
  -- Read `dynamic_fields` (the single source of truth, matching `is_empty`),
  -- not the maintained-but-unread `size` field which no invariant ties to it.
  !t.dynamic_fields.isEmpty
def drop.aborts (K V : Type) [BEq K] [Inhabited V] (_t : Table K V) : Bool := false
@[simp] theorem drop_aborts_eq_false
    (K V : Type) [BEq K] [Inhabited V] (t : Table K V) :
    drop.aborts K V t = false := rfl

/-- `table::borrow_mut<K, V>(t: &mut Table<K, V>, k: K): &mut V`. Same
abort condition as `borrow.aborts` -- both fail iff key is missing. -/
def borrow_mut.aborts (K V : Type) [BEq K] [Inhabited V] (t : Table K V) (k : K) : Bool :=
  (t.dynamic_fields.find? (fun kv => kv.1 == k)).isNone

/-- **NOT a Move source function** -- a writeback primitive added so
the new-pipeline renderer can express `*table::borrow_mut(t, k) = v`
without peeking into `Table`'s internal `dynamic_fields` representation.
Replaces the value at `k` with `v`; size unchanged (this is an
update, not an add). Idempotent / no-op when `k` is missing -- in
that case Move's preceding `borrow_mut` would have aborted before
this set fires, so the no-op branch is unreachable along
`AbortResult.NoAbort` paths. -/
def set (K V : Type) [BEq K] [Inhabited V] (t : Table K V) (k : K) (v : V) : Table K V :=
  let new_fields := t.dynamic_fields.map (fun kv => if kv.1 == k then (kv.1, v) else kv)
  { t with dynamic_fields := new_fields }

end Table

@[move_effect] theorem TableEffects.add_aborts_eq_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) (value : V) :
    _root_.Table.add.aborts K V table key value =
      _root_.Table.contains K V table key := by
  rfl

@[move_effect] theorem TableEffects.borrow_aborts_eq_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) :
    _root_.Table.borrow.aborts K V table key =
      !_root_.Table.contains K V table key := by
  unfold _root_.Table.borrow.aborts _root_.Table.contains
  cases List.find? (fun kv => kv.1 == key) table.dynamic_fields <;> rfl

@[move_effect] theorem TableEffects.borrow_mut_aborts_eq_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) :
    _root_.Table.borrow_mut.aborts K V table key =
      !_root_.Table.contains K V table key := by
  unfold _root_.Table.borrow_mut.aborts _root_.Table.contains
  cases List.find? (fun kv => kv.1 == key) table.dynamic_fields <;> rfl

@[move_effect] theorem TableEffects.remove_aborts_eq_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) :
    _root_.Table.remove.aborts K V table key =
      !_root_.Table.contains K V table key := by
  unfold _root_.Table.remove.aborts _root_.Table.contains
  cases List.find? (fun kv => kv.1 == key) table.dynamic_fields <;> rfl

theorem table_borrow_no_abort_of_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K)
    (h_contains : _root_.Table.contains K V table key = true) :
    _root_.Table.borrow.aborts K V table key = false := by
  simp only [TableEffects.borrow_aborts_eq_not_contains, h_contains, Bool.not_true]

theorem table_borrow_mut_no_abort_of_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K)
    (h_contains : _root_.Table.contains K V table key = true) :
    _root_.Table.borrow_mut.aborts K V table key = false := by
  simp only [TableEffects.borrow_mut_aborts_eq_not_contains, h_contains, Bool.not_true]

theorem table_remove_no_abort_of_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K)
    (h_contains : _root_.Table.contains K V table key = true) :
    _root_.Table.remove.aborts K V table key = false := by
  simp only [TableEffects.remove_aborts_eq_not_contains, h_contains, Bool.not_true]

theorem table_add_no_abort_of_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) (value : V)
    (h_not_contains : _root_.Table.contains K V table key = false) :
    _root_.Table.add.aborts K V table key value = false := by
  simp only [TableEffects.add_aborts_eq_contains, h_not_contains]

@[move_effect] theorem table_contains_add_same
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) (value : V) :
    _root_.Table.contains K V (_root_.Table.add K V table key value) key =
      true := by
  unfold _root_.Table.contains _root_.Table.add
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | some kv =>
      simp [h_find]
  | none =>
      simp [h_find]

@[move_effect] theorem table_contains_add_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (added key : K) (value : V)
    (h_ne : key ≠ added) :
    _root_.Table.contains K V (_root_.Table.add K V table added value) key =
      _root_.Table.contains K V table key := by
  unfold _root_.Table.contains _root_.Table.add
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | some kv =>
      simp [h_find]
  | none =>
      have h_beq : (added == key) = false := by
        apply Bool.eq_false_iff.mpr
        intro h_true
        exact h_ne ((LawfulBEq.eq_of_beq h_true).symm)
      simp [h_find, h_beq]

@[move_effect] theorem table_borrow_add_same_of_not_contains
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) (value : V)
    (h_not_contains : _root_.Table.contains K V table key = false) :
    _root_.Table.borrow K V (_root_.Table.add K V table key value) key =
      value := by
  unfold _root_.Table.contains at h_not_contains
  unfold _root_.Table.borrow _root_.Table.add
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | some kv =>
      simp [h_find] at h_not_contains
  | none =>
      simp [h_find]

@[move_effect] theorem table_borrow_add_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (added key : K) (value : V)
    (h_ne : key ≠ added) :
    _root_.Table.borrow K V (_root_.Table.add K V table added value) key =
      _root_.Table.borrow K V table key := by
  unfold _root_.Table.borrow _root_.Table.add
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | some kv =>
      simp [h_find]
  | none =>
      have h_beq : (added == key) = false := by
        apply Bool.eq_false_iff.mpr
        intro h_true
        exact h_ne ((LawfulBEq.eq_of_beq h_true).symm)
      simp [h_find, h_beq]

private theorem table_set_find_same_of_contains
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

private theorem table_set_find_ne
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

private theorem table_set_find_isSome_same
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

@[move_effect] theorem table_contains_set_same
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) (value : V) :
    _root_.Table.contains K V (_root_.Table.set K V table key value) key =
      _root_.Table.contains K V table key := by
  unfold _root_.Table.contains _root_.Table.set
  exact table_set_find_isSome_same table.dynamic_fields key value

theorem table_contains_set_same_of_contains
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) (value : V)
    (h_contains : _root_.Table.contains K V table key = true) :
    _root_.Table.contains K V (_root_.Table.set K V table key value) key =
      true := by
  unfold _root_.Table.contains _root_.Table.set at *
  have h_find := table_set_find_same_of_contains table.dynamic_fields key value h_contains
  simp [h_find]

@[move_effect] theorem TableEffects.contains_set_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (updated key : K) (value : V)
    (h_ne : key ≠ updated) :
    _root_.Table.contains K V (_root_.Table.set K V table updated value) key =
      _root_.Table.contains K V table key := by
  unfold _root_.Table.contains _root_.Table.set
  rw [table_set_find_ne table.dynamic_fields updated key value h_ne]

/-- Unconditional `contains`/`set` frame: `set` rewrites a value in place and
never changes the key set, so presence is invariant at EVERY key. Subsumes
`table_contains_set_same` and `TableEffects.contains_set_ne`; clients that
carry no `key ≠ updated` hypothesis cite this one. -/
theorem TableEffects.contains_set
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (updated key : K) (value : V) :
    _root_.Table.contains K V (_root_.Table.set K V table updated value) key =
      _root_.Table.contains K V table key := by
  by_cases h_ne : key = updated
  · subst h_ne
    exact table_contains_set_same K V table key value
  · exact TableEffects.contains_set_ne K V table updated key value h_ne

@[move_effect] theorem table_borrow_set_same_of_contains
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) (value : V)
    (h_contains : _root_.Table.contains K V table key = true) :
    _root_.Table.borrow K V (_root_.Table.set K V table key value) key =
      value := by
  unfold _root_.Table.contains at h_contains
  unfold _root_.Table.borrow _root_.Table.set
  have h_find := table_set_find_same_of_contains table.dynamic_fields key value h_contains
  simp [h_find]

@[move_effect] theorem TableEffects.borrow_set_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (updated key : K) (value : V)
    (h_ne : key ≠ updated) :
    _root_.Table.borrow K V (_root_.Table.set K V table updated value) key =
      _root_.Table.borrow K V table key := by
  unfold _root_.Table.borrow _root_.Table.set
  rw [table_set_find_ne table.dynamic_fields updated key value h_ne]

@[move_effect] theorem table_contains_remove_same
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) :
    _root_.Table.contains K V (_root_.Table.remove K V table key).2 key =
      false := by
  unfold _root_.Table.contains _root_.Table.remove
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | none =>
      simp [h_find]
  | some kv =>
      simp [List.find?_filter]

theorem table_contains_remove_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (removed key : K)
    (h_ne : key ≠ removed) :
    _root_.Table.contains K V (_root_.Table.remove K V table removed).2 key =
      _root_.Table.contains K V table key := by
  unfold _root_.Table.contains _root_.Table.remove
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

theorem table_borrow_remove_ne
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (removed key : K)
    (h_ne : key ≠ removed) :
    _root_.Table.borrow K V (_root_.Table.remove K V table removed).2 key =
      _root_.Table.borrow K V table key := by
  unfold _root_.Table.borrow _root_.Table.remove
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

theorem table_borrow_remove_same
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) :
    _root_.Table.borrow K V (_root_.Table.remove K V table key).2 key =
      default := by
  unfold _root_.Table.borrow _root_.Table.remove
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | none =>
      simp [h_find]
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

@[move_effect] theorem table_contains_remove
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (removed key : K) :
    _root_.Table.contains K V (_root_.Table.remove K V table removed).2 key =
      if key == removed then false else _root_.Table.contains K V table key := by
  by_cases h_same : (key == removed) = true
  · have h_eq : key = removed := LawfulBEq.eq_of_beq h_same
    subst key
    rw [if_pos h_same]
    exact table_contains_remove_same K V table removed
  · rw [if_neg h_same]
    have h_ne : key ≠ removed := by
      intro h_eq
      subst key
      exact h_same (beq_self_eq_true removed)
    exact table_contains_remove_ne K V table removed key h_ne

@[move_effect] theorem table_borrow_remove
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (removed key : K) :
    _root_.Table.borrow K V (_root_.Table.remove K V table removed).2 key =
      if key == removed then default else _root_.Table.borrow K V table key := by
  by_cases h_same : (key == removed) = true
  · have h_eq : key = removed := LawfulBEq.eq_of_beq h_same
    subst key
    rw [if_pos h_same]
    exact table_borrow_remove_same K V table removed
  · rw [if_neg h_same]
    have h_ne : key ≠ removed := by
      intro h_eq
      subst key
      exact h_same (beq_self_eq_true removed)
    exact table_borrow_remove_ne K V table removed key h_ne

theorem table_remove_fst_eq_borrow_of_contains
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K)
    (h_contains : _root_.Table.contains K V table key = true) :
    (_root_.Table.remove K V table key).1 =
      _root_.Table.borrow K V table key := by
  unfold _root_.Table.contains at h_contains
  unfold _root_.Table.remove _root_.Table.borrow
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | none =>
      simp [h_find] at h_contains
  | some kv =>
      simp [h_find]

@[move_effect] theorem table_remove_fst_eq_borrow
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) :
    (_root_.Table.remove K V table key).1 =
      _root_.Table.borrow K V table key := by
  unfold _root_.Table.remove _root_.Table.borrow
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields <;>
    simp [h_find]

-- ---------------------------------------------------------------------------
-- Constructor faces: every observer (and every partial op's abort face) at a
-- freshly constructed table. All rfl-class frame rewrites toward a literal,
-- so they carry `@[simp]` per the allocation-frame pack discipline.
-- ---------------------------------------------------------------------------

@[simp] theorem table_contains_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (key : K) :
    _root_.Table.contains K V (_root_.Table.new K V ctx world).1 key = false := rfl

@[simp] theorem table_borrow_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (key : K) :
    _root_.Table.borrow K V (_root_.Table.new K V ctx world).1 key = default := rfl

@[simp] theorem table_length_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    _root_.Table.length K V (_root_.Table.new K V ctx world).1 =
      (0 : BoundedNat (2^64)) := rfl

@[simp] theorem table_is_empty_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    _root_.Table.is_empty K V (_root_.Table.new K V ctx world).1 = true := rfl

@[simp] theorem table_add_aborts_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be)
    (key : K) (value : V) :
    _root_.Table.add.aborts K V (_root_.Table.new K V ctx world).1 key value =
      false := rfl

@[simp] theorem table_borrow_aborts_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (key : K) :
    _root_.Table.borrow.aborts K V (_root_.Table.new K V ctx world).1 key = true := rfl

@[simp] theorem table_borrow_mut_aborts_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (key : K) :
    _root_.Table.borrow_mut.aborts K V (_root_.Table.new K V ctx world).1 key =
      true := rfl

@[simp] theorem table_remove_aborts_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) (key : K) :
    _root_.Table.remove.aborts K V (_root_.Table.new K V ctx world).1 key = true := rfl

@[simp] theorem table_destroy_empty_aborts_new
    {Ev Ob Df Be : Type} (K V : Type) [BEq K] [Inhabited V]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be) :
    _root_.Table.destroy_empty.aborts K V (_root_.Table.new K V ctx world).1 =
      false := rfl

/-- Abort-face bridge for `destroy_empty`, completing the observer bridges:
    both sides read `dynamic_fields` (the single source of truth). -/
@[simp] theorem table_destroy_empty_aborts_eq_not_is_empty
    (K V : Type) [BEq K] [Inhabited V] (table : _root_.Table.Table K V) :
    _root_.Table.destroy_empty.aborts K V table =
      !_root_.Table.is_empty K V table := rfl

-- ---------------------------------------------------------------------------
-- Unified same/distinct-key transports (if-form), completing the matrix rows
-- that so far existed only as separate same-key / distinct-key lemmas.
-- Conditional / if-carrying, so citation + `@[move_effect]` only -- never
-- `@[simp]` (per the standing attribute discipline).
-- ---------------------------------------------------------------------------

@[move_effect] theorem table_contains_add
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (added key : K) (value : V) :
    _root_.Table.contains K V (_root_.Table.add K V table added value) key =
      if key == added then true else _root_.Table.contains K V table key := by
  by_cases h_same : (key == added) = true
  · rw [if_pos h_same]
    have h_eq : key = added := LawfulBEq.eq_of_beq h_same
    subst key
    exact table_contains_add_same K V table added value
  · rw [if_neg h_same]
    have h_ne : key ≠ added := by
      intro h_eq
      subst key
      exact h_same (beq_self_eq_true added)
    exact table_contains_add_ne K V table added key value h_ne

/-- `borrow` after `add`, both branches at once. The side condition is the
    add's own non-abort face (`contains = false`): the model appends, so at
    an already-present key the OLD value would still win the `find?` -- but
    Move's `add` aborts there, making the guarded statement the honest
    general form. -/
@[move_effect] theorem table_borrow_add
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (added key : K) (value : V)
    (h_not_contains : _root_.Table.contains K V table added = false) :
    _root_.Table.borrow K V (_root_.Table.add K V table added value) key =
      if key == added then value else _root_.Table.borrow K V table key := by
  by_cases h_same : (key == added) = true
  · rw [if_pos h_same]
    have h_eq : key = added := LawfulBEq.eq_of_beq h_same
    subst key
    exact table_borrow_add_same_of_not_contains K V table added value h_not_contains
  · rw [if_neg h_same]
    have h_ne : key ≠ added := by
      intro h_eq
      subst key
      exact h_same (beq_self_eq_true added)
    exact table_borrow_add_ne K V table added key value h_ne

/-- `borrow` after the `borrow_mut` writeback, both branches at once. Side
    condition mirrors Move: the preceding `borrow_mut` aborts unless the key
    is present, so `set` only fires under `contains = true`. -/
@[move_effect] theorem table_borrow_set
    (K V : Type) [BEq K] [LawfulBEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (updated key : K) (value : V)
    (h_contains : _root_.Table.contains K V table updated = true) :
    _root_.Table.borrow K V (_root_.Table.set K V table updated value) key =
      if key == updated then value else _root_.Table.borrow K V table key := by
  by_cases h_same : (key == updated) = true
  · rw [if_pos h_same]
    have h_eq : key = updated := LawfulBEq.eq_of_beq h_same
    subst key
    exact table_borrow_set_same_of_contains K V table updated value h_contains
  · rw [if_neg h_same]
    have h_ne : key ≠ updated := by
      intro h_eq
      subst key
      exact h_same (beq_self_eq_true updated)
    exact TableEffects.borrow_set_ne K V table updated key value h_ne

-- ---------------------------------------------------------------------------
-- Size / emptiness transports through the writers.
-- ---------------------------------------------------------------------------

/-- `set` maps values in place, so the derived length is untouched. -/
@[simp] theorem table_length_set
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) (value : V) :
    _root_.Table.length K V (_root_.Table.set K V table key value) =
      _root_.Table.length K V table := by
  apply BoundedNat.ext
  show (table.dynamic_fields.map _).length % (2^64) =
    table.dynamic_fields.length % (2^64)
  rw [List.length_map]

@[simp] theorem table_is_empty_set
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) (value : V) :
    _root_.Table.is_empty K V (_root_.Table.set K V table key value) =
      _root_.Table.is_empty K V table := by
  unfold _root_.Table.is_empty _root_.Table.set
  cases table.dynamic_fields <;> rfl

@[simp] theorem table_is_empty_add
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) (value : V) :
    _root_.Table.is_empty K V (_root_.Table.add K V table key value) = false := by
  unfold _root_.Table.is_empty _root_.Table.add
  cases table.dynamic_fields <;> rfl

/-- `add` appends exactly one entry, so the derived length grows by one --
    unconditionally (the model appends even at a present key; Move's `add`
    aborts there, so reachable uses always satisfy it). Stated at `.val` so
    no wrap term appears: `list_length_bounded_pred` caps the appended list
    below `2^64`. Citation-only: the RHS is not a smaller term. -/
theorem table_length_add_val
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) (value : V) :
    (_root_.Table.length K V (_root_.Table.add K V table key value)).val =
      (_root_.Table.length K V table).val + 1 := by
  have h_bound := MoveVector.list_length_bounded_pred (K × V) table.dynamic_fields
  show (table.dynamic_fields ++ [(key, value)]).length % (2^64) =
    table.dynamic_fields.length % (2^64) + 1
  rw [List.length_append]
  simp only [List.length_cons, List.length_nil]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

namespace Table

private theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ xs : List α, xs.eraseDups.Nodup
  | [] => by simp
  | a :: rest => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp
      · exact eraseDups_nodup (rest.filter fun b => !(b == a))
termination_by xs => xs.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem length_of_nodup_insert_membership {α : Type} [DecidableEq α]
    {a : α} {before after : List α} (h_before : before.Nodup)
    (h_after : after.Nodup)
    (h_mem : ∀ x, x ∈ after ↔ x = a ∨ x ∈ before) :
    after.length = if a ∈ before then before.length else before.length + 1 := by
  have h_perm : after.Perm (if a ∈ before then before else a :: before) := by
    rw [List.perm_iff_count]
    intro x
    simp only [h_after.count, h_mem]
    by_cases h_a : a ∈ before
    · rw [if_pos h_a, h_before.count]
      by_cases h_x : x = a <;> simp [h_x, h_a]
    · rw [if_neg h_a, (List.nodup_cons.mpr ⟨h_a, h_before⟩).count]
      by_cases h_x : x = a <;> simp [h_x, h_a]
  rw [h_perm.length_eq]
  split <;> simp

private theorem length_of_nodup_erase_membership {α : Type} [DecidableEq α]
    {a : α} {before after : List α} (h_before : before.Nodup)
    (h_after : after.Nodup)
    (h_mem : ∀ x, x ∈ after ↔ x ≠ a ∧ x ∈ before) :
    after.length = if a ∈ before then before.length - 1 else before.length := by
  by_cases h_a : a ∈ before
  · rw [if_pos h_a]
    have h_not_mem : a ∉ after := by
      intro h
      exact (h_mem a).mp h |>.1 rfl
    have h_perm : before.Perm (a :: after) := by
      rw [List.perm_iff_count]
      intro x
      rw [h_before.count, (List.nodup_cons.mpr ⟨h_not_mem, h_after⟩).count]
      simp only [List.mem_cons, h_mem]
      by_cases h_x : x = a <;> simp [h_x, h_a]
    have h_length := h_perm.length_eq
    simp only [List.length_cons] at h_length
    omega
  · rw [if_neg h_a]
    have h_perm : after.Perm before := by
      rw [List.perm_iff_count]
      intro x
      rw [h_after.count, h_before.count]
      simp only [h_mem]
      by_cases h_x : x = a <;> simp [h_x, h_a]
    exact h_perm.length_eq

@[simp] theorem spec_keys_world_passthrough
    {World K V : Type} [DecidableEq K]
    (table : Table K V) (world : World) :
    (spec_keys K V table world).2 = world := rfl

theorem spec_keys_fst_world_irrelevant
    {World K V : Type} [DecidableEq K]
    (table : Table K V) (before after : World) :
    (spec_keys K V table before).1 = (spec_keys K V table after).1 := rfl

@[simp] theorem spec_keys_nodup
    {World K V : Type} [DecidableEq K]
    (table : Table K V) (world : World) :
    (spec_keys K V table world).1.Nodup := by
  exact eraseDups_nodup _

@[simp] theorem mem_spec_keys_iff_contains
    {World K V : Type} [DecidableEq K] [BEq K] [LawfulBEq K] [Inhabited V]
    (table : Table K V) (world : World) (key : K) :
    key ∈ (spec_keys K V table world).1 ↔ contains K V table key = true := by
  unfold spec_keys contains
  simp only [List.mem_eraseDups, List.mem_map, List.find?_isSome]
  constructor
  · rintro ⟨kv, h_mem, rfl⟩
    exact ⟨kv, h_mem, beq_self_eq_true _⟩
  · rintro ⟨kv, h_mem, h_eq⟩
    exact ⟨kv, h_mem, LawfulBEq.eq_of_beq h_eq⟩

@[simp] theorem spec_keys_new
    {Ev Ob Df Be World K V : Type} [BEq K] [Inhabited V] [DecidableEq K]
    (ctx : Tx_context.TxContext) (world : Prover.World.World Ev Ob Df Be)
    (observer_world : World) :
    (spec_keys K V (new K V ctx world).1 observer_world).1 = [] := by
  simp [spec_keys, new]

@[move_effect] theorem mem_spec_keys_add
    {World K V : Type} [DecidableEq K] [BEq K] [LawfulBEq K] [Inhabited V]
    (table : Table K V) (world : World) (added key : K) (value : V) :
    key ∈ (spec_keys K V (add K V table added value) world).1 ↔
      key = added ∨ key ∈ (spec_keys K V table world).1 := by
  simp only [mem_spec_keys_iff_contains]
  by_cases h_eq : key = added
  · subst key
    simp [table_contains_add_same]
  · simp [h_eq, table_contains_add_ne K V table added key value h_eq]

@[move_effect] theorem spec_keys_add_length_of_not_contains
    {World K V : Type} [DecidableEq K] [BEq K] [LawfulBEq K] [Inhabited V]
    (table : Table K V) (world : World) (key : K) (value : V)
    (h_not_contains : contains K V table key = false) :
    (spec_keys K V (add K V table key value) world).1.length =
      (spec_keys K V table world).1.length + 1 := by
  have h_length := length_of_nodup_insert_membership
    (spec_keys_nodup table world)
    (spec_keys_nodup (add K V table key value) world)
    (fun x => mem_spec_keys_add table world key x value)
  rw [if_neg] at h_length
  · exact h_length
  · simpa using h_not_contains

@[move_effect] theorem mem_spec_keys_remove
    {World K V : Type} [DecidableEq K] [BEq K] [LawfulBEq K] [Inhabited V]
    (table : Table K V) (world : World) (removed key : K) :
    key ∈ (spec_keys K V (remove K V table removed).2 world).1 ↔
      key ≠ removed ∧ key ∈ (spec_keys K V table world).1 := by
  simp only [mem_spec_keys_iff_contains]
  by_cases h_eq : key = removed
  · subst key
    simp [table_contains_remove_same]
  · simp [h_eq, table_contains_remove_ne K V table removed key h_eq]

@[move_effect] theorem spec_keys_remove_length_of_contains
    {World K V : Type} [DecidableEq K] [BEq K] [LawfulBEq K] [Inhabited V]
    (table : Table K V) (world : World) (key : K)
    (h_contains : contains K V table key = true) :
    (spec_keys K V (remove K V table key).2 world).1.length =
      (spec_keys K V table world).1.length - 1 := by
  have h_length := length_of_nodup_erase_membership
    (spec_keys_nodup table world)
    (spec_keys_nodup (remove K V table key).2 world)
    (fun x => mem_spec_keys_remove table world key x)
  rw [if_pos] at h_length
  · exact h_length
  · simpa using h_contains

@[move_effect] theorem spec_keys_set
    {World K V : Type} [DecidableEq K] [BEq K] [Inhabited V]
    (table : Table K V) (world : World) (key : K) (value : V) :
    (spec_keys K V (set K V table key value) world).1 =
      (spec_keys K V table world).1 := by
  unfold spec_keys set
  have h_keys :
      List.map (fun kv : K × V => kv.1)
          (List.map
            (fun kv : K × V => if kv.1 == key then (kv.1, value) else kv)
            table.dynamic_fields) =
        List.map (fun kv : K × V => kv.1) table.dynamic_fields := by
    induction table.dynamic_fields with
    | nil => rfl
    | cons kv rest ih =>
        simp only [List.map]
        rw [ih]
        split <;> rfl
  rw [h_keys]

end Table

-- ---------------------------------------------------------------------------
-- Pass 2: the size x remove row, stated honestly. The model's `remove`
-- filters EVERY entry at the key, so with duplicate keys (unreachable via
-- Move's aborting `add`, but expressible in an arbitrary `Table` value) the
-- "length - 1" equality is FALSE; the honest characterization is the no-op
-- transport on the absent branch plus the le / strict-lt pair.
-- ---------------------------------------------------------------------------

-- (strict-decrease core consolidated into `ListFacts.length_filter_lt_of_any`
-- in `Prelude/Helpers.lean` by the lemma-wave landing.)

/-- Removing an absent key is a no-op on the whole table (the model returns
    `t` itself on that branch), so EVERY observer is framed at once. -/
theorem table_remove_snd_of_not_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K)
    (h_not_contains : _root_.Table.contains K V table key = false) :
    (_root_.Table.remove K V table key).2 = table := by
  unfold _root_.Table.contains at h_not_contains
  unfold _root_.Table.remove
  cases h_find : List.find? (fun kv => kv.1 == key) table.dynamic_fields with
  | some kv =>
      rw [h_find] at h_not_contains
      simp at h_not_contains
  | none => simp [h_find]

theorem table_length_remove_le
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K) :
    (_root_.Table.length K V (_root_.Table.remove K V table key).2).val ≤
      (_root_.Table.length K V table).val := by
  have h_bound := MoveVector.list_length_bounded (K × V) table.dynamic_fields
  unfold _root_.Table.length _root_.Table.remove
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

theorem table_length_remove_lt_of_contains
    (K V : Type) [BEq K] [Inhabited V]
    (table : _root_.Table.Table K V) (key : K)
    (h_contains : _root_.Table.contains K V table key = true) :
    (_root_.Table.length K V (_root_.Table.remove K V table key).2).val <
      (_root_.Table.length K V table).val := by
  have h_bound := MoveVector.list_length_bounded (K × V) table.dynamic_fields
  unfold _root_.Table.contains at h_contains
  unfold _root_.Table.length _root_.Table.remove
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
