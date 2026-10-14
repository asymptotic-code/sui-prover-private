-- Trusted model axiom(s) for `sui::table_vec` (density).
--
-- `table_vec::TableVec<T>` wraps a `Table<u64, T>` whose backing store is
-- mutated ONLY via `push_back` / `pop_back`, so every reachable TableVec has
-- keys exactly `0 .. length-1` (a dense prefix). The generated `Table` model
-- (TableNatives.lean) tracks an arbitrary key set in the ghost `dynamic_fields`
-- and cannot observe this invariant, so a linear scan
-- (`find_validator_from_table_vec.aborts.while_0`) that calls `table_vec::borrow`
-- at every intermediate index would spuriously appear to abort at an "absent"
-- index (concrete M3 counterexample: `dynamic_fields = [(1,_),(7,_)]`, length 2,
-- keys {1,7} -- the value search finds index 1 while the abort scan aborts at
-- index 0). This axiom restates the real TableVec contiguity invariant as a
-- trusted model assumption -- matching Boogie, where the scan's per-index
-- presence obligation is vacuous.
--
-- Precedent: MoveOption's `move_option_vec_length_le_one` (MoveOptionLemmas.lean)
-- and the M2 `list_length_bounded_pred` (MoveVectorNatives.lean) -- trusted,
-- container-shape model assumptions with an in-docstring justification.
--
-- Distinct from the generic partial-envelope gotcha: the root cause is the
-- missing density invariant, NOT a too-weak assert. The principled fix is an
-- `inv_target`-style datatype invariant the new pipeline cannot yet emit/consume
-- (memo M3, plans/sui-system-staking-fv.md); this axiom is the interim trusted
-- model of exactly that invariant, scoped to `TableVec` so it does not
-- over-constrain plain `Table<u64, V>` values.

import Sui.Table_vec
import Sui.TableNatives
import MoveStdlib.MoveVectorNatives

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Table_vec

/-- TableVec key-density (trusted model axiom). An index `i` is present in the
backing store iff `i < length`. `index_present t i` is `Table.contains
t.contents i`, so this pins the key set of a reachable TableVec to the dense
prefix `0 .. length-1`. -/
axiom index_present_iff_lt (t_tv0 : Type) [DecidableEq t_tv0] [Inhabited t_tv0]
    (t : (TableVec t_tv0)) (i : BoundedNat (2^64)) :
    Table_vec.index_present t_tv0 t i = true ↔
      BoundedNat.lt i (Table_vec.length t_tv0 t) = true

/-- Backing-table presence corollary: for `i < length` the key `i` is present in
the backing `Table`. Consumed by the value-scan (`find_validator_from_table_vec`)
reasoning. -/
theorem contains_of_lt (t_tv0 : Type) [DecidableEq t_tv0] [Inhabited t_tv0]
    (t : (TableVec t_tv0)) (i : BoundedNat (2^64))
    (h : BoundedNat.lt i (Table_vec.length t_tv0 t) = true) :
    _root_.Table.contains (BoundedNat (2^64)) t_tv0 t.contents i = true := by
  have hpres : Table_vec.index_present t_tv0 t i = true :=
    (index_present_iff_lt t_tv0 t i).mpr h
  unfold Table_vec.index_present at hpres
  exact hpres

/-- Abort corollary: `table_vec::borrow` does not abort at any in-range index.
This is the form the abort-side scan proofs consume -- it discharges the
`Table_vec.borrow.aborts` face that the M3 counterexample makes reachable-true
in the un-axiomatized model. -/
theorem borrow_noabort_of_lt (t_tv0 : Type) [DecidableEq t_tv0] [Inhabited t_tv0]
    (t : (TableVec t_tv0)) (i : BoundedNat (2^64))
    (h : BoundedNat.lt i (Table_vec.length t_tv0 t) = true) :
    Table_vec.borrow.aborts t_tv0 t i = Abort.AbortResult.NoAbort := by
  have hcontains : _root_.Table.contains (BoundedNat (2^64)) t_tv0 t.contents i = true :=
    contains_of_lt t_tv0 t i h
  have hbor : _root_.Table.borrow.aborts (BoundedNat (2^64)) t_tv0 t.contents i = false :=
    table_borrow_no_abort_of_contains (BoundedNat (2^64)) t_tv0 t.contents i hcontains
  have hgt : BoundedNat.gt (Table_vec.length t_tv0 t) i = true := h
  unfold Table_vec.borrow.aborts Table_vec.length.aborts
  simp only [_root_.Table.length_aborts_eq_false, if_false, hgt, hbor,
    if_true, Bool.false_eq_true]

/-- Abort corollary keyed on presence: an index that is `index_present` is in
range (by density) so `table_vec::borrow` does not abort there. This is the form
consumed at a scan's resolved index, where the surrounding spec's
`pending_found_index_present`-style `requires` supplies `index_present`. -/
theorem borrow_noabort_of_index_present (t_tv0 : Type) [DecidableEq t_tv0] [Inhabited t_tv0]
    (t : (TableVec t_tv0)) (i : BoundedNat (2^64))
    (h : Table_vec.index_present t_tv0 t i = true) :
    Table_vec.borrow.aborts t_tv0 t i = Abort.AbortResult.NoAbort :=
  borrow_noabort_of_lt t_tv0 t i ((index_present_iff_lt t_tv0 t i).mp h)

end Table_vec
