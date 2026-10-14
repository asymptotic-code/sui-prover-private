-- These lemmas reference framework `.aborts` companions (e.g.
-- `MoveOption.borrow.aborts`) that per-package pruning drops unless an
-- importing package actually uses those functions. The file is copied into
-- every output tree but imported by nobody, so `sui-lean --test` does not
-- build it as a standalone lake target. To import it from a client package,
-- that package must exercise the referenced `.aborts` functions (or a future
-- force-retain must keep them through pruning). See catalog item c1.
import MoveStdlib.MoveOption

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem move_option_some_no_abort
    (T : Type) [DecidableEq T] [Inhabited T] (e : T) :
    _root_.MoveOption.some.aborts T e =
      _root_.Abort.AbortResult.NoAbort := by
  simp

theorem move_option_none_no_abort
    (T : Type) [DecidableEq T] [Inhabited T] :
    _root_.MoveOption.none.aborts T =
      _root_.Abort.AbortResult.NoAbort := by
  simp

axiom move_option_vec_length_le_one
    (T : Type) [DecidableEq T] [Inhabited T]
    (opt : _root_.MoveOption.MoveOption T) :
    opt.vec.length <= 1

theorem move_option_eq_some_of_is_some_borrow
    (T : Type) [DecidableEq T] [Inhabited T]
    (opt : _root_.MoveOption.MoveOption T) (v : T)
    (h_some : _root_.MoveOption.is_some T opt = true)
    (h_borrow : _root_.MoveOption.borrow T opt = v) :
    opt = _root_.MoveOption.some T v := by
  cases opt with
  | mk vec =>
      have h_vec_len_le_one : vec.length <= 1 :=
        move_option_vec_length_le_one T ({ vec := vec } : _root_.MoveOption.MoveOption T)
      cases vec with
      | nil =>
          simp [_root_.MoveOption.is_some, _root_.MoveVector.is_empty] at h_some
      | cons head tail =>
          have h_tail_len_succ_le_one : Nat.succ tail.length <= 1 := by
            simpa using h_vec_len_le_one
          have h_tail_len_zero : tail.length = 0 := by
            omega
          have h_tail_nil : tail = [] := by
            cases tail with
            | nil => rfl
            | cons _ _ => simp at h_tail_len_zero
          have h_head_eq : head = v := by
            have h_zero_val : (0 : BoundedNat (2^64)).val = 0 := by
              rfl
            simpa [_root_.MoveOption.borrow, _root_.MoveOption.is_some,
              _root_.MoveVector.is_empty, _root_.MoveVector.borrow,
              h_zero_val] using h_borrow
          subst tail
          subst head
          simp [_root_.MoveOption.some, _root_.MoveVector.singleton]

theorem move_option_borrow_no_abort_of_is_some
    {α : Type} [DecidableEq α] [Inhabited α]
    (opt : _root_.MoveOption.MoveOption α)
    (h_some : _root_.MoveOption.is_some α opt = true) :
    _root_.MoveOption.borrow.aborts α opt =
      _root_.Abort.AbortResult.NoAbort := by
  cases opt with
  | mk vec =>
      have h_vec_ne_nil : vec ≠ [] := by
        intro h_nil
        simp [_root_.MoveOption.is_some, _root_.MoveVector.is_empty,
          h_nil] at h_some
      have h_len_pos : 0 < vec.length := List.length_pos_iff.mpr h_vec_ne_nil
      have h_zero_val : (0 : BoundedNat (2^64)).val = 0 := by
        rfl
      have h_borrow_no_abort :
          _root_.MoveVector.borrow.aborts α vec (0 : BoundedNat (2^64)) =
            false := by
        unfold _root_.MoveVector.borrow.aborts
        rw [h_zero_val]
        exact decide_eq_false (Nat.not_le_of_gt h_len_pos)
      simp [_root_.MoveOption.borrow.aborts, h_some, h_borrow_no_abort]

theorem move_option_borrow_aborts_no_abort_of_is_some
    (α : Type) [DecidableEq α] [Inhabited α]
    (opt : _root_.MoveOption.MoveOption α)
    (h_some : _root_.MoveOption.is_some α opt = true) :
    _root_.MoveOption.borrow.aborts α opt =
      _root_.Abort.AbortResult.NoAbort :=
  move_option_borrow_no_abort_of_is_some opt h_some
