import Prover.Abort

theorem abort_result_eq_no_abort_of_flag_false {α : Type}
    {r : _root_.Abort.AbortResult α}
    (h :
      (match r with
      | _root_.Abort.AbortResult.NoAbort => false
      | _root_.Abort.AbortResult.Aborted _ => true) = false) :
    r = _root_.Abort.AbortResult.NoAbort := by
  cases r <;> simp at h ⊢

-- NOT promoted here: the `(match r with | .NoAbort => false | .Aborted _ => true)`
-- <-> `r = .NoAbort` bridges that every corpus carries per-file. At a CONCRETE
-- result type Lean elaborates a fresh per-module matcher auxiliary, and a copy
-- of the bridge living in this module is not defeq to the client's -- which is
-- exactly why those copies are per-file rather than per-corpus. The in-place
-- `cases r <;> simp_all` is one line and always works; a shared lemma does not.
-- See the W5 shared-facts report.
