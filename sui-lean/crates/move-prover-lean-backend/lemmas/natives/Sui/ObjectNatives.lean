-- Native implementations for sui::object

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.ProgramState

namespace Object

-- Struct definitions needed for the natives (defined first)
structure ID where
  bytes : Address
deriving BEq

structure UID where
  id : ID
deriving BEq

def uidKey (u : UID) : Nat := u.id.bytes.bytes.val

/-- Verification-only canonical token for semantic UID identity. In the
unified backend a UID's identity is its address value; the unary encoding
makes token equality definitionally reducible to identity equality. -/
def uid_token (uid : UID) : List (BoundedNat (2^8)) :=
  List.replicate (uidKey uid) (0 : BoundedNat (2^8))

@[simp] theorem length_uid_token (uid : UID) :
    (uid_token uid).length = uidKey uid := by
  simp [uid_token]

@[simp] theorem uid_token_eq_iff_uidKey_eq (left right : UID) :
    uid_token left = uid_token right ↔ uidKey left = uidKey right := by
  constructor
  · intro h
    have hlength := congrArg List.length h
    rw [length_uid_token, length_uid_token] at hlength
    exact hlength
  · intro h
    simp [uid_token, h]

@[simp] theorem uid_token_ne_iff_uidKey_ne (left right : UID) :
    uid_token left ≠ uid_token right ↔ uidKey left ≠ uidKey right := by
  simp only [ne_eq, uid_token_eq_iff_uidKey_eq]

@[simp] theorem uid_token_beq (left right : UID) :
    (uid_token left == uid_token right) = (uidKey left == uidKey right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, uid_token_eq_iff_uidKey_eq]

instance : Inhabited ID where
  default := { bytes := Address.mk 0 }

instance : Inhabited UID where
  default := { id := default }

-- Native function stubs

-- delete_impl deletes an object by its address
def delete_impl (_id : Address) : Unit :=
  ()

-- borrow_uid borrows the UID from an object
-- In Move this is a native that accesses the first field of any object with `key` ability
def borrow_uid (tv0 : Type) [BEq tv0] [Inhabited tv0] (_obj : tv0) : UID :=
  default

-- record_new_uid is called during object creation to register a new UID
def record_new_uid (_id : Address) : Unit :=
  ()

end Object
