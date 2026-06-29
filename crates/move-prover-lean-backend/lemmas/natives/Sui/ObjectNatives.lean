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
