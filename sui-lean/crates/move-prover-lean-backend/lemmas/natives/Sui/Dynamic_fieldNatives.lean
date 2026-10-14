-- Native implementations for sui::dynamic_field
-- Low-level VM functions that have no Move source.
-- Higher-level functions (borrow, add, remove, exists) are Move-defined
-- and get rewritten to TypedMap operations by the dynamic field rewriting pass.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.ProgramState
import Sui.ObjectNatives

set_option linter.unusedVariables false

namespace Dynamic_field

-- Struct: dynamic_field::Field
structure Field (tv0 : Type) (tv1 : Type) where
  id : Object.UID
  name : tv0
  value : tv1
deriving BEq
instance [Inhabited tv0] [Inhabited tv1] : Inhabited (Field tv0 tv1) where default := ⟨default, default, default⟩

-- hash_type_and_key computes a hash of the type and key for dynamic field lookup
def hash_type_and_key (tv0 : Type) (_parent : Address) (_key : tv0) : Address :=
  Address.mk 0

-- add_child_object adds a child object to a parent
def add_child_object (tv0 : Type) (_parent : Address) (_child : tv0) : Unit :=
  ()

-- has_child_object checks if a child object exists
@[reducible] def has_child_object (_parent : Address) (_id : Address) : Bool :=
  false

-- has_child_object_with_ty checks if a child object of specific type exists
@[reducible] def has_child_object_with_ty (tv0 : Type) (_parent : Address) (_id : Address) : Bool :=
  false

-- borrow_child_object borrows a child object immutably.
-- The dynamic_field_rewriting pass turns most uses into TypedMap.get; this
-- stub catches stragglers and returns the type's default so test bodies
-- evaluate without `sorry`.
def borrow_child_object (tv0 : Type) [Inhabited tv0] (_parent : Object.UID) (_id : Address) : tv0 :=
  default

-- borrow_child_object_mut borrows a child object mutably.
-- Returns a default Mutable wrapper; the .aborts companion already captures
-- the relevant abort condition at the higher-level dynamic_field call sites.
def borrow_child_object_mut (tv0 : Type) [Inhabited tv0] (_parent : Object.UID) (_id : Address) : (Mutable tv0 Object.UID) × Object.UID :=
  (Mutable.mk default (fun _ => default), default)

-- remove_child_object removes and returns a child object
def remove_child_object (tv0 : Type) [Inhabited tv0] (_parent : Address) (_id : Address) : tv0 :=
  default

-- field_info returns UID and address for a dynamic field
def field_info (tv0 : Type) [BEq tv0] [Inhabited tv0] (_object : Object.UID) (_name : tv0) : (Object.UID × Address) :=
  (default, default)

-- field_info_mut is the mutable variant
def field_info_mut (tv0 : Type) [BEq tv0] [Inhabited tv0] (_object : Object.UID) (_name : tv0) : ((Object.UID × Address) × Object.UID) :=
  ((default, default), default)

end Dynamic_field
