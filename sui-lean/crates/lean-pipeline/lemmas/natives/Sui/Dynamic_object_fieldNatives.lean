-- Native implementations for sui::dynamic_object_field.
--
-- dof is modelled IDENTICALLY to `dynamic_field`. The value being an
-- object (the Move `key` ability) is a blockchain storage optimisation
-- we deliberately do NOT model: at the Lean level these are the same
-- `Inhabited`-only stubs, and the high-level ops (add/borrow/borrow_mut/
-- exists_/exists_with_type/remove) are routed to the World `store_*`
-- natives by `dynamic_field_rewrite::df_op` exactly like df. `key`-related
-- abort semantics live in the verification harness.
--
-- `Parent` is an IMPLICIT `{Parent : Type}` (inferred from `_self`),
-- mirroring df. Call sites supply only the source-level type-args
-- (`[Name, Value]`, or `[Name]` for `exists_`/`id`); the parent struct
-- type is recovered from the self argument. These stubs are only reached
-- for the residual ops not covered by the world-routing rewrite
-- (`internal_*`, `id`, `borrow_or_unknown`); the routed ops never hit them.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.ProgramState
import Sui.ObjectNatives
import MoveStdlib.MoveOption

set_option linter.unusedVariables false

namespace Dynamic_object_field

-- Internal wrapper key used by the Move source to keep
-- dynamic_object_field keys disjoint from direct dynamic_field keys
-- on the same UID. Surface from the IR; instances let it sit inside
-- helper-fn return positions.
structure Wrapper (tv0 : Type) where
  name : tv0
deriving DecidableEq
instance [Inhabited tv0] : Inhabited (Wrapper tv0) where default := ⟨default⟩

-- ---------------------------------------------------------------------------
-- High-level natives (new-pipeline).
--
-- After stage 3 mut-to-let, callers pass the unwrapped (`.val`-stripped)
-- parent for any `&mut UID` parameter and re-wrap the augmented return
-- via the renderer's `callee_is_native` auto-unwrap. The native stubs
-- return abstract placeholder values; real verification is delegated
-- to the prover at proof time.
-- ---------------------------------------------------------------------------

/-- `dynamic_object_field::borrow<Name, Value>(object: &UID, name: Name): &Value`.
Immutable borrow on the parent struct `P`. Returns the type's default
since real lookup semantics live in the proof layer. -/
def borrow (Name Value : Type) {Parent : Type} [Inhabited Value]
    (_self : Parent) (_key : Name) : Value :=
  default

/-- `dynamic_object_field::borrow_mut<Name, Value>(object: &mut UID, name: Name): &mut Value`.
After stage 3 augmentation: `(self: Parent, key: Name) -> (Value, Parent)`.
The caller destructures `(value_mut, augmented_parent)`. Renderer
re-wraps each slot into the appropriate `Mutation` via its auto-unwrap. -/
def borrow_mut (Name Value : Type) {Parent : Type} [Inhabited Value]
    (self : Parent) (_key : Name) : Value × Parent :=
  (default, self)

/-- `dynamic_object_field::add<Name, Value>(object: &mut UID, name: Name, value: Value)`.
Move return is `()`; after stage 3 augmentation, returns just the
augmented Parent. -/
def add (Name Value : Type) {Parent : Type}
    (self : Parent) (_key : Name) (_value : Value) : Parent :=
  self

/-- `dynamic_object_field::remove<Name, Value>(object: &mut UID, name: Name): Value`.
After stage 3 augmentation: returns `(Value, Parent)`. -/
def remove (Name Value : Type) {Parent : Type} [Inhabited Value]
    (self : Parent) (_key : Name) : Value × Parent :=
  (default, self)

/-- `dynamic_object_field::exists_<Name>(object: &UID, name: Name): bool`.
No `&mut`; no augmentation. -/
def «exists_» (Name : Type) {Parent : Type} (_self : Parent) (_key : Name) : Bool :=
  false

/-- `dynamic_object_field::exists_with_type<Name, Value>(object: &UID, name: Name): bool`. -/
def exists_with_type (Name Value : Type) {Parent : Type}
    (_self : Parent) (_key : Name) : Bool :=
  false

/-- `dynamic_object_field::id<Name>(object: &UID, name: Name): Option<ID>`.
Returns the ID of the object associated with the dynamic object field,
or `none` if the field doesn't exist. Stub always returns `none`. -/
def id (Name : Type) {Parent : Type}
    (_self : Parent) (_key : Name) : MoveOption.MoveOption Object.ID :=
  ⟨[]⟩

-- ---------------------------------------------------------------------------
-- public(package) pass-throughs.
--
-- Same signatures as the public surface, sans the `key + store` /
-- `key` typeclass nuance which is purely a Move-level constraint.
-- ---------------------------------------------------------------------------

def internal_add (Name Value : Type) {Parent : Type}
    (self : Parent) (_key : Name) (_value : Value) : Parent :=
  self

def internal_borrow (Name Value : Type) {Parent : Type} [Inhabited Value]
    (_self : Parent) (_key : Name) : Value :=
  default

def internal_borrow_mut (Name Value : Type) {Parent : Type} [Inhabited Value]
    (self : Parent) (_key : Name) : Value × Parent :=
  (default, self)

def internal_remove (Name Value : Type) {Parent : Type} [Inhabited Value]
    (self : Parent) (_key : Name) : Value × Parent :=
  (default, self)

def internal_exists_with_type (Name Value : Type) {Parent : Type}
    (_self : Parent) (_key : Name) : Bool :=
  false

/-- `dynamic_object_field::borrow_or_unknown<Name, Value>(object: &UID, name: Name): &Value`.
Spec-only total counterpart of `borrow` that never aborts -- missing-field
reads return an uninterpreted-but-deterministic value (modelled here as
`default`). -/
def borrow_or_unknown (Name Value : Type) {Parent : Type} [Inhabited Value]
    (_self : Parent) (_key : Name) : Value :=
  default

-- ---------------------------------------------------------------------------
-- Aborts companions.
--
-- Always false; abort conditions for missing-key / type-mismatch live
-- in the verification harness, not the IR.
-- ---------------------------------------------------------------------------

def borrow.aborts (Name Value : Type) {Parent : Type} [Inhabited Value]
    (_self : Parent) (_key : Name) : Bool := false
def borrow_mut.aborts (Name Value : Type) {Parent : Type} [Inhabited Value]
    (_self : Parent) (_key : Name) : Bool := false
def add.aborts (Name Value : Type) {Parent : Type}
    (_self : Parent) (_key : Name) (_value : Value) : Bool := false
def remove.aborts (Name Value : Type) {Parent : Type} [Inhabited Value]
    (_self : Parent) (_key : Name) : Bool := false
def «exists_».aborts (Name : Type) {Parent : Type}
    (_self : Parent) (_key : Name) : Bool := false
def exists_with_type.aborts (Name Value : Type) {Parent : Type}
    (_self : Parent) (_key : Name) : Bool := false
def id.aborts (Name : Type) {Parent : Type}
    (_self : Parent) (_key : Name) : Bool := false

def internal_add.aborts (Name Value : Type) {Parent : Type}
    (_self : Parent) (_key : Name) (_value : Value) : Bool := false
def internal_borrow.aborts (Name Value : Type) {Parent : Type} [Inhabited Value]
    (_self : Parent) (_key : Name) : Bool := false
def internal_borrow_mut.aborts (Name Value : Type) {Parent : Type} [Inhabited Value]
    (_self : Parent) (_key : Name) : Bool := false
def internal_remove.aborts (Name Value : Type) {Parent : Type} [Inhabited Value]
    (_self : Parent) (_key : Name) : Bool := false
def internal_exists_with_type.aborts (Name Value : Type) {Parent : Type}
    (_self : Parent) (_key : Name) : Bool := false

end Dynamic_object_field
