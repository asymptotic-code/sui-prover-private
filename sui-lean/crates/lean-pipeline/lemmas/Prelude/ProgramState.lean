import Prelude.BoundedNat

-- Mutable reference wrapper for functional encoding of mutable borrows
-- val: the borrowed value
-- reconstruct: function to write the value back to the parent structure
structure Mutable (α : Type) (State : Type) where
  val : α
  reconstruct : α → State

instance [Inhabited α] [Inhabited State] : Inhabited (Mutable α State) where
  default := ⟨default, fun _ => default⟩

@[reducible] def Mutable.set (m : Mutable α State) (v : α) : Mutable α State :=
  ⟨v, m.reconstruct⟩

@[reducible] def Mutable.apply (m : Mutable α State) : State :=
  m.reconstruct m.val

@[reducible] def Mutable.compose (inner : Mutable α Mid) (outer : Mutable Mid Top) : Mutable α Top :=
  ⟨inner.val, fun v => outer.reconstruct (inner.reconstruct v)⟩

@[simp] theorem Mutable.apply_mk (v : α) (f : α → State) : (Mutable.mk v f).apply = f v := rfl
@[simp] theorem Mutable.val_mk (v : α) (f : α → State) : (Mutable.mk v f).val = v := rfl
@[simp] theorem Mutable.apply_set (m : Mutable α State) (v : α) : (m.set v).apply = m.reconstruct v := rfl
@[simp] theorem Mutable.val_set (m : Mutable α State) (v : α) : (m.set v).val = v := rfl

-- Pure while loop combinator
-- Takes a condition function, a body function, and initial state
-- Returns the final state after the condition becomes false
partial def whileLoop {α : Type}
  (cond : α → Prop) [inst : ∀ x, Decidable (cond x)]
  (body : α → α)
  (init : α) : α :=
  if cond init then
    whileLoop cond body (body init)
  else
    init
