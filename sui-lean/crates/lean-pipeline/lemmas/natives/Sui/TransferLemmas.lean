import Sui.Transfer

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem transfer_public_transfer_aborts_no_abort
    {Ev Obj Df Be ObjU : Type} [Universe ObjU]
    (t : Type) [DecidableEq t] [Inhabited t]
    [HasCode ObjU t] [_root_.Object.HasObjectId t]
    (obj : t)
    (recipient : Address)
    (world : _root_.Prover.World.World Ev (_root_.Bag.Entry ObjU) Df Be)
    (__ghost_SuiSpecs__transfer_spec__SpecTransferAddress : Address)
    (__ghost_SuiSpecs__transfer_spec__SpecTransferAddressExists : Bool) :
    _root_.Transfer.public_transfer.aborts t obj recipient world
      __ghost_SuiSpecs__transfer_spec__SpecTransferAddress __ghost_SuiSpecs__transfer_spec__SpecTransferAddressExists = _root_.Abort.AbortResult.NoAbort := by
  simp [_root_.Transfer.public_transfer.aborts]

/-- Bridge: the generated `public_transfer` body is exactly the ghost-augmented
    native transfer (`Transfer.transfer_impl__ghost`) -- the wrapper only
    destructures and repacks the triple, so the two are rfl-equal (structure
    eta). `@[simp]` routes every `public_transfer` goal into the
    `Sui.TransferNatives` face/frame battery (ownership transitions, frames,
    cross-object reads, freshness). -/
@[simp] theorem transfer_public_transfer_eq_impl_ghost
    {Ev Df Be ObjU : Type} [Universe ObjU]
    (t : Type) [DecidableEq t] [Inhabited t]
    [HasCode ObjU t] [_root_.Object.HasObjectId t]
    (obj : t) (recipient : Address)
    (world : _root_.Prover.World.World Ev (_root_.Bag.Entry ObjU) Df Be)
    (__ghost_178 : Address) (__ghost_179 : Bool) :
    _root_.Transfer.public_transfer t obj recipient world __ghost_178 __ghost_179
      = _root_.Transfer.transfer_impl__ghost t obj recipient world
          __ghost_178 __ghost_179 := rfl

/-- Transition face at the generated head (citation-only convenience). -/
theorem transfer_public_transfer_world_owned
    {Ev Df Be ObjU : Type} [Universe ObjU]
    (t : Type) [DecidableEq t] [Inhabited t]
    [HasCode ObjU t] [_root_.Object.HasObjectId t]
    (obj : t) (recipient : Address)
    (world : _root_.Prover.World.World Ev (_root_.Bag.Entry ObjU) Df Be)
    (__ghost_178 : Address) (__ghost_179 : Bool) :
    (_root_.Transfer.public_transfer t obj recipient world
        __ghost_178 __ghost_179).1.owned
      = world.owned ++ [(recipient,
          _root_.Object.uidKey (_root_.Object.HasObjectId.uid obj),
          _root_.Transfer.Object.toEntry t obj)] := rfl

/-- Commit-record face at the generated head (citation-only convenience). -/
theorem transfer_public_transfer_world_tx_created
    {Ev Df Be ObjU : Type} [Universe ObjU]
    (t : Type) [DecidableEq t] [Inhabited t]
    [HasCode ObjU t] [_root_.Object.HasObjectId t]
    (obj : t) (recipient : Address)
    (world : _root_.Prover.World.World Ev (_root_.Bag.Entry ObjU) Df Be)
    (__ghost_178 : Address) (__ghost_179 : Bool) :
    (_root_.Transfer.public_transfer t obj recipient world
        __ghost_178 __ghost_179).1.tx_created
      = world.tx_created
          ++ [_root_.Object.uidKey (_root_.Object.HasObjectId.uid obj)] := rfl

/-- Ghost-write faces at the generated head (citation-only). -/
theorem transfer_public_transfer_addr
    {Ev Df Be ObjU : Type} [Universe ObjU]
    (t : Type) [DecidableEq t] [Inhabited t]
    [HasCode ObjU t] [_root_.Object.HasObjectId t]
    (obj : t) (recipient : Address)
    (world : _root_.Prover.World.World Ev (_root_.Bag.Entry ObjU) Df Be)
    (__ghost_178 : Address) (__ghost_179 : Bool) :
    (_root_.Transfer.public_transfer t obj recipient world
        __ghost_178 __ghost_179).2.1 = recipient := rfl

theorem transfer_public_transfer_exists
    {Ev Df Be ObjU : Type} [Universe ObjU]
    (t : Type) [DecidableEq t] [Inhabited t]
    [HasCode ObjU t] [_root_.Object.HasObjectId t]
    (obj : t) (recipient : Address)
    (world : _root_.Prover.World.World Ev (_root_.Bag.Entry ObjU) Df Be)
    (__ghost_178 : Address) (__ghost_179 : Bool) :
    (_root_.Transfer.public_transfer t obj recipient world
        __ghost_178 __ghost_179).2.2 = true := rfl
