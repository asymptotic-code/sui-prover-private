-- World v2 — the unified two-store state model (unified-backend design §3).
--
-- One threaded `World` value replaces the accreted per-case state
-- mechanisms (ghost `dynamic_fields` slots, transfer ghost markers,
-- Versioned monomorphization, opaque df stubs). Phase 0 lands the data
-- model, the typed-view API and its round-trip laws; the threading pass
-- (Phase 1) is what makes generated code consume it.
--
-- Two association stores:
--   * `objects` — object store keyed by uid (low-64 nat hash model),
--     each record carrying an `Ownership` and a typed value.
--   * `df` — dynamic fields keyed by first-class `DfKey` (parent uid +
--     typed key), values `DfVal.plain` (a DfU universe value) or
--     `DfVal.bag` (an inline bag: a Bag cannot be a member of its own
--     universe, so bags stored under dynamic fields are represented
--     structurally — this retires the bag-containing-df exclusion).
--
-- Heterogeneity is quarantined: `Entry`, `▸`, `dite`-on-codes and
-- `HasCode.proof` appear only inside the bodies and proofs of this file
-- (and `Generated/*Interp.lean` instances, all `rfl`). Generated code and
-- client proofs only ever see the typed views (`getDf`/`setDf`/...) and
-- the `@[world_simp]` round-trip laws.
--
-- Representation note: association lists, not finmaps — with local
-- `assocGet`/`assocSet`/`assocErase` and laws we control. The
-- representation hides behind the typed-view API and can be swapped
-- later without touching client proofs.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.Universe
import Prelude.WorldSimp

namespace Prover.World

-- ---------------------------------------------------------------------------
-- Association-list primitives.
-- ---------------------------------------------------------------------------

def assocGet {κ ν : Type} [DecidableEq κ] (l : List (κ × ν)) (k : κ) : Option ν :=
  match l with
  | [] => none
  | (k', v) :: rest => if k' = k then some v else assocGet rest k

def assocErase {κ ν : Type} [DecidableEq κ] (l : List (κ × ν)) (k : κ) :
    List (κ × ν) :=
  match l with
  | [] => []
  | (k', v) :: rest =>
    if k' = k then assocErase rest k else (k', v) :: assocErase rest k

def assocSet {κ ν : Type} [DecidableEq κ] (l : List (κ × ν)) (k : κ) (v : ν) :
    List (κ × ν) :=
  (k, v) :: assocErase l k

theorem assocGet_erase_eq {κ ν : Type} [DecidableEq κ] (l : List (κ × ν)) (k : κ) :
    assocGet (assocErase l k) k = none := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k', v⟩ := hd
    by_cases h : k' = k
    · simp [assocErase, h, ih]
    · simp [assocErase, assocGet, h, ih]

theorem assocGet_erase_ne {κ ν : Type} [DecidableEq κ] (l : List (κ × ν))
    {k k' : κ} (h : k ≠ k') : assocGet (assocErase l k) k' = assocGet l k' := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k0, v⟩ := hd
    by_cases h0 : k0 = k
    · subst h0
      simp [assocErase, assocGet, h, ih]
    · simp [assocErase, assocGet, h0, ih]

theorem assocGet_set_eq {κ ν : Type} [DecidableEq κ] (l : List (κ × ν))
    (k : κ) (v : ν) : assocGet (assocSet l k v) k = some v := by
  simp [assocSet, assocGet]

theorem assocGet_set_ne {κ ν : Type} [DecidableEq κ] (l : List (κ × ν))
    {k k' : κ} (v : ν) (h : k ≠ k') :
    assocGet (assocSet l k v) k' = assocGet l k' := by
  simp only [assocSet, assocGet, if_neg h]
  exact assocGet_erase_ne l h

-- ---------------------------------------------------------------------------
-- Typed key/value entries (the kc/k and vc/v halves of `Entry`, split so the
-- frame-lemma key type `DfKey` is first-class and `DecidableEq`, and value
-- records carry no dead key slot).
-- ---------------------------------------------------------------------------

structure KeyEntry (U : Type) [Universe U] where
  kc : U
  k  : Universe.interp kc

/-- The one sanctioned, cast-free coercion into a key entry. -/
def KeyEntry.of {U : Type} [Universe U] {K : Type} [hk : HasCode U K]
    (k : K) : KeyEntry U :=
  ⟨hk.code, hk.proof.symm ▸ k⟩

instance {U : Type} [Universe U] : DecidableEq (KeyEntry U) := fun e1 e2 => by
  cases e1 with | mk kc1 k1 =>
  cases e2 with | mk kc2 k2 =>
  cases Universe.decEq kc1 kc2 with
  | isFalse h => exact isFalse (fun he => by cases he; exact h rfl)
  | isTrue h =>
    subst h
    cases Universe.decEqInterp kc1 k1 k2 with
    | isFalse hk => exact isFalse (fun he => by cases he; exact hk rfl)
    | isTrue hk => subst hk; exact isTrue rfl

theorem KeyEntry.of_inj {U : Type} [Universe U] {K : Type} [HasCode U K]
    {k k' : K} (h : k ≠ k') :
    KeyEntry.of (U := U) k ≠ KeyEntry.of (U := U) k' := by
  intro he
  apply h
  have h2 := (KeyEntry.mk.injEq _ _ _ _).mp he
  exact cast_inj (HasCode.proof (U := U) (T := K)) (eq_of_heq h2.2)

structure ValEntry (U : Type) [Universe U] where
  vc : U
  v  : Universe.interp vc

def ValEntry.of {U : Type} [Universe U] {V : Type} [hv : HasCode U V]
    (v : V) : ValEntry U :=
  ⟨hv.code, hv.proof.symm ▸ v⟩

/-- Typed read of a value entry: `some` exactly when the stored code is the
requested type's code. The honest wrong-type-read-is-none semantics. -/
def ValEntry.get? {U : Type} [Universe U] (V : Type) [hv : HasCode U V]
    (e : ValEntry U) : Option V :=
  if h : e.vc = hv.code then some (hv.proof ▸ h ▸ e.v) else none

theorem ValEntry.get?_of_eq {U : Type} [Universe U] {V : Type} [hv : HasCode U V]
    (v : V) : (ValEntry.of (U := U) v).get? V = some v := by
  unfold ValEntry.of ValEntry.get?
  rw [dif_pos rfl]
  exact congrArg some (cast_symm_cancel hv.proof v)

theorem ValEntry.get?_of_wrongType {U : Type} [Universe U] {V V' : Type}
    [hv : HasCode U V] [hv' : HasCode U V']
    (h : Universe.codeOf U V ≠ Universe.codeOf U V') (v : V) :
    (ValEntry.of (U := U) v).get? V' = none := by
  unfold ValEntry.of ValEntry.get?
  exact dif_neg h

-- ---------------------------------------------------------------------------
-- The World type.
-- ---------------------------------------------------------------------------

inductive Ownership where
  | owned    (recipient : Address)
  | shared
  | frozen
  | received (from_ : Address)
deriving BEq

/-- Object-store record: object values live in the Df universe
(`key`-ability structs are always universe members). -/
structure ObjRecord (DfU : Type) [Universe DfU] where
  own : Ownership
  val : ValEntry DfU

/-- Dynamic-field key: parent uid (low-64 nat, existing hash model) plus the
typed key entry. -/
structure DfKey (DfU : Type) [Universe DfU] where
  parent : Nat
  key    : KeyEntry DfU
deriving DecidableEq

/-- A df value is a plain universe value or an inline bag (a Bag cannot be a
member of its own universe). Replaces parallel df/bag/df-bag lists — and the
bag-containing-df exclusion class. -/
inductive DfVal (DfU BagU : Type) [Universe DfU] [Universe BagU] where
  | plain (v : ValEntry DfU)
  | bag   (id : Address) (size : BoundedNat (2^64)) (storage : List (Entry BagU))

structure World (Event : Type) (DfU BagU : Type)
    [Universe DfU] [Universe BagU] where
  events         : List Event
  objects        : List (Nat × ObjRecord DfU)
  deleted        : List Nat
  df             : List (DfKey DfU × DfVal DfU BagU)
  tx_created     : List Nat
  tx_user_events : BoundedNat (2^64)
  gas_used       : Nat
  -- Transfer-marker slots (the World-resident replacement for the retired
  -- `__ghost_SpecTransferAddress{,Exists}` spec-ghost threading): `putOwned`
  -- records that an owned transfer happened and to whom. Initial values are
  -- whatever the incoming `__world` carries — havoc'd at spec boundaries,
  -- exactly the old ghost-slot initial-value semantics.
  transfer_exists : Bool
  last_transfer   : Address

variable {Event DfU BagU : Type} [Universe DfU] [Universe BagU]

-- The empty world. Needed so world-threaded return types `(T × World)` (and
-- their tuples) are `Inhabited` — the generated `default`/`sorry` fallbacks on
-- unmodeled branches require it (world-mode `Validator_cap`, `Table_vec`).
instance : Inhabited (World Event DfU BagU) where
  default :=
    { events := [], objects := [], deleted := [], df := [], tx_created := [],
      tx_user_events := default, gas_used := 0, transfer_exists := false,
      last_transfer := default }

/-- The initial (empty) world a per-test driver threads into a world-mode
`<fn>.aborts (__world : World)`. -/
def World.init : World Event DfU BagU := default

-- ---------------------------------------------------------------------------
-- Typed-view API — the cast quarantine. All heterogeneous access in generated
-- code and contract lemmas goes through these.
-- ---------------------------------------------------------------------------

def World.getDf {K V : Type} [HasCode DfU K] [HasCode DfU V]
    (w : World Event DfU BagU) (parent : Nat) (k : K) : Option V :=
  match assocGet w.df ⟨parent, KeyEntry.of k⟩ with
  | some (.plain e) => e.get? V
  | some (.bag _ _ _) => none
  | none => none

def World.setDf {K V : Type} [HasCode DfU K] [HasCode DfU V]
    (w : World Event DfU BagU) (parent : Nat) (k : K) (v : V) :
    World Event DfU BagU :=
  { w with df := assocSet w.df ⟨parent, KeyEntry.of k⟩ (.plain (ValEntry.of v)) }

def World.eraseDf {K : Type} [HasCode DfU K]
    (w : World Event DfU BagU) (parent : Nat) (k : K) : World Event DfU BagU :=
  { w with df := assocErase w.df ⟨parent, KeyEntry.of k⟩ }

def World.hasDf {K : Type} [HasCode DfU K]
    (w : World Event DfU BagU) (parent : Nat) (k : K) : Bool :=
  (assocGet w.df ⟨parent, KeyEntry.of k⟩).isSome

-- Structural bag-df views: a `bag::Bag` value cannot be a `DfU` universe
-- member (a bag can't live in its own universe), so it is stored in the
-- `DfVal.bag` arm as its raw parts (`id`, `size`, `storage`) rather than
-- through the `HasCode`-constrained typed views. The per-project
-- `Generated/World.lean` wrappers reconstruct the `Bag` struct from these.
def World.setDfBag {K : Type} [HasCode DfU K]
    (w : World Event DfU BagU) (parent : Nat) (k : K)
    (id : Address) (size : BoundedNat (2^64)) (storage : List (Entry BagU)) :
    World Event DfU BagU :=
  { w with df := assocSet w.df ⟨parent, KeyEntry.of k⟩ (.bag id size storage) }

def World.getDfBagParts {K : Type} [HasCode DfU K]
    (w : World Event DfU BagU) (parent : Nat) (k : K) :
    Option (Address × BoundedNat (2^64) × List (Entry BagU)) :=
  match assocGet w.df ⟨parent, KeyEntry.of k⟩ with
  | some (.bag id size storage) => some (id, size, storage)
  | _ => none

def World.hasDfBag {K : Type} [HasCode DfU K]
    (w : World Event DfU BagU) (parent : Nat) (k : K) : Bool :=
  match assocGet w.df ⟨parent, KeyEntry.of k⟩ with
  | some (.bag _ _ _) => true
  | _ => false

def World.dfKeys (w : World Event DfU BagU) : List (DfKey DfU) :=
  w.df.map (·.1)

def World.putObj {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (own : Ownership) (uid : Nat) (x : T) :
    World Event DfU BagU :=
  { w with objects := assocSet w.objects uid ⟨own, ValEntry.of x⟩ }

def World.putOwned {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (recipient : Address) (uid : Nat) (x : T) :
    World Event DfU BagU :=
  { w.putObj (.owned recipient) uid x with
    transfer_exists := true, last_transfer := recipient }

def World.putShared {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (uid : Nat) (x : T) : World Event DfU BagU :=
  w.putObj .shared uid x

def World.putFrozen {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (uid : Nat) (x : T) : World Event DfU BagU :=
  w.putObj .frozen uid x

def World.getObj (T : Type) [HasCode DfU T]
    (w : World Event DfU BagU) (uid : Nat) : Option T :=
  match assocGet w.objects uid with
  | some r => r.val.get? T
  | none => none

def World.getOwner (w : World Event DfU BagU) (uid : Nat) : Option Ownership :=
  (assocGet w.objects uid).map (·.own)

def World.transferExists (w : World Event DfU BagU) : Bool := w.transfer_exists

def World.lastTransfer (w : World Event DfU BagU) : Address := w.last_transfer

def World.delete (w : World Event DfU BagU) (uid : Nat) : World Event DfU BagU :=
  { w with objects := assocErase w.objects uid, deleted := w.deleted ++ [uid] }

-- ---------------------------------------------------------------------------
-- Owner-indexed reads — the `test_scenario` inventory API. `putOwned`
-- prepends (via `assocSet`), so the object store is most-recent-first; owner
-- scans preserve that order (`most_recent_*` = first match).
-- ---------------------------------------------------------------------------

/-- uids of objects currently owned by `owner`, INSERTION order (oldest
first) — the Move VM stores per-address inventories as an IndexSet, and
`ids_for_address` enumerates it in insertion order. The objects list is
newest-first (putOwned prepends), so reverse the scan. Backs
`test_scenario::ids_for_address`. -/
def World.uidsOwnedBy (w : World Event DfU BagU) (owner : Address) : List Nat :=
  (w.objects.filterMap (fun (p : Nat × ObjRecord DfU) =>
    match p.2.own with
    | .owned r => if r == owner then some p.1 else none
    | _ => none)).reverse

/-- The uid of the most-recently-transferred object owned by `owner`, if any.
Backs `test_scenario::most_recent_id_for_address`. -/
def World.mostRecentOwnedBy (w : World Event DfU BagU) (owner : Address) : Option Nat :=
  (w.uidsOwnedBy owner).getLast?

/-- Whether `uid` is currently owned by `owner` (i.e. still takeable). Backs
`test_scenario::was_taken_from_address` (post-take the object is `delete`d, so
this reflects presence). -/
def World.ownedBy (w : World Event DfU BagU) (owner : Address) (uid : Nat) : Bool :=
  match w.getOwner uid with
  | some (.owned r) => r == owner
  | _ => false

/-- uids of currently-shared objects whose value has type `T`, most-recent
first. Type-filtered (unlike the owner-keyed scans) because distinct shared
singletons of different types coexist in one scenario. Backs
`test_scenario::most_recent_id_shared`. -/
def World.sharedUids (T : Type) [HasCode DfU T]
    (w : World Event DfU BagU) : List Nat :=
  w.objects.filterMap (fun (p : Nat × ObjRecord DfU) =>
    match p.2.own with
    | .shared => if (p.2.val.get? T).isSome then some p.1 else none
    | _ => none)

/-- The uid of the most-recently-shared object of type `T`, if any. -/
def World.mostRecentShared (T : Type) [HasCode DfU T]
    (w : World Event DfU BagU) : Option Nat :=
  (w.sharedUids T).head?

/-- uids of objects of type `T` currently owned by `owner`, most-recent
first. The typed variant of `uidsOwnedBy`: `take_from_sender<T>` must not
select an object of another type the sender also owns (a Coin ahead of the
requested StakedSui), or `takeObj T` type-misses into the default. -/
def World.uidsOwnedByT (T : Type) [HasCode DfU T]
    (w : World Event DfU BagU) (owner : Address) : List Nat :=
  (w.objects.filterMap (fun (p : Nat × ObjRecord DfU) =>
    match p.2.own with
    | .owned r => if r == owner && (p.2.val.get? T).isSome then some p.1 else none
    | _ => none)).reverse

/-- The uid of the most-recently-transferred `T` owned by `owner`, if any. -/
def World.mostRecentOwnedByT (T : Type) [HasCode DfU T]
    (w : World Event DfU BagU) (owner : Address) : Option Nat :=
  (w.uidsOwnedByT T owner).getLast?

/-- Whether `uid` is currently shared (still takeable via
`take_shared_by_id`; post-take the record is `delete`d). -/
def World.isShared (w : World Event DfU BagU) (uid : Nat) : Bool :=
  match w.getOwner uid with
  | some .shared => true
  | _ => false

/-- Take an owned object out of the store: its typed value plus the world with
that uid removed. Backs `test_scenario::take_from_address_by_id`. Returns the
`Inhabited` default (never reached on well-formed tests, which only take ids
`ids_for_address` returned) when the object is absent or mistyped. -/
def World.takeObj (T : Type) [HasCode DfU T] [Inhabited T]
    (w : World Event DfU BagU) (uid : Nat) : T × World Event DfU BagU :=
  (((w.getObj T uid).getD default), w.delete uid)

/-- `transfer::receive`: the typed read + removal of a received object. -/
def World.takeReceived (T : Type) [HasCode DfU T]
    (w : World Event DfU BagU) (uid : Nat) :
    Option T × World Event DfU BagU :=
  (w.getObj T uid, w.delete uid)

/-- `event::emit`: appends the event and bumps the tx event counter. -/
def World.emit (w : World Event DfU BagU) (e : Event) : World Event DfU BagU :=
  { w with events := w.events ++ [e], tx_user_events := w.tx_user_events + 1 }

/-- `test_scenario::end_transaction`: reads the per-tx user-event count and
resets it to 0 — the counter is per-transaction, and tests run multiple
`next_tx`/`next_epoch` cycles, so it must not accumulate across them. -/
def World.takeTxUserEvents (w : World Event DfU BagU) :
    BoundedNat (2^64) × World Event DfU BagU :=
  (w.tx_user_events, { w with tx_user_events := 0 })

-- ---------------------------------------------------------------------------
-- Round-trip laws (`@[world_simp]`) — proven once; the only place transport
-- collapse is ever reasoned about.
-- ---------------------------------------------------------------------------

@[world_simp] theorem getDf_setDf_eq {K V : Type} [HasCode DfU K] [HasCode DfU V]
    (w : World Event DfU BagU) (p : Nat) (k : K) (v : V) :
    (w.setDf p k v).getDf p k = some v := by
  unfold World.getDf World.setDf
  simp only [assocGet_set_eq]
  exact ValEntry.get?_of_eq v

@[world_simp] theorem getDf_setDf_ne {K K' V V' : Type}
    [HasCode DfU K] [HasCode DfU V] [HasCode DfU K'] [HasCode DfU V']
    (w : World Event DfU BagU) {p p' : Nat} {k : K} {k' : K'} (v : V)
    (h : DfKey.mk (DfU := DfU) p (.of k) ≠ DfKey.mk p' (.of k')) :
    (w.setDf p k v).getDf p' k' = (w.getDf p' k' : Option V') := by
  unfold World.getDf World.setDf
  rw [assocGet_set_ne _ _ h]

/-- The honest wrong-type-read law: writing at `V` and reading at `V'` with a
different code yields `none` — observably, not via a generation-time error. -/
@[world_simp] theorem getDf_setDf_wrongType {K V V' : Type}
    [HasCode DfU K] [HasCode DfU V] [HasCode DfU V']
    (w : World Event DfU BagU) (p : Nat) (k : K) (v : V)
    (h : Universe.codeOf DfU V ≠ Universe.codeOf DfU V') :
    ((w.setDf p k v).getDf p k : Option V') = none := by
  unfold World.getDf World.setDf
  simp only [assocGet_set_eq]
  exact ValEntry.get?_of_wrongType h v

@[world_simp] theorem getDf_eraseDf_eq {K V : Type}
    [HasCode DfU K] [HasCode DfU V]
    (w : World Event DfU BagU) (p : Nat) (k : K) :
    ((w.eraseDf p k).getDf p k : Option V) = none := by
  unfold World.getDf World.eraseDf
  rw [assocGet_erase_eq]

@[world_simp] theorem getDf_eraseDf_ne {K K' V' : Type}
    [HasCode DfU K] [HasCode DfU K'] [HasCode DfU V']
    (w : World Event DfU BagU) {p p' : Nat} {k : K} {k' : K'}
    (h : DfKey.mk (DfU := DfU) p (.of k) ≠ DfKey.mk p' (.of k')) :
    ((w.eraseDf p k).getDf p' k' : Option V') = w.getDf p' k' := by
  unfold World.getDf World.eraseDf
  rw [assocGet_erase_ne _ h]

@[world_simp] theorem hasDf_setDf_eq {K V : Type} [HasCode DfU K] [HasCode DfU V]
    (w : World Event DfU BagU) (p : Nat) (k : K) (v : V) :
    (w.setDf p k v).hasDf p k = true := by
  unfold World.hasDf World.setDf
  simp [assocGet_set_eq]

@[world_simp] theorem hasDf_setDf_ne {K K' V : Type}
    [HasCode DfU K] [HasCode DfU V] [HasCode DfU K']
    (w : World Event DfU BagU) {p p' : Nat} {k : K} {k' : K'} (v : V)
    (h : DfKey.mk (DfU := DfU) p (.of k) ≠ DfKey.mk p' (.of k')) :
    (w.setDf p k v).hasDf p' k' = w.hasDf p' k' := by
  unfold World.hasDf World.setDf
  rw [assocGet_set_ne _ _ h]

@[world_simp] theorem hasDf_eraseDf_eq {K : Type} [HasCode DfU K]
    (w : World Event DfU BagU) (p : Nat) (k : K) :
    (w.eraseDf p k).hasDf p k = false := by
  unfold World.hasDf World.eraseDf
  simp [assocGet_erase_eq]

@[world_simp] theorem hasDf_eraseDf_ne {K K' : Type}
    [HasCode DfU K] [HasCode DfU K']
    (w : World Event DfU BagU) {p p' : Nat} {k : K} {k' : K'}
    (h : DfKey.mk (DfU := DfU) p (.of k) ≠ DfKey.mk p' (.of k')) :
    (w.eraseDf p k).hasDf p' k' = w.hasDf p' k' := by
  unfold World.hasDf World.eraseDf
  rw [assocGet_erase_ne _ h]

@[world_simp] theorem getObj_putObj_eq {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (own : Ownership) (uid : Nat) (x : T) :
    (w.putObj own uid x).getObj T uid = some x := by
  unfold World.getObj World.putObj
  simp only [assocGet_set_eq]
  exact ValEntry.get?_of_eq x

@[world_simp] theorem getObj_putObj_ne {T T' : Type} [HasCode DfU T] [HasCode DfU T']
    (w : World Event DfU BagU) (own : Ownership) {uid uid' : Nat} (x : T)
    (h : uid ≠ uid') :
    ((w.putObj own uid x).getObj T' uid' : Option T') = w.getObj T' uid' := by
  unfold World.getObj World.putObj
  rw [assocGet_set_ne _ _ h]

@[world_simp] theorem getObj_putObj_wrongType {T T' : Type}
    [HasCode DfU T] [HasCode DfU T']
    (w : World Event DfU BagU) (own : Ownership) (uid : Nat) (x : T)
    (h : Universe.codeOf DfU T ≠ Universe.codeOf DfU T') :
    ((w.putObj own uid x).getObj T' uid : Option T') = none := by
  unfold World.getObj World.putObj
  simp only [assocGet_set_eq]
  exact ValEntry.get?_of_wrongType h x

@[world_simp] theorem getObj_delete_eq {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (uid : Nat) :
    ((w.delete uid).getObj T uid : Option T) = none := by
  unfold World.getObj World.delete
  rw [assocGet_erase_eq]

@[world_simp] theorem getObj_delete_ne {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) {uid uid' : Nat} (h : uid ≠ uid') :
    ((w.delete uid).getObj T uid' : Option T) = w.getObj T uid' := by
  unfold World.getObj World.delete
  rw [assocGet_erase_ne _ h]

@[world_simp] theorem getOwner_putObj_eq {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (own : Ownership) (uid : Nat) (x : T) :
    (w.putObj own uid x).getOwner uid = some own := by
  unfold World.getOwner World.putObj
  simp [assocGet_set_eq]

@[world_simp] theorem emit_events (w : World Event DfU BagU) (e : Event) :
    (w.emit e).events = w.events ++ [e] := rfl

-- Cross-store frame primitives: each store op leaves the other stores alone.

@[world_simp] theorem setDf_objects {K V : Type} [HasCode DfU K] [HasCode DfU V]
    (w : World Event DfU BagU) (p : Nat) (k : K) (v : V) :
    (w.setDf p k v).objects = w.objects := rfl

@[world_simp] theorem setDf_events {K V : Type} [HasCode DfU K] [HasCode DfU V]
    (w : World Event DfU BagU) (p : Nat) (k : K) (v : V) :
    (w.setDf p k v).events = w.events := rfl

@[world_simp] theorem eraseDf_objects {K : Type} [HasCode DfU K]
    (w : World Event DfU BagU) (p : Nat) (k : K) :
    (w.eraseDf p k).objects = w.objects := rfl

@[world_simp] theorem eraseDf_events {K : Type} [HasCode DfU K]
    (w : World Event DfU BagU) (p : Nat) (k : K) :
    (w.eraseDf p k).events = w.events := rfl

@[world_simp] theorem putObj_df {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (own : Ownership) (uid : Nat) (x : T) :
    (w.putObj own uid x).df = w.df := rfl

@[world_simp] theorem putObj_events {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (own : Ownership) (uid : Nat) (x : T) :
    (w.putObj own uid x).events = w.events := rfl

@[world_simp] theorem emit_df (w : World Event DfU BagU) (e : Event) :
    (w.emit e).df = w.df := rfl

-- Transfer-marker laws: `putOwned` stamps the slots, every other store op
-- leaves them alone.

@[world_simp] theorem transferExists_putOwned {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (r : Address) (uid : Nat) (x : T) :
    (w.putOwned r uid x).transferExists = true := rfl

@[world_simp] theorem lastTransfer_putOwned {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (r : Address) (uid : Nat) (x : T) :
    (w.putOwned r uid x).lastTransfer = r := rfl

@[world_simp] theorem transferExists_setDf {K V : Type} [HasCode DfU K] [HasCode DfU V]
    (w : World Event DfU BagU) (p : Nat) (k : K) (v : V) :
    (w.setDf p k v).transferExists = w.transferExists := rfl

@[world_simp] theorem lastTransfer_setDf {K V : Type} [HasCode DfU K] [HasCode DfU V]
    (w : World Event DfU BagU) (p : Nat) (k : K) (v : V) :
    (w.setDf p k v).lastTransfer = w.lastTransfer := rfl

@[world_simp] theorem transferExists_eraseDf {K : Type} [HasCode DfU K]
    (w : World Event DfU BagU) (p : Nat) (k : K) :
    (w.eraseDf p k).transferExists = w.transferExists := rfl

@[world_simp] theorem lastTransfer_eraseDf {K : Type} [HasCode DfU K]
    (w : World Event DfU BagU) (p : Nat) (k : K) :
    (w.eraseDf p k).lastTransfer = w.lastTransfer := rfl

@[world_simp] theorem transferExists_putObj {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (own : Ownership) (uid : Nat) (x : T) :
    (w.putObj own uid x).transferExists = w.transferExists := rfl

@[world_simp] theorem lastTransfer_putObj {T : Type} [HasCode DfU T]
    (w : World Event DfU BagU) (own : Ownership) (uid : Nat) (x : T) :
    (w.putObj own uid x).lastTransfer = w.lastTransfer := rfl

@[world_simp] theorem transferExists_emit (w : World Event DfU BagU) (e : Event) :
    (w.emit e).transferExists = w.transferExists := rfl

@[world_simp] theorem lastTransfer_emit (w : World Event DfU BagU) (e : Event) :
    (w.emit e).lastTransfer = w.lastTransfer := rfl

@[world_simp] theorem transferExists_delete (w : World Event DfU BagU) (uid : Nat) :
    (w.delete uid).transferExists = w.transferExists := rfl

@[world_simp] theorem lastTransfer_delete (w : World Event DfU BagU) (uid : Nat) :
    (w.delete uid).lastTransfer = w.lastTransfer := rfl

@[world_simp] theorem emit_objects (w : World Event DfU BagU) (e : Event) :
    (w.emit e).objects = w.objects := rfl

-- ---------------------------------------------------------------------------
-- Df-store frame vocabulary (unified-backend design §5.4, Phase 4).
--
-- `FrameDf w w' S` says `w'` agrees with `w` on every dynamic field whose key
-- lies outside the footprint `S`. Generated per-function frame theorems
-- (`<fn>.frame_thm : FrameDf __world ((<fn> … __world).world) (<fn>.dfFootprint …)`)
-- are combinator trees over the leaves below: one leaf per store op
-- (`FrameDf.setDf` / `FrameDf.eraseDf`, reached through the per-project
-- `World.frame_setDf` / `World.frame_eraseDf` wrappers), `FrameDf.step_df_eq`
-- for df-preserving ops (transfer/emit, `rfl` side condition), the callee's
-- own `frame_thm` at call sites (footprints compose by substitution), and
-- `FrameDf.comp` / `FrameDf.bite` / `FrameDf.ite_pair` for sequencing and
-- branches. The user-facing corollary is `<fn>.frame_df_out`.
-- ---------------------------------------------------------------------------

def FrameDf (w w' : World Event DfU BagU) (S : List (DfKey DfU)) : Prop :=
  ∀ {K V : Type} [HasCode DfU K] [HasCode DfU V] (p : Nat) (k : K),
    DfKey.mk p (KeyEntry.of k) ∉ S → (w'.getDf p k : Option V) = w.getDf p k

theorem FrameDf.refl {S : List (DfKey DfU)} (w : World Event DfU BagU) :
    FrameDf w w S := by
  intro K V _ _ p k _
  rfl

theorem FrameDf.mono {w w' : World Event DfU BagU} {S S' : List (DfKey DfU)}
    (hs : ∀ x, x ∈ S → x ∈ S') (h : FrameDf w w' S) : FrameDf w w' S' := by
  intro K V _ _ p k hn
  exact h p k (fun m => hn (hs _ m))

theorem FrameDf.comp {w w' w'' : World Event DfU BagU} {S S' : List (DfKey DfU)}
    (h1 : FrameDf w w' S) (h2 : FrameDf w' w'' S') : FrameDf w w'' (S ++ S') := by
  intro K V _ _ p k hn
  rw [h2 p k (fun m => hn (List.mem_append.mpr (Or.inr m))),
      h1 p k (fun m => hn (List.mem_append.mpr (Or.inl m)))]

theorem FrameDf.setDf {K V : Type} [HasCode DfU K] [HasCode DfU V]
    (w : World Event DfU BagU) (p : Nat) (k : K) (v : V) :
    FrameDf w (w.setDf p k v) [DfKey.mk p (KeyEntry.of k)] := by
  intro K' V' _ _ p' k' hn
  exact getDf_setDf_ne w v (fun he => hn (List.mem_singleton.mpr he.symm))

theorem FrameDf.eraseDf {K : Type} [HasCode DfU K]
    (w : World Event DfU BagU) (p : Nat) (k : K) :
    FrameDf w (w.eraseDf p k) [DfKey.mk p (KeyEntry.of k)] := by
  intro K' V' _ _ p' k' hn
  exact getDf_eraseDf_ne w (fun he => hn (List.mem_singleton.mpr he.symm))

/-- Df-preserving step (transfer / emit / delete): `w''` is one op past `w'`
that leaves the df store untouched (`he` is `rfl` at every generated use). -/
theorem FrameDf.step_df_eq {w w' : World Event DfU BagU} {S : List (DfKey DfU)}
    (w'' : World Event DfU BagU) (h : FrameDf w w' S) (he : w''.df = w'.df) :
    FrameDf w w'' S := by
  intro K V _ _ p k hn
  have hw : (w''.getDf p k : Option V) = w'.getDf p k := by
    unfold World.getDf
    rw [he]
  rw [hw]
  exact h p k hn

theorem FrameDf.bite {w : World Event DfU BagU} {S S' : List (DfKey DfU)}
    {c : Prop} [Decidable c] {w1 w2 : World Event DfU BagU}
    (h1 : FrameDf w w1 S) (h2 : FrameDf w w2 S') :
    FrameDf w (if c then w1 else w2) (S ++ S') := by
  by_cases hc : c
  · rw [if_pos hc]
    exact FrameDf.mono (fun x m => List.mem_append.mpr (Or.inl m)) h1
  · rw [if_neg hc]
    exact FrameDf.mono (fun x m => List.mem_append.mpr (Or.inr m)) h2

/-- Branch combinator for value faces: the world is the second component of a
result pair, so the split happens under the projection. -/
theorem FrameDf.ite_pair {α : Type} {w : World Event DfU BagU}
    {S S' : List (DfKey DfU)} {c : Prop} [Decidable c]
    {a b : α × World Event DfU BagU}
    (h1 : FrameDf w a.2 S) (h2 : FrameDf w b.2 S') :
    FrameDf w (if c then a else b).2 (S ++ S') := by
  by_cases hc : c
  · rw [if_pos hc]
    exact FrameDf.mono (fun x m => List.mem_append.mpr (Or.inl m)) h1
  · rw [if_neg hc]
    exact FrameDf.mono (fun x m => List.mem_append.mpr (Or.inr m)) h2

-- ---------------------------------------------------------------------------
-- Df-store invariants (unified-backend design §7, Phase 5).
--
-- `w.allDf p P` says every dynamic field stored under parent `p` that reads
-- at the predicate's value type satisfies `P`. The definition quantifies over
-- typed READS (not raw store membership), so wrong-typed and bag entries are
-- vacuously covered, and the lever lemmas below never touch `Entry` /
-- transport internals. Generated hypotheses are
-- `hdinv : w.allDf parent <pred>`; preservation goals conclude
-- `((F … w).world).allDf parent <pred>` and are discharged from
-- `allDf_setDf` / `allDf_eraseDf` at write sites and `allDf_of_frame`
-- (through the per-function `frame_thm`) everywhere else.
-- ---------------------------------------------------------------------------

/-- Cross-key-type read-after-write: when the written and read `DfKey`s agree
(possibly at different key TYPES), the read is the typed view of the written
entry. The `DfKey`-equality premise form is what `allDf` case splits produce. -/
theorem getDf_setDf_eq' {K K' V V' : Type}
    [HasCode DfU K] [HasCode DfU K'] [HasCode DfU V] [HasCode DfU V']
    (w : World Event DfU BagU) {p p' : Nat} {k : K} {k' : K'} (v : V)
    (he : DfKey.mk (DfU := DfU) p (KeyEntry.of k) = DfKey.mk p' (KeyEntry.of k')) :
    ((w.setDf p k v).getDf p' k' : Option V') = (ValEntry.of (U := DfU) v).get? V' := by
  unfold World.getDf World.setDf
  rw [← he, assocGet_set_eq]

/-- Cross-key-type read-after-erase at an agreeing `DfKey`: `none`. -/
theorem getDf_eraseDf_eq' {K K' V' : Type}
    [HasCode DfU K] [HasCode DfU K'] [HasCode DfU V']
    (w : World Event DfU BagU) {p p' : Nat} {k : K} {k' : K'}
    (he : DfKey.mk (DfU := DfU) p (KeyEntry.of k) = DfKey.mk p' (KeyEntry.of k')) :
    ((w.eraseDf p k).getDf p' k' : Option V') = none := by
  unfold World.getDf World.eraseDf
  rw [← he, assocGet_erase_eq]

def World.allDf {V : Type} [HasCode DfU V]
    (w : World Event DfU BagU) (parent : Nat) (P : V → Prop) : Prop :=
  ∀ (K : Type) [HasCode DfU K] (k : K) (v : V),
    w.getDf parent k = some v → P v

/-- The read lever: an invariant on parent `p` transfers to every successful
typed read under `p`. -/
theorem World.get_of_allDf {K V : Type} [HasCode DfU K] [HasCode DfU V]
    {w : World Event DfU BagU} {p : Nat} {P : V → Prop} {k : K} {v : V}
    (h : w.allDf p P) (hg : w.getDf p k = some v) : P v :=
  h K k v hg

/-- The write lever: storing a value that satisfies the invariant preserves
`allDf` on that parent. -/
theorem World.allDf_setDf {K V : Type} [HasCode DfU K] [HasCode DfU V]
    {w : World Event DfU BagU} {p : Nat} {P : V → Prop} {k : K} {v : V}
    (hv : P v) (h : w.allDf p P) : (w.setDf p k v).allDf p P := by
  intro K' _ k' v' hg
  by_cases he : DfKey.mk (DfU := DfU) p (KeyEntry.of k) = DfKey.mk p (KeyEntry.of k')
  · rw [getDf_setDf_eq' w v he, ValEntry.get?_of_eq] at hg
    cases hg
    exact hv
  · rw [getDf_setDf_ne w v he] at hg
    exact h K' k' v' hg

/-- Writes at a DIFFERENT parent preserve `allDf` unconditionally. -/
theorem World.allDf_setDf_ne {K V V' : Type}
    [HasCode DfU K] [HasCode DfU V] [HasCode DfU V']
    {w : World Event DfU BagU} {p p' : Nat} {P : V → Prop} {k : K} {v : V'}
    (hp : p' ≠ p) (h : w.allDf p P) : (w.setDf p' k v).allDf p P := by
  intro K' _ k' v' hg
  rw [getDf_setDf_ne w v (fun he => hp (congrArg DfKey.parent he))] at hg
  exact h K' k' v' hg

/-- Erasure preserves `allDf` (it only removes constrained reads). -/
theorem World.allDf_eraseDf {K V : Type} [HasCode DfU K] [HasCode DfU V]
    {w : World Event DfU BagU} {p p' : Nat} {P : V → Prop} {k : K}
    (h : w.allDf p P) : (w.eraseDf p' k).allDf p P := by
  intro K' _ k' v' hg
  by_cases he : DfKey.mk (DfU := DfU) p' (KeyEntry.of k) = DfKey.mk p (KeyEntry.of k')
  · rw [getDf_eraseDf_eq' w he] at hg
    cases hg
  · rw [getDf_eraseDf_ne w he] at hg
    exact h K' k' v' hg

/-- The frame lever (§7 `allDf_frame`): an invariant on parent `p` survives
any function whose df footprint avoids `p` — via the generated `frame_thm`. -/
theorem World.allDf_of_frame {V : Type} [HasCode DfU V]
    {w w' : World Event DfU BagU} {S : List (DfKey DfU)} {p : Nat}
    {P : V → Prop} (hf : FrameDf w w' S) (hp : ∀ e ∈ S, e.parent ≠ p)
    (h : w.allDf p P) : w'.allDf p P := by
  intro K _ k v hg
  rw [hf p k (fun m => hp _ m rfl)] at hg
  exact h K k v hg

/-- Event emission never touches the df store. -/
theorem World.allDf_emit {V : Type} [HasCode DfU V]
    {w : World Event DfU BagU} {p : Nat} {P : V → Prop} (e : Event)
    (h : w.allDf p P) : (w.emit e).allDf p P := by
  intro K _ k v hg
  unfold World.getDf at hg
  exact h K k v hg

/-- Object-store and event ops never touch the df store, so `allDf` passes
through them; stated over a df-equality side condition (`rfl` at use sites),
mirroring `FrameDf.step_df_eq`. -/
theorem World.allDf_df_eq {V : Type} [HasCode DfU V]
    {w : World Event DfU BagU} (w' : World Event DfU BagU) {p : Nat}
    {P : V → Prop} (h : w.allDf p P) (he : w'.df = w.df) : w'.allDf p P := by
  intro K _ k v hg
  unfold World.getDf at hg
  rw [he] at hg
  exact h K k v hg

end Prover.World
