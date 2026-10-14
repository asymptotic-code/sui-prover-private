-- Typed Mutation prelude for Move's `&mut` references.
--
-- See `plans/lean-pipeline/mutable-references.md` for the design.
-- The prelude is **abstract over `Key`** -- the per-package generator
-- emits an `AnyKey` inductive that fills the parameter for each
-- translated package; the IR carries `MapKey { key_type, value_type }`
-- on borrow edges and the renderer wraps each runtime key in the
-- matching `AnyKey.k_<mangled>` constructor.
--
-- All operations are pure value-form. Path entries record the borrow
-- chain at runtime; writeback operations consume the innermost entry
-- to reconstruct the parent's new value. Runtime keys / indices are
-- recovered at runtime from the child's own path: the `writeBack*Last`
-- helpers read only the LAST path edge (the index/key of the borrow
-- being written back), so the path prefix -- arbitrary at non-root
-- call sites -- never affects writeback semantics.

import Prelude.Helpers

set_option linter.unusedVariables false

namespace Prover.Mutation

-- A mutation's location: where the borrow ultimately roots.
-- `global` is shared by frontends with explicit program globals.  Its
-- numeric payload is the renderer-stable `GlobalId`; the current global
-- value still travels in `Mutation.val`, exactly like local and parameter
-- roots.  The updated root is returned and threaded through calls as an
-- ordinary hidden mutable-reference parameter.
inductive Loc where
  | localRoot  (i : Nat)
  | param      (i : Nat)
  | global     (i : Nat)
  | specGlobal (tyArgs : List Nat)
  deriving DecidableEq, Repr

-- One step along a borrow path. Mirrors `crate::ir::BorrowEdge` 1:1.
-- The runtime payload for `vecIndex` is the index `Nat`; for `mapKey`
-- it is the key value wrapped in the per-package `AnyKey`-style type
-- supplied by the caller via the `Key` parameter.
inductive Edge (Key : Type) where
  | direct
  | structField (sid : Nat) (offset : Nat)
  | enumField   (sid : Nat) (variant : Nat) (offset : Nat)
  | vecIndex    (i : Nat)
  | mapKey      (k : Key)
  deriving BEq

-- A live mutable reference: location + path from that location + the
-- current value at that path. The field is named `val` so existing
-- legacy renderer code that emitted `r.val` for legacy `Mutable` values
-- continues to work syntactically against the typed prelude.
structure Mutation (Key : Type) (T : Type) where
  loc   : Loc
  path  : List (Edge Key)
  val   : T

-- Inhabited instances for the mutref types. `partial def` loop
-- helpers extracted by stage 7 require Lean to prove the helper's
-- return type is `Nonempty`. Without these, helpers that return
-- `(Mutation S × Mutation T)` (a common shape for `borrow_mut_*`
-- functions that bundle multiple mutable refs back into the
-- post-loop continuation) fail `partial def`'s nonemptiness
-- check.
instance : Inhabited Loc where default := .localRoot 0
instance {Key : Type} : Inhabited (Edge Key) where default := .direct
instance {Key : Type} {T : Type} [Inhabited T] : Inhabited (Mutation Key T) where
  default := { loc := default, path := [], val := default }

namespace Mutation

variable {Key : Type} {S T V : Type}

-- ---- Atoms ----

def deref (m : Mutation Key T) : T := m.val

def updateValue (m : Mutation Key T) (v : T) : Mutation Key T :=
  { m with val := v }

@[simp] theorem val_updateValue (m : Mutation Key T) (v : T) :
    (m.updateValue v).val = v := rfl

theorem path_updateValue (m : Mutation Key T) (v : T) :
    (m.updateValue v).path = m.path := rfl

theorem loc_updateValue (m : Mutation Key T) (v : T) :
    (m.updateValue v).loc = m.loc := rfl

-- Legacy alias: matches the spelling the renderer uses for value-form
-- writes (`Mutable.set r v` -> `Mutation.set r v`).
def set (m : Mutation Key T) (v : T) : Mutation Key T := updateValue m v

@[simp] theorem val_set (m : Mutation Key T) (v : T) :
    (m.set v).val = v := rfl

@[simp]
theorem path_set (m : Mutation Key T) (v : T) :
    (m.set v).path = m.path := rfl

@[simp]
theorem loc_set (m : Mutation Key T) (v : T) :
    (m.set v).loc = m.loc := rfl

-- ---- Borrow extensions ----

-- Materialise a fresh mutation rooted at a local. Used to lower
-- `Expr::BorrowLoc(x)` when `x` is a local variable.
def ofLocal (i : Nat) (v : T) : Mutation Key T :=
  { loc := .localRoot i, path := [], val := v }

@[simp] theorem val_ofLocal (i : Nat) (v : T) :
    (ofLocal (Key := Key) i v).val = v := rfl

@[simp] theorem path_ofLocal (i : Nat) (v : T) :
    (ofLocal (Key := Key) i v).path = [] := rfl

@[simp] theorem loc_ofLocal (i : Nat) (v : T) :
    (ofLocal (Key := Key) i v).loc = .localRoot i := rfl

-- Materialise a fresh mutation rooted at a parameter.
def ofParam (i : Nat) (v : T) : Mutation Key T :=
  { loc := .param i, path := [], val := v }

@[simp] theorem val_ofParam (i : Nat) (v : T) :
    (ofParam (Key := Key) i v).val = v := rfl

@[simp] theorem path_ofParam (i : Nat) (v : T) :
    (ofParam (Key := Key) i v).path = [] := rfl

@[simp] theorem loc_ofParam (i : Nat) (v : T) :
    (ofParam (Key := Key) i v).loc = .param i := rfl

-- Materialise a mutation rooted at a program global.  The boundary caller
-- supplies the current value; this helper records the stable root identity.
-- After that, ordinary mutation writeback and call-result threading carry the
-- updated value without an ambient World or global-state object.
def ofGlobal (i : Nat) (v : T) : Mutation Key T :=
  { loc := .global i, path := [], val := v }

@[simp] theorem val_ofGlobal (i : Nat) (v : T) :
    (ofGlobal (Key := Key) i v).val = v := rfl

@[simp] theorem path_ofGlobal (i : Nat) (v : T) :
    (ofGlobal (Key := Key) i v).path = [] := rfl

@[simp] theorem loc_ofGlobal (i : Nat) (v : T) :
    (ofGlobal (Key := Key) i v).loc = .global i := rfl

-- Keep the boundary constructor computational: generated entry adapters use
-- these reductions directly, and a future opaque implementation would make a
-- globally rooted mutation observationally different from local/param roots.
private def globalRootSmoke : Mutation Nat Nat :=
  @Prover.Mutation.Mutation.ofGlobal Nat Nat 17 23

-- This is the exact explicit-argument shape emitted by the global boundary
-- renderer, including a non-atomic pointee type that must stay parenthesized.
private def generatedGlobalRootShape {Key : Type} (value : BoundedNat (2^64)) :
    Mutation Key (BoundedNat (2^64)) :=
  @Prover.Mutation.Mutation.ofGlobal Key (BoundedNat (2^64)) 17 value

private theorem generatedGlobalRootShape_val {Key : Type} (value : BoundedNat (2^64)) :
    (generatedGlobalRootShape (Key := Key) value).val = value := rfl

#guard globalRootSmoke.loc = .global 17
#guard globalRootSmoke.path == []
#guard globalRootSmoke.val == 23

-- Sentinel for `Operation::Uninit` markers emitted by upstream's
-- livevar_analysis for non-parameter mutable-ref temps that are
-- conditionally defined in the function body (e.g. `let v = if c
-- then borrow_a else borrow_b`). The slot `i` keeps two distinct
-- uninits structurally distinct (no `isParent` cross-talk) and
-- doesn't collide with a real `localRoot i` because no Move local
-- of reference type has an associated value-form root. Requires
-- `[Inhabited T]` so the placeholder `val` is total Lean. Conditional
-- `WriteBack` chains that reference this temp are gated on runtime
-- `isParent` checks; on the path where the sentinel survives,
-- `isParent` returns `false` against any real borrow path, so the
-- writeback is a no-op.
def uninit (i : Nat) [Inhabited T] : Mutation Key T :=
  { loc := .localRoot i, path := [], val := default }

def uninit.aborts (_ : Nat) : Bool := false

-- Extend the path with a struct field projection.
def borrowField
    (m : Mutation Key S) (sid : Nat) (offset : Nat) (sel : S -> T) : Mutation Key T :=
  { loc := m.loc, path := m.path ++ [.structField sid offset], val := sel m.val }

@[simp] theorem val_borrowField
    (m : Mutation Key S) (sid : Nat) (offset : Nat) (sel : S -> T) :
    (borrowField m sid offset sel).val = sel m.val := rfl

theorem path_borrowField
    (m : Mutation Key S) (sid : Nat) (offset : Nat) (sel : S -> T) :
    (borrowField m sid offset sel).path =
      m.path ++ [.structField sid offset] := rfl

theorem loc_borrowField
    (m : Mutation Key S) (sid : Nat) (offset : Nat) (sel : S -> T) :
    (borrowField m sid offset sel).loc = m.loc := rfl

-- Extend the path with an enum-variant field projection.
def borrowEnumField
    (m : Mutation Key S) (sid variant offset : Nat) (sel : S -> T) : Mutation Key T :=
  { loc := m.loc, path := m.path ++ [.enumField sid variant offset], val := sel m.val }

@[simp] theorem val_borrowEnumField
    (m : Mutation Key S) (sid variant offset : Nat) (sel : S -> T) :
    (borrowEnumField m sid variant offset sel).val = sel m.val := rfl

theorem path_borrowEnumField
    (m : Mutation Key S) (sid variant offset : Nat) (sel : S -> T) :
    (borrowEnumField m sid variant offset sel).path =
      m.path ++ [.enumField sid variant offset] := rfl

theorem loc_borrowEnumField
    (m : Mutation Key S) (sid variant offset : Nat) (sel : S -> T) :
    (borrowEnumField m sid variant offset sel).loc = m.loc := rfl

-- Extend the path with a vector index (`vector::borrow_mut`).
def borrowVecIndex
    (m : Mutation Key (List T)) (i : Nat) [Inhabited T] : Mutation Key T :=
  { loc := m.loc,
    path := m.path ++ [.vecIndex i],
    val := m.val.getD i default }

@[simp] theorem val_borrowVecIndex
    (m : Mutation Key (List T)) (i : Nat) [Inhabited T] :
    (borrowVecIndex m i).val = m.val.getD i (default : T) := rfl

theorem path_borrowVecIndex
    (m : Mutation Key (List T)) (i : Nat) [Inhabited T] :
    (borrowVecIndex m i).path = m.path ++ [.vecIndex i] := rfl

theorem loc_borrowVecIndex
    (m : Mutation Key (List T)) (i : Nat) [Inhabited T] :
    (borrowVecIndex m i).loc = m.loc := rfl

-- Extend the path with a map key (`table::borrow_mut` /
-- `dynamic_field::borrow_mut` / etc.). The container's value is
-- projected to the borrowed value via the supplied `lookup`
-- function. Renderer-side: `lookup` is wired to `TypedMap.get` (or
-- the matching native lookup) at the call site.
def borrowMapKey
    (m : Mutation Key S) (k : Key) (lookup : S -> Key -> V) : Mutation Key V :=
  { loc := m.loc,
    path := m.path ++ [.mapKey k],
    val := lookup m.val k }

@[simp] theorem val_borrowMapKey
    (m : Mutation Key S) (k : Key) (lookup : S -> Key -> V) :
    (borrowMapKey m k lookup).val = lookup m.val k := rfl

theorem path_borrowMapKey
    (m : Mutation Key S) (k : Key) (lookup : S -> Key -> V) :
    (borrowMapKey m k lookup).path = m.path ++ [.mapKey k] := rfl

theorem loc_borrowMapKey
    (m : Mutation Key S) (k : Key) (lookup : S -> Key -> V) :
    (borrowMapKey m k lookup).loc = m.loc := rfl

-- ---- Writebacks ----
-- Each writeback helper takes the parent + child mutations plus a
-- container-specific updater. Runtime keys / indices are recovered
-- from the child's path at runtime; the `*Last` forms (the ones the
-- renderer emits) read only the last path edge.

-- Vector-index writeback: rewrites `parent.val` (a `List T`) at the index
-- the child was borrowed at, recovering that index from `child.path` (the
-- renderer inlines the statically-known-index case to a direct `List.set`,
-- so this helper is the path-recovering form used when the borrow site is
-- in a parent function and only the runtime path carries the index).
def writeBackVecIndex
    (parent : Mutation Key (List T)) (child : Mutation Key T)
    : Mutation Key (List T) :=
  match child.path.reverse.findSome? (fun e => match e with | .vecIndex i => some i | _ => none) with
  | some i => updateValue parent (parent.val.set i child.val)
  | none => parent

def writeBackVecIndex.aborts
    (_ : Mutation Key (List T)) (_ : Mutation Key T) : Bool := false

-- Prefix-agnostic writebacks: a single-edge writeback child is by
-- construction the mutation borrowed at this container level, so its
-- LAST path edge carries the index/key. Only that edge is read; the
-- path PREFIX (arbitrary at non-root call sites) is never consulted.
--
-- History: the original writeback matched `.vecIndex` only as the
-- FIRST edge after dropping the parent prefix, which missed children
-- borrowed through a struct field (e.g. `borrow_mut_rewarder` borrows
-- `manager.rewarders[idx]`, so the child path is
-- `[.structField rewarders, .vecIndex idx]` while the writeback parent
-- is the bare `rewarders` vector) -- there the leading `.structField`
-- made the match fall through to the identity no-op, silently dropping
-- the element update. Its replacement (`writeBackVecIndex`, now
-- deprecated) scanned the WHOLE path from the right for the most
-- recent matching edge, which fixed that case but consulted the path
-- prefix -- wrong when the parent is a fresh `ofLocal` wrap inside a
-- callee invoked on an interior borrow whose prefix carries a foreign
-- `.vecIndex`/`.mapKey` (a structField-terminal child would write at
-- the prefix's index instead of no-op'ing). Reading only the LAST edge
-- is correct at every emission site: the renderer's chain peeling
-- guarantees the static suffix from the writeback level to the child
-- is exactly one edge.
def writeBackVecIndexLast
    (parent : Mutation Key (List T)) (child : Mutation Key T)
    : Mutation Key (List T) :=
  match child.path.reverse.head? with
  | some (.vecIndex i) => updateValue parent (parent.val.set i child.val)
  | _ => parent

def writeBackVecIndexLast.aborts
    (_ : Mutation Key (List T)) (_ : Mutation Key T) : Bool := false

@[simp] theorem val_writeBackVecIndexLast_borrowVecIndex_set
    (parent : Mutation Key (List T)) (i : Nat) [Inhabited T] (v : T) :
    (writeBackVecIndexLast parent ((borrowVecIndex parent i).set v)).val =
      parent.val.set i v := by
  simp [writeBackVecIndexLast, borrowVecIndex, set, updateValue]

@[simp] theorem path_writeBackVecIndexLast
    (parent : Mutation Key (List T)) (child : Mutation Key T) :
    (writeBackVecIndexLast parent child).path = parent.path := by
  unfold writeBackVecIndexLast; split <;> rfl

@[simp] theorem loc_writeBackVecIndexLast
    (parent : Mutation Key (List T)) (child : Mutation Key T) :
    (writeBackVecIndexLast parent child).loc = parent.loc := by
  unfold writeBackVecIndexLast; split <;> rfl

theorem writeBackVecIndexLast_congr
    (parent : Mutation Key (List T)) {c₁ c₂ : Mutation Key T}
    (hpath : c₁.path.reverse.head? = c₂.path.reverse.head?)
    (hval : c₁.val = c₂.val) :
    writeBackVecIndexLast parent c₁ = writeBackVecIndexLast parent c₂ := by
  unfold writeBackVecIndexLast
  rw [hpath, hval]

-- Map-key writeback with path-recovered key: pulls the runtime key from
-- `child.path` (the most recent `.mapKey`) rather than taking an explicit
-- `k : Key`, mirroring `writeBackVecIndex`'s `.vecIndex` scan. Necessary at
-- writeback sites where the renderer's `render_map_key_for_child` falls
-- back to `default` because the borrow site isn't in `borrow_sources`
-- (typical when the child is the result of intermediate `Mutation.set`
-- operations on a borrowed map-key value, e.g.
-- `*vec_map::get_mut(m, k) = *count + 1`).
def writeBackMapKey
    (insert : S -> Key -> V -> S)
    (parent : Mutation Key S) (child : Mutation Key V)
    : Mutation Key S :=
  match child.path.reverse.findSome? (fun e => match e with | .mapKey k => some k | _ => none) with
  | some k => updateValue parent (insert parent.val k child.val)
  | none => parent

@[simp]
theorem val_writeBackMapKey_borrowMapKey_set
    (insert : S -> Key -> V -> S)
    (parent : Mutation Key S) (k : Key) (lookup : S -> Key -> V) (v : V) :
    (writeBackMapKey insert parent (set (borrowMapKey parent k lookup) v)).val =
      insert parent.val k v := by
  simp [writeBackMapKey, borrowMapKey, set, updateValue]

def writeBackMapKey.aborts
    (_ : S -> Key -> V -> S)
    (_ : Mutation Key S) (_ : Mutation Key V) : Bool := false

def writeBackMapKeyLast
    (insert : S -> Key -> V -> S)
    (parent : Mutation Key S) (child : Mutation Key V)
    : Mutation Key S :=
  match child.path.reverse.head? with
  | some (.mapKey k) => updateValue parent (insert parent.val k child.val)
  | _ => parent

def writeBackMapKeyLast.aborts
    (_ : S -> Key -> V -> S) (_ : Mutation Key S) (_ : Mutation Key V) : Bool := false

@[simp] theorem val_writeBackMapKeyLast_borrowMapKey_set
    (insert : S -> Key -> V -> S) (parent : Mutation Key S) (k : Key)
    (lookup : S -> Key -> V) (v : V) :
    (writeBackMapKeyLast insert parent ((borrowMapKey parent k lookup).set v)).val =
      insert parent.val k v := by
  simp [writeBackMapKeyLast, borrowMapKey, set, updateValue]

@[simp] theorem path_writeBackMapKeyLast
    (insert : S -> Key -> V -> S) (parent : Mutation Key S) (child : Mutation Key V) :
    (writeBackMapKeyLast insert parent child).path = parent.path := by
  unfold writeBackMapKeyLast; split <;> rfl

@[simp] theorem loc_writeBackMapKeyLast
    (insert : S -> Key -> V -> S) (parent : Mutation Key S) (child : Mutation Key V) :
    (writeBackMapKeyLast insert parent child).loc = parent.loc := by
  unfold writeBackMapKeyLast; split <;> rfl

-- Applied post-hoc rather than inline on the old defs: the replacement
-- identifier must already be defined when the attribute elaborates, and
-- inline placement would fire the deprecation linter at
-- `val_writeBackMapKey_borrowMapKey_set` above.
attribute [deprecated writeBackVecIndexLast (since := "2026-07-15")] writeBackVecIndex
attribute [deprecated writeBackMapKeyLast (since := "2026-07-15")] writeBackMapKey

section PrefixAdversarialGuards
-- r0 countermodel, Key := Nat. These execute at elaboration in every
-- Prelude copy; delete the deprecated-op guards with the aliases.
private def advP : Mutation Nat (List Nat) :=
  { loc := .localRoot 0, path := [], val := [0, 0, 0] }
private def advC : Mutation Nat Nat :=
  { loc := .param 0, path := [.vecIndex 1, .structField 5 0], val := 42 }
-- fixed: structField-terminal child => no-op regardless of prefix
#guard (writeBackVecIndexLast advP advC).val = [0, 0, 0]
-- documents the legacy divergence (the absolute scan writes at the prefix's index)
set_option linter.deprecated false in
#guard (writeBackVecIndex advP advC).val = [0, 42, 0]
private def advCW : Mutation Nat Nat :=
  { loc := .param 0, path := [.vecIndex 1, .structField 5 0, .vecIndex 2], val := 42 }
-- write direction: prefix ignored, the LAST edge's index is written
#guard (writeBackVecIndexLast advP advCW).val = [0, 0, 42]

private def advPM : Mutation Nat (List (Nat × Nat)) :=
  { loc := .localRoot 0, path := [], val := [] }
private def advIns (s : List (Nat × Nat)) (k v : Nat) : List (Nat × Nat) :=
  s ++ [(k, v)]
private def advCM : Mutation Nat Nat :=
  { loc := .param 0, path := [.mapKey 7, .structField 5 0], val := 42 }
#guard (writeBackMapKeyLast advIns advPM advCM).val = []
set_option linter.deprecated false in
#guard (writeBackMapKey advIns advPM advCM).val = [(7, 42)]
private def advCMW : Mutation Nat Nat :=
  { loc := .param 0, path := [.mapKey 7, .structField 5 0, .mapKey 9], val := 42 }
#guard (writeBackMapKeyLast advIns advPM advCMW).val = [(9, 42)]
end PrefixAdversarialGuards

-- ---- IsParent predicate ----
--
-- Decides whether `parent`'s path is a strict prefix of `child`'s
-- path with exactly `edge` in between. Used to lower
-- `Operation::IsParent` at conditional-borrow dispatch sites.
-- Edge match for the ANCESTOR predicates (`isParent` / `isParentHyper`):
-- compares a guard edge (emitted by the renderer with a PLACEHOLDER
-- payload) against the child's runtime path edge (carrying the REAL
-- payload), so the match is VALUE-agnostic WITHIN a kind:
--   * `mapKey _ ~ mapKey _`: the renderer can't statically know the
--     runtime df/map key, so it emits the `AnyKey.unit` placeholder while
--     the child's path carries the real key (the writeback body recovers
--     it from the child's own path).
--   * `vecIndex _ ~ vecIndex _`: likewise, the guard stamps a `0`
--     placeholder index while the child carries the real index.
-- The edge KIND, by contrast, must match EXACTLY -- a `mapKey` never
-- legitimately faces a `vecIndex` (or vice versa). Stage 2 normalizes
-- every container edge so its kind reflects the container TYPE:
-- `promote_vec_index_for_map_borrow` rewrites the internal `VecIndex` of a
-- vector-backed map native (`vec_map::get_mut`) to `MapKey`, and
-- `demote_map_key_for_vector_field` rewrites a `MapKey` summarized for a
-- find-by-value lookup over a real `vector` field
-- (`validator_set::get_validator_mut(addr)`) back to `VecIndex`. With the
-- kind correct at the source, the guard and the child path always agree on
-- kind, so cross-kind compatibility is neither needed nor sound. All other
-- kinds (structField / enumField / direct) match exactly via `BEq`.
def edgeMatchesAncestor [BEq Key] (a b : Edge Key) : Bool :=
  match a, b with
  | .mapKey _, .mapKey _ => true
  | .vecIndex _, .vecIndex _ => true
  | _, _ => a == b

def isParent [BEq Key]
    (parent : Mutation Key S) (e : Edge Key) (child : Mutation Key T) : Bool :=
  let suffix := child.path.drop parent.path.length
  (parent.loc == child.loc)
    && (child.path.length == parent.path.length + 1)
    && (child.path.take parent.path.length == parent.path)
    && (match suffix with
        | [] => false
        | head :: _ => edgeMatchesAncestor head e)

-- IsParent generalised to a chain of edges. Mirrors `isParent` but
-- compares the child's tail against a list of edges rather than a
-- single one. Used to lower `Operation::IsParent` when upstream's
-- borrow analysis emits a `Hyper` (multi-step) edge -- e.g. a
-- struct-field borrow that descends into a Table value lowers to
-- `[structField, mapKey]` and the child's path carries both entries.
-- Path membership uses boolean `BEq (Edge Key)`, lifted pointwise
-- to `List (Edge Key)` by the standard library.
def isParentHyper [BEq Key]
    (parent : Mutation Key S) (es : List (Edge Key)) (child : Mutation Key T) : Bool :=
  (parent.loc == child.loc)
    && (child.path.length == parent.path.length + es.length)
    && (child.path.take parent.path.length == parent.path)
    && ((child.path.drop parent.path.length).zip es |>.all (fun p => edgeMatchesAncestor p.1 p.2))

-- Same-location, same-path equality. Used for the unconditional
-- direct-writeback flavour in `memory_instrumentation.rs`.
def isSameMutation [BEq Key]
    (a : Mutation Key S) (b : Mutation Key T) : Bool :=
  (a.loc == b.loc) && (a.path == b.path)

-- ---- Aborts companions (always false by construction) ----
def deref.aborts          (_ : Mutation Key T) : Bool := false
def updateValue.aborts    (_ : Mutation Key T) (_ : T) : Bool := false
def isParent.aborts [BEq Key]
    (_ : Mutation Key S) (_ : Edge Key) (_ : Mutation Key T) : Bool := false
def isParentHyper.aborts [BEq Key]
    (_ : Mutation Key S) (_ : List (Edge Key)) (_ : Mutation Key T) : Bool := false
def isSameMutation.aborts [BEq Key]
    (_ : Mutation Key S) (_ : Mutation Key T) : Bool := false

end Mutation

-- Ghost-state writeback stub for `BorrowNode::SpecGlobalRoot`.
-- The renderer emits `Prover.Mutation.writeBackSpecGlobal v` at
-- every `WriteBack { node: SpecGlobalRoot { tyArgs }, .. }` site;
-- this prelude defines the helper as Unit-returning so the
-- generated Lean type-checks. The verification harness substitutes
-- real ghost-state semantics for this helper at proof time.
-- Used only by `prover::ghost::borrow_mut<T, U>()` callsites; no
-- in-tree client currently exercises this path.
def writeBackSpecGlobal {U : Type} (v : U) : Unit :=
  let _ := v
  ()

end Prover.Mutation

@[simp]
theorem mutation_path_set {K T : Type} (m : _root_.Prover.Mutation.Mutation K T)
    (v : T) :
    (_root_.Prover.Mutation.Mutation.set m v).path = m.path :=
  _root_.Prover.Mutation.Mutation.path_set m v

@[simp]
theorem mutation_loc_set {K T : Type} (m : _root_.Prover.Mutation.Mutation K T)
    (v : T) :
    (_root_.Prover.Mutation.Mutation.set m v).loc = m.loc :=
  _root_.Prover.Mutation.Mutation.loc_set m v

-- Inject a concrete key value into the per-package `AnyKey` type.
--
-- LEMMA-package modules (Sui / MoveStdlib / ... framework code) are
-- rendered abstract over the key: `variable {__MutKey : Type}` with
-- `local notation AnyKey => __MutKey`. They cannot import the
-- per-package `Generated.AnyKey` inductive (that would close a module
-- import cycle, since `Generated.AnyKey` imports user `_Types`). So an
-- abstract framework function that borrows a map keyed by a CONCRETE
-- type (e.g. `sui::versioned::load_value_mut`, keyed by a `u64`) has no
-- `AnyKey.k_<ctor>` constructor in scope to wrap the key with.
--
-- `IntoKey Key A` bridges that gap: the framework function carries a
-- `[IntoKey __MutKey <concrete>]` hypothesis and emits
-- `IntoKey.intoKey <key>`; the per-package `Generated.AnyKey` provides
-- the matching `instance : IntoKey AnyKey <concrete>` (mapping to the
-- real `AnyKey.k_<ctor>` constructor), so resolution succeeds at the
-- user-package call site where `__MutKey := AnyKey`. This is the
-- map-key analogue of the abstract `__ObjU` / `__TyU` universe
-- treatment for lemma-package object transfers.
class IntoKey (Key : Type) (A : Type) where
  intoKey : A -> Key

-- The inverse of `IntoKey`: recover a key value back out of the abstract
-- `__MutKey` on the writeback side. A lemma-package function generic over a
-- map key `K` carries `[IntoKey AnyKey K] [FromKey AnyKey K]` -- the
-- per-package `ToAnyKey` / `FromAnyKey` classes live in `Generated.AnyKey`,
-- which framework modules never import (an unknown class in a binder is
-- `invalid binder annotation, type is not a class instance`). The
-- per-package `Generated.AnyKey` derives both instances from its own
-- `ToAnyKey` / `FromAnyKey`, so user call sites resolve them.
class FromKey (Key : Type) (A : Type) where
  fromKey : Key -> A

-- Edge derived-BEq bridge surface (hoisted from the move-stl SLcompat kit):
-- same-constructor unfold equations plus the lawfulness instance, so
-- `eq_of_beq` / `beq_iff_eq` / `beq_self_eq_true` fire on `Edge K` (and,
-- through core's List instance, on paths `List (Edge K)`) whenever the key
-- carries `LawfulBEq`.
theorem edge_beq_direct {K : Type} [BEq K] :
    ((Prover.Mutation.Edge.direct : Prover.Mutation.Edge K) == .direct) = true := rfl

theorem edge_beq_structField {K : Type} [BEq K] (s o s' o' : Nat) :
    ((Prover.Mutation.Edge.structField s o : Prover.Mutation.Edge K)
      == .structField s' o') = (s == s' && o == o') := rfl

theorem edge_beq_enumField {K : Type} [BEq K] (s v o s' v' o' : Nat) :
    ((Prover.Mutation.Edge.enumField s v o : Prover.Mutation.Edge K)
      == .enumField s' v' o') = (s == s' && (v == v' && o == o')) := rfl

theorem edge_beq_vecIndex {K : Type} [BEq K] (i i' : Nat) :
    ((Prover.Mutation.Edge.vecIndex i : Prover.Mutation.Edge K)
      == .vecIndex i') = (i == i') := rfl

theorem edge_beq_mapKey {K : Type} [BEq K] (k k' : K) :
    ((Prover.Mutation.Edge.mapKey k : Prover.Mutation.Edge K)
      == .mapKey k') = (k == k') := rfl

instance {K : Type} [BEq K] [LawfulBEq K] :
    LawfulBEq (Prover.Mutation.Edge K) where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;>
      first
      | rfl
      | exact Bool.noConfusion (show false = true from h)
      | (rw [edge_beq_vecIndex] at h
         exact congrArg _ (eq_of_beq h))
      | (rw [edge_beq_mapKey] at h
         exact congrArg _ (eq_of_beq h))
      | (rw [edge_beq_structField, Bool.and_eq_true] at h
         rw [eq_of_beq h.1, eq_of_beq h.2])
      | (rw [edge_beq_enumField, Bool.and_eq_true, Bool.and_eq_true] at h
         rw [eq_of_beq h.1, eq_of_beq h.2.1, eq_of_beq h.2.2])
  rfl {a} := by
    cases a <;>
      simp only [edge_beq_direct, edge_beq_structField, edge_beq_enumField,
        edge_beq_vecIndex, edge_beq_mapKey, beq_self_eq_true, Bool.and_self]
