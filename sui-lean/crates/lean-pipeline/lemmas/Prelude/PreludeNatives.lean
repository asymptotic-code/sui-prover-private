-- Bridge file: maps the renderer-emitted `Prelude.Prelude.TypedMap.*`
-- qualified names onto the real, list-backed `TypedMap.*` definitions
-- in `Prelude.TypedMap`.
--
-- Why this file exists. The IR registers the synthetic `TypedMap`
-- struct and the five `TypedMap.{get,set,remove,has,empty}` functions
-- under a module whose `package_name == name == "Prelude"`. The
-- renderer's namespace logic emits qualified names as
-- `<package>.<name>.<symbol>`, i.e. `Prelude.Prelude.TypedMap.empty`
-- (with `Prelude` doubled). Without a sibling
-- `Prelude/PreludeNatives.lean` in the lemmas tree, the renderer
-- would emit `:= sorry` stubs at those paths, which then resolve in
-- preference to anything from `Prelude.TypedMap` and panic at runtime
-- on the first invocation.
--
-- This file IS that sibling. It declares the same five operations
-- inside `namespace Prelude.Prelude.TypedMap`, each forwarding to the
-- real implementation in the root `TypedMap` namespace. Importing
-- this file also brings in the implementations transitively
-- (via `import Prelude.TypedMap` below), so any module that imports
-- one of `Prelude.Prelude` or `Prelude.TypedMap` resolves identically.

import Prelude.TypedMap
import Prelude.BoundedNat

set_option linter.unusedVariables false

-- Type alias for the renderer-emitted qualified name. `abbrev`
-- (rather than `def`) so it's defeq with `List (K x V)` everywhere
-- and the forwarding wrappers below typecheck without explicit
-- coercions.
namespace Prelude.Prelude
abbrev TypedMap (K V : Type) : Type := List (K × V)
end Prelude.Prelude

namespace Prelude.Prelude.TypedMap

def empty (K V : Type) : List (K × V) := _root_.TypedMap.empty K V

def get (K V : Type) [BEq K] [Inhabited V] (m : List (K × V)) (k : K) : V :=
  _root_.TypedMap.get K V m k

def set (K V : Type) [BEq K] (m : List (K × V)) (k : K) (v : V) : List (K × V) :=
  _root_.TypedMap.set K V m k v

def has (K V : Type) [BEq K] (m : List (K × V)) (k : K) : Bool :=
  _root_.TypedMap.has K V m k

-- The IR's `TypedMap.remove` returns `(map, value)`; the underlying
-- handwritten `TypedMap.erase` returns `(value, map)`. Flip the
-- tuple here so the rendered call site's tuple-destructure pattern
-- (`let (new_m, removed_v) := ...`) lines up.
def remove (K V : Type) [BEq K] [Inhabited V] (m : List (K × V)) (k : K)
    : (List (K × V) × V) :=
  let (v, m') := _root_.TypedMap.erase K V m k
  (m', v)

-- Renderer aliases for the underlying `TypedMap.erase` /
-- `TypedMap.erase_if_exists` operations, used by the
-- `Dynamic_field.{remove, remove_if_exists}` rewrite in
-- `try_render_dynamic_field_call`. The rewrite emits the call as
-- `Prelude.Prelude.TypedMap.erase _ _ parent.<ghost> key`, expecting
-- the canonical `(value, map)` / `(List value, map)` return shape
-- (NOT the flipped `remove` shape above).
def erase (K V : Type) [BEq K] [Inhabited V] (m : List (K × V)) (k : K)
    : (V × List (K × V)) :=
  _root_.TypedMap.erase K V m k

def erase_if_exists (K V : Type) [BEq K] [Inhabited V] (m : List (K × V)) (k : K)
    : (List V × List (K × V)) :=
  _root_.TypedMap.erase_if_exists K V m k

-- `.aborts` companions: every TypedMap op is total at the Lean
-- modeling layer; the real partial cases (missing key, type
-- mismatch) live in the spec layer. Mirrors the existing
-- `TypedMap.<op>.aborts := false` declarations in
-- `Prelude/TypedMap.lean`.
def empty.aborts (K V : Type) : Bool := false
def get.aborts (K V : Type) [BEq K] [Inhabited V] (_m : List (K × V)) (_k : K) : Bool := false
def set.aborts (K V : Type) [BEq K] (_m : List (K × V)) (_k : K) (_v : V) : Bool := false
def has.aborts (K V : Type) [BEq K] (_m : List (K × V)) (_k : K) : Bool := false
def remove.aborts (K V : Type) [BEq K] [Inhabited V] (_m : List (K × V)) (_k : K) : Bool := false
def erase.aborts (K V : Type) [BEq K] [Inhabited V] (_m : List (K × V)) (_k : K) : Bool := false
def erase_if_exists.aborts (K V : Type) [BEq K] [Inhabited V] (_m : List (K × V)) (_k : K) : Bool := false

end Prelude.Prelude.TypedMap
