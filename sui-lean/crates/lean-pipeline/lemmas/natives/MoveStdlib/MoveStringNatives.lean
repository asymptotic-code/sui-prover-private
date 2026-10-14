-- Native implementations for std::string.
-- These are Move stdlib `native fun` declarations (string.move). The
-- implementations here are total and reducible by the kernel so closed
-- terms involving string operations evaluate during `decide`/`native_decide`.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.World
import MoveStdlib.Ascii
import MoveStdlib.MoveOption

namespace MoveString

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

-- Move source: `public struct String has copy, drop, store {
-- bytes: vector<u8> }`. The renderer mangles the struct name to
-- `MoveString` (avoiding a collision with Lean's builtin `String`),
-- so user code references it as `MoveString.MoveString`.
structure MoveString where
  bytes : List (BoundedNat (2^8))
deriving DecidableEq

instance : Inhabited MoveString where default := ⟨[]⟩

/-- True iff the byte sequence is valid UTF-8.

Walks the bytes interpreting leading bytes:
- 0xxxxxxx — 1-byte ASCII (<= 0x7F).
- 110xxxxx 10xxxxxx — 2 bytes (>= 0xC0, < 0xE0). Disallow overlong (< 0xC2).
- 1110xxxx 10xxxxxx 10xxxxxx — 3 bytes (>= 0xE0, < 0xF0). Disallow overlong
  (E0 80–9F) and surrogate halves (ED A0–BF).
- 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx — 4 bytes (>= 0xF0, < 0xF5). Disallow
  overlong (F0 80–8F) and out-of-range (F4 90–BF, F5..FF).

Continuation bytes must be 10xxxxxx (>= 0x80, < 0xC0). -/
@[reducible] private def internal_check_utf8_pure (bytes : List (BoundedNat (2^8))) : Bool :=
  let isCont (b : BoundedNat (2^8)) : Bool := decide (0x80 ≤ b.val) && decide (b.val < 0xC0)
  let rec go : List (BoundedNat (2^8)) → Bool
    | [] => true
    | b :: rest =>
      let v := b.val
      if v < 0x80 then go rest
      else if v < 0xC2 then false  -- continuation byte at start, or overlong 2-byte
      else if v < 0xE0 then
        match rest with
        | c1 :: rest' => if isCont c1 then go rest' else false
        | _ => false
      else if v < 0xF0 then
        match rest with
        | c1 :: c2 :: rest' =>
          if !isCont c1 || !isCont c2 then false
          else if v = 0xE0 && c1.val < 0xA0 then false  -- overlong 3-byte
          else if v = 0xED && c1.val ≥ 0xA0 then false  -- surrogate
          else go rest'
        | _ => false
      else if v < 0xF5 then
        match rest with
        | c1 :: c2 :: c3 :: rest' =>
          if !isCont c1 || !isCont c2 || !isCont c3 then false
          else if v = 0xF0 && c1.val < 0x90 then false  -- overlong 4-byte
          else if v = 0xF4 && c1.val ≥ 0x90 then false  -- > U+10FFFF
          else go rest'
        | _ => false
      else false
  go bytes

/-- True iff `i` is a valid char boundary into `bytes` (start of a UTF-8
codepoint, or one past the end). For our verification purposes we check the
weaker "i is at or past the end, or not in the middle of a continuation",
which is sufficient to reduce on closed terms. -/
@[reducible] private def internal_is_char_boundary_pure (bytes : List (BoundedNat (2^8))) (i : BoundedNat (2^64)) : Bool :=
  if i.val ≥ bytes.length then decide (i.val = bytes.length)
  else
    match bytes[i.val]? with
    | some b => decide (b.val < 0x80) || decide (b.val ≥ 0xC0)
    | none => false

/-- Find the first index of `sub` in `bytes`, or `bytes.length` if not found.
Linear scan. -/
@[reducible] private def internal_index_of_pure (bytes : List (BoundedNat (2^8))) (sub : List (BoundedNat (2^8))) : BoundedNat (2^64) :=
  let rec startsAt : List (BoundedNat (2^8)) → List (BoundedNat (2^8)) → Bool
    | [], _ => true
    | _ :: _, [] => false
    | s :: ss, b :: bs =>
      if s.val = b.val then startsAt ss bs else false
  let rec scan (i : Nat) : List (BoundedNat (2^8)) → Nat
    | [] => i + bytes.length  -- not found: return end (caller masks via `convert`)
    | b :: rest =>
      if startsAt sub (b :: rest) then i else scan (i + 1) rest
  let found := scan 0 bytes
  if h : found < 2^64 then ⟨found, h⟩
  else if hb : (2 : Nat) ^ 64 > 0 then ⟨found % 2^64, Nat.mod_lt _ hb⟩
  else ⟨0, Nat.two_pow_pos 64⟩

/-- Substring `bytes[i..j]`. If indices are out of range or `i > j`, returns
empty list. Total. -/
@[reducible] private def internal_sub_string_pure (bytes : List (BoundedNat (2^8))) (i : BoundedNat (2^64)) (j : BoundedNat (2^64)) : List (BoundedNat (2^8)) :=
  if i.val > j.val then []
  else (bytes.drop i.val).take (j.val - i.val)

/-- Public world-threaded native — stage 4 (effects) wraps every Move
`native fun` with a `world` thread, so spec-rendered call sites like
`SuiSpecs.String_spec.internal_check_utf8_spec` destructure
`(value, world')` from each call. Underlying check is pure (no
state read); just thread `world` through unchanged. -/
def internal_check_utf8 (bytes : List (BoundedNat (2^8))) (world : World) : (Bool × World) :=
  (internal_check_utf8_pure bytes, world)

def internal_check_utf8.aborts (_bytes : List (BoundedNat (2^8))) (_world : World) : Bool := false

theorem internal_check_utf8_of_ascii
    (bytes : List (BoundedNat (2^8)))
    (world : World)
    (hascii : ∀ b ∈ bytes, b.val < 128) :
    (internal_check_utf8 bytes world).1 = true := by
  induction bytes with
  | nil =>
      rfl
  | cons b bytes ih =>
      have hb : b.val < 128 := hascii b (by simp)
      have htail : ∀ c ∈ bytes, c.val < 128 := by
        intro c hc
        exact hascii c (by simp [hc])
      cases bytes with
      | nil =>
          simp [internal_check_utf8, internal_check_utf8_pure,
            internal_check_utf8_pure.go, hb]
      | cons c bytes =>
          change internal_check_utf8_pure.go
            (fun b => decide (0x80 ≤ b.val) && decide (b.val < 0xC0))
            (b :: c :: bytes) = true
          rw [internal_check_utf8_pure.go.eq_2, if_pos hb]
          exact ih htail

/-- World-threaded surface for `std::string::internal_is_char_boundary`. -/
def internal_is_char_boundary (bytes : List (BoundedNat (2^8))) (i : BoundedNat (2^64))
    (world : World) : (Bool × World) :=
  (internal_is_char_boundary_pure bytes i, world)

def internal_is_char_boundary.aborts (_bytes : List (BoundedNat (2^8))) (_i : BoundedNat (2^64))
    (_world : World) : Bool := false

/-- World-threaded surface for `std::string::internal_index_of`. -/
def internal_index_of (bytes : List (BoundedNat (2^8))) (sub : List (BoundedNat (2^8)))
    (world : World) : (BoundedNat (2^64) × World) :=
  (internal_index_of_pure bytes sub, world)

def internal_index_of.aborts (_bytes : List (BoundedNat (2^8))) (_sub : List (BoundedNat (2^8)))
    (_world : World) : Bool := false

/-- World-threaded surface for `std::string::internal_sub_string`. -/
def internal_sub_string (bytes : List (BoundedNat (2^8))) (i : BoundedNat (2^64))
    (j : BoundedNat (2^64)) (world : World) : ((List (BoundedNat (2^8))) × World) :=
  (internal_sub_string_pure bytes i j, world)

def internal_sub_string.aborts (_bytes : List (BoundedNat (2^8))) (_i : BoundedNat (2^64))
    (_j : BoundedNat (2^64)) (_world : World) : Bool := false

/-- `std::string::utf8(bytes: vector<u8>): String`. Aborts if `bytes`
isn't valid UTF-8; the value-form stub wraps unconditionally. -/
def utf8 (bytes : List (BoundedNat (2^8))) : MoveString := ⟨bytes⟩

def utf8.aborts (bytes : List (BoundedNat (2^8))) : Bool :=
  !(internal_check_utf8_pure bytes)

/-- `std::string::try_utf8(bytes: vector<u8>): Option<String>`. Returns
`some(String)` iff `bytes` is valid UTF-8, else `none` -- never aborts.
World-threaded (it transitively calls the world-threaded
`internal_check_utf8`); the world is read-only and threaded through
unchanged.

The Option is built directly from the `MoveOption` structure
(`vec := [s]` for some, `[]` for none) rather than the generated
`MoveOption.some`/`.none` defs: those only exist when the client's Move
code references `option::some`/`none` (cetus-clmm does; cetus-stl and
integer-mate do not), but the `MoveOption` STRUCTURE is always emitted, so
the anonymous constructor keeps this native client-agnostic. -/
def try_utf8 (bytes : List (BoundedNat (2^8))) (world : World) :
    ((MoveOption.MoveOption MoveString) × World) :=
  let result : MoveOption.MoveOption MoveString :=
    if internal_check_utf8_pure bytes then ⟨[⟨bytes⟩]⟩
    else ⟨[]⟩
  (result, world)

def try_utf8.aborts (_bytes : List (BoundedNat (2^8))) (_world : World) : Bool := false

theorem try_utf8_eq_some_of_ascii
    (bytes : List (BoundedNat (2^8)))
    (world : World)
    (hascii : ∀ b ∈ bytes, b.val < 128) :
    (try_utf8 bytes world).1 =
      (⟨[⟨bytes⟩]⟩ : MoveOption.MoveOption MoveString) := by
  have hcheck := internal_check_utf8_of_ascii bytes world hascii
  change (if (internal_check_utf8 bytes world).1 then
    (⟨[⟨bytes⟩]⟩ : MoveOption.MoveOption MoveString)
  else
    (⟨[]⟩ : MoveOption.MoveOption MoveString)) =
      (⟨[⟨bytes⟩]⟩ : MoveOption.MoveOption MoveString)
  rw [hcheck]
  rfl

/-- `std::string::length(self: &String): u64`. Byte length. -/
axiom string_length_bounded (v : List (BoundedNat (2^8))) : v.length < 2^64
def length (self : MoveString) : BoundedNat (2^64) :=
  ⟨self.bytes.length, string_length_bounded self.bytes⟩

def length.aborts (_self : MoveString) : Bool := false

/-- `std::string::is_empty(self: &String): bool`. -/
def is_empty (self : MoveString) : Bool := self.bytes.isEmpty

def is_empty.aborts (_self : MoveString) : Bool := false

/-- `std::string::as_bytes(self: &String): &vector<u8>`. -/
def as_bytes (self : MoveString) : List (BoundedNat (2^8)) := self.bytes

def as_bytes.aborts (_self : MoveString) : Bool := false

/-- `std::string::bytes(self: &String): &vector<u8>`. The underlying
byte vector -- same value as `as_bytes`. -/
def bytes (self : MoveString) : List (BoundedNat (2^8)) := self.bytes

def bytes.aborts (_self : MoveString) : Bool := false

/-- `std::string::into_bytes(self: String): vector<u8>`. Consumes the
string and returns its underlying byte vector -- same value as `bytes`,
by value. -/
def into_bytes (self : MoveString) : List (BoundedNat (2^8)) := self.bytes

def into_bytes.aborts (_self : MoveString) : Bool := false

/-- `std::string::from_ascii(s: ascii::String): String`. Converts an
ASCII-validated string to a UTF-8 string. Since ASCII is a subset of
UTF-8, this is a wrap-then-rewrap operation on the underlying bytes. -/
def from_ascii (s : Ascii.MoveString) : MoveString :=
  ⟨s.bytes⟩

def from_ascii.aborts (_s : Ascii.MoveString) : Bool := false

/-- `std::string::substring(s: &String, i: u64, j: u64): String`.
Returns the substring `s[i..j]`. Aborts if `i > j`, `j > length`,
or the indices aren't on UTF-8 char boundaries. Lean model returns
the raw bytes; abort semantics are captured in `.aborts`. -/
def substring (s : MoveString) (i : BoundedNat (2^64)) (j : BoundedNat (2^64)) : MoveString :=
  ⟨internal_sub_string_pure s.bytes i j⟩

def substring.aborts (s : MoveString) (i : BoundedNat (2^64)) (j : BoundedNat (2^64)) : Bool :=
  let l := s.bytes.length
  decide (j.val > l) || decide (i.val > j.val)
    || !(internal_is_char_boundary_pure s.bytes i)
    || !(internal_is_char_boundary_pure s.bytes j)

/-- `std::string::append(s: &mut String, r: String)`. Concatenates `r`
onto `s`. Returns the updated `s` value -- the IR's augmented `&mut`
return position with the original `Unit` slot collapsed by stage 6's
tuple_simplify. Classified as `PurePartial` (see natives.rs); no
world threading at call sites. -/
def append (s : MoveString) (r : MoveString) : MoveString :=
  ⟨s.bytes ++ r.bytes⟩

def append.aborts (_s : MoveString) (_r : MoveString) : Bool := false

/-- `std::string::append_utf8(s: &mut String, bytes: vector<u8>)`.
Concatenates the UTF-8 bytes onto `s`. Aborts iff `bytes` isn't valid
UTF-8 (the abort companion checks via `internal_check_utf8_pure`). -/
def append_utf8 (s : MoveString) (bytes : List (BoundedNat (2^8))) : MoveString :=
  ⟨s.bytes ++ bytes⟩

def append_utf8.aborts (_s : MoveString) (bytes : List (BoundedNat (2^8))) : Bool :=
  !(internal_check_utf8_pure bytes)

/-- `std::string::index_of(s: &String, r: &String): u64`. Returns the
first byte-offset of `r` in `s`, or `length(s)` if `r` is not a
substring. Pure / total: never aborts. Abstract stub returns
`default` (0); real verification lives in the harness. -/
def index_of (_s : MoveString) (_r : MoveString) : BoundedNat (2^64) :=
  default

def index_of.aborts (_s : MoveString) (_r : MoveString) : Bool := false

end MoveString

/-! ## Shared `try_utf8` world frame

Namespaced per the standing rule in
`plans/lean-pipeline/shared-proof-infra.md`.

NOT here (deliberately): the corpora's
`MoveOption.is_some _ (try_utf8 (into_bytes (Type_name.into_string ...)) w).1 = true`.
Its shipped half is already `MoveString.try_utf8_eq_some_of_ascii` above, after
which the goal is `rfl`; its other half -- "every type name in THIS package is
ASCII" -- is an induction over the generated `TyCode` universe and cannot leave
the client. Routing the composed form through `MoveOption.is_some` would also
make a per-package-prunable generated function a hard dependency of this
natives file. See the W5 shared-facts report. -/

namespace MoveStringFacts

theorem try_utf8_snd {Ev Ob Df Be : Type}
    (bytes : List (BoundedNat (2^8)))
    (world : Prover.World.World Ev Ob Df Be) :
    (MoveString.try_utf8 bytes world).2 = world := rfl

end MoveStringFacts
