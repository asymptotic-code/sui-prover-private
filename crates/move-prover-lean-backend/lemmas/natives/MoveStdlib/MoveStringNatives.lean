-- Native implementations for std::string.
-- These are Move stdlib `native fun` declarations (string.move). The
-- implementations here are total and reducible by the kernel so closed
-- terms involving string operations evaluate during `decide`/`native_decide`.

import Prelude.BoundedNat
import Prelude.Helpers

namespace MoveString

/-- True iff the byte sequence is valid UTF-8.

Walks the bytes interpreting leading bytes:
- 0xxxxxxx — 1-byte ASCII (<= 0x7F).
- 110xxxxx 10xxxxxx — 2 bytes (>= 0xC0, < 0xE0). Disallow overlong (< 0xC2).
- 1110xxxx 10xxxxxx 10xxxxxx — 3 bytes (>= 0xE0, < 0xF0). Disallow overlong
  (E0 80–9F) and surrogate halves (ED A0–BF).
- 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx — 4 bytes (>= 0xF0, < 0xF5). Disallow
  overlong (F0 80–8F) and out-of-range (F4 90–BF, F5..FF).

Continuation bytes must be 10xxxxxx (>= 0x80, < 0xC0). -/
@[reducible] def internal_check_utf8 (bytes : List (BoundedNat (2^8))) : Bool :=
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
@[reducible] def internal_is_char_boundary (bytes : List (BoundedNat (2^8))) (i : BoundedNat (2^64)) : Bool :=
  if i.val ≥ bytes.length then decide (i.val = bytes.length)
  else
    match bytes[i.val]? with
    | some b => decide (b.val < 0x80) || decide (b.val ≥ 0xC0)
    | none => false

/-- Find the first index of `sub` in `bytes`, or `bytes.length` if not found.
Linear scan. -/
@[reducible] def internal_index_of (bytes : List (BoundedNat (2^8))) (sub : List (BoundedNat (2^8))) : BoundedNat (2^64) :=
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
  else ⟨found % 2^64, Nat.mod_lt _ (by decide)⟩  -- unreachable for real strings

/-- Substring `bytes[i..j]`. If indices are out of range or `i > j`, returns
empty list. Total. -/
@[reducible] def internal_sub_string (bytes : List (BoundedNat (2^8))) (i : BoundedNat (2^64)) (j : BoundedNat (2^64)) : List (BoundedNat (2^8)) :=
  if i.val > j.val then []
  else (bytes.drop i.val).take (j.val - i.val)

end MoveString
