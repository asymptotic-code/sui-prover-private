-- Native implementations for sui::address

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.World
-- `to_ascii_string` returns `ascii::String` (`Ascii.MoveString`). Every
-- client that calls it inherently uses `ascii::String`, so the generated
-- `MoveStdlib.Ascii` is present (cf. `MoveStringNatives` importing it too).
import MoveStdlib.Ascii
-- `to_string` returns `string::String` (`MoveString.MoveString`); pull in
-- the generated stdlib module that re-exports it (same as `CoinNatives`).
import MoveStdlib.MoveString

-- `Address.ofNat` lives in `Prelude.Helpers` alongside the struct
-- definition; user-package files import `Prelude.Helpers` directly and
-- so see it without an extra `import Sui.Address`.

namespace Address

variable {__WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry : Type}
local notation:max "World" => Prover.World.World __WorldEvent __WorldObject __WorldDfEntry __WorldBagEntry

-- Fold the byte list (big-endian) into a 256-bit address. Bytes after the
-- 32nd are ignored (Sui addresses are 32 bytes); missing bytes are treated
-- as zero. Round-trips with `to_bytes` for canonical 32-byte inputs.
private def bytesToNat (bytes : List (BoundedNat (2^8))) : Nat :=
  bytes.foldl (fun acc b => (acc * 256 + b.val) % (2^256)) 0

def from_bytes (bytes : List (BoundedNat (2^8))) : Address :=
  Address.mk ⟨bytesToNat bytes % (2^256), Nat.mod_lt _ (by decide)⟩

/-- `address::from_u256(n: u256): address`. Aborts if `n > MAX_ADDRESS`
    (which doesn't apply here since `BoundedNat (2^256)` is already
    capped). Stage 4 (effects) threads `world` on this native because
    it's marked Impure upstream (no `#[ext(pure)]` annotation, can
    abort). Caller destructures `(value, world')`. -/
def from_u256 (n : BoundedNat (2^256)) (world : World) : (Address × World) :=
  (Address.mk n, world)

def from_u256.aborts (_n : BoundedNat (2^256)) : Bool := false

-- Faithful ASCII-hex codec shared by `to_ascii_string` (encode) and
-- `from_ascii_bytes` (decode). The Move round-trip
-- `from_ascii_bytes(address_string(t).as_bytes()).to_id() == package_id(t)`
-- relies on `to_ascii_string` and `from_ascii_bytes` being mutual inverses
-- on the canonical 64-char lowercase hex representation of an address, so a
-- stub (empty/default) breaks any client that checks the identity (e.g.
-- `pas::namespace::setup`). These model the real hex encode/decode.
private def hexNibble (c : BoundedNat (2^8)) : Nat :=
  let v := c.val
  if 48 ≤ v ∧ v ≤ 57 then v - 48
  else if 97 ≤ v ∧ v ≤ 102 then v - 87
  else if 65 ≤ v ∧ v ≤ 70 then v - 55
  else 0

private def hexBytesToNat (bytes : List (BoundedNat (2^8))) : Nat :=
  bytes.foldl (fun acc b => (acc * 16 + hexNibble b) % (2^256)) 0

private def nibbleToHexCode (n : Nat) : BoundedNat (2^8) :=
  let d := n % 16
  let code := if d < 10 then d + 48 else d + 87
  ⟨code % (2^8), Nat.mod_lt _ (by decide)⟩

private def addrToHexAux : Nat -> Nat -> List (BoundedNat (2^8)) -> List (BoundedNat (2^8))
  | 0, _, acc => acc
  | Nat.succ k, x, acc =>
    addrToHexAux k (x / 16) (nibbleToHexCode (x % 16) :: acc)

private def addrToHexBytes (a : Address) : List (BoundedNat (2^8)) :=
  addrToHexAux 64 a.bytes.val []

/-- `address::to_ascii_string(a): ascii::String`. Hex-encodes the address
into a 64-char lowercase ASCII string. Modeled faithfully (not a stub):
clients round-trip the result through `from_ascii_bytes` and compare against
the canonical address-string of a type (`pas::namespace::setup`), so the
concrete bytes must match. World is threaded read-only: the upstream native
isn't `#[ext(pure)]`-annotated (so stage 4 world-threads it, like
`from_u256`); the underlying encoding reads no state. -/
def to_ascii_string (a : Address) (world : World) : (_root_.Ascii.MoveString × World) :=
  ((⟨addrToHexBytes a⟩ : _root_.Ascii.MoveString), world)

def to_u256 (a : Address) : BoundedNat (2^256) :=
  a.bytes

/-- `address::max(): u256` returns `MAX_ADDRESS` (2^256 - 1).
    Move source: `public fun max(): u256 { MAX }`. Total. -/
def max : BoundedNat (2^256) :=
  (115792089237316195423570985008687907853269984665640564039457584007913129639935 : BoundedNat (2^256))

def max.aborts : Bool := false

/-- `address::to_bytes(a: address): vector<u8>` -- big-endian 32-byte
    serialisation. Matches `bytesToNat` in the inverse direction:
    `from_bytes (to_bytes a) == a` for any well-formed address.

    The encoder itself is `Address.toBytesBE` in `Prelude/Helpers.lean`,
    shared with `object::{id_to_bytes, uid_to_bytes}` -- those three Move
    natives are all `bcs::to_bytes` of an `address` and must agree. This def
    stays here (rather than being replaced by the Helpers one) so it remains
    the `Sui::address::to_bytes` row that
    `native_world_arity_matches_lean_models` reads its arity from. -/
def to_bytes (a : Address) : List (BoundedNat (2^8)) :=
  Address.toBytesBE a

def to_bytes.aborts (_a : Address) : Bool := false

/-- Half of the cross-file agreement pin (the other half is
    `Object.id_to_bytes_eq_toBytesBE_of_id_to_address`, which cannot mention
    `to_bytes` because `ObjectNatives` must not import this module -- see the
    note on `Address.toBytesBE`). Together they say
    `object::id_to_bytes id = address::to_bytes (object::id_to_address id)`. -/
theorem to_bytes_eq_toBytesBE (a : Address) : to_bytes a = Address.toBytesBE a := rfl

/-- `address::to_bytes` yields exactly 32 bytes. -/
theorem length_to_bytes (a : Address) : (to_bytes a).length = 32 :=
  Address.length_toBytesBE a

/-- `address::to_string(a: address): string::String`. Decimal/hex-encodes
the address into a `string::String`. Like `to_ascii_string`, the Move
encode loop is opaque (`skip`) so the concrete bytes aren't modeled -- a
stub `MoveString` suffices. World is threaded read-only: the upstream
native isn't `#[ext(pure)]`-annotated (so stage 4 world-threads it, like
`from_u256`/`to_ascii_string`); the underlying encoding reads no state. -/
def to_string (_a : Address) (world : World) : (_root_.MoveString.MoveString × World) :=
  ((default : _root_.MoveString.MoveString), world)

/-- `address::from_ascii_bytes(bytes: vector<u8>): address`. Parses a
64-char ASCII hex string into an address. Modeled faithfully (not a stub)
as the inverse of `to_ascii_string`: clients check
`from_ascii_bytes(address_string(t).as_bytes()).to_id() == package_id(t)`
(`pas::namespace::setup` via `test_helpers::package_id`), which only holds
if the decode actually reconstructs the address. World is threaded
read-only (not `#[ext(pure)]`). -/
def from_ascii_bytes (bytes : List (BoundedNat (2^8))) (world : World) : (Address × World) :=
  (Address.mk ⟨hexBytesToNat bytes % (2^256), Nat.mod_lt _ (by decide)⟩, world)

end Address
