-- Native implementations for move_stdlib::bcs
-- Binary Canonical Serialization
--
-- `bcs::to_bytes<X>(v)` for a GENERIC `X` (the only path that reaches
-- this framework native -- `comparator::compare<X>` ->
-- `compare_u8_vector(to_bytes(v1), to_bytes(v2))`) dispatches through
-- the type-code universe: the `[HasCode U X]` instance in scope at the
-- call site gives the code, and `Universe.serialize` (generated per
-- project in `Generated/TyCodeInterp.lean`) produces the BCS bytes.
-- `Universe.serialize` defaults to `[]` (the old stub) for universes /
-- types that don't implement it, so unmodeled serializations still
-- evaluate (and any test asserting their exact bytes fails, the correct
-- outcome). Concrete `bcs::to_bytes<TypeName>` etc. are routed to
-- per-type natives at the call site, not here.

import Prelude.BoundedNat
import Prelude.Helpers
import Prelude.Universe

namespace Bcs

def to_bytes {U : Type} [Universe U] (_tv0 : Type) [BEq _tv0] [Inhabited _tv0]
    [hc : HasCode U _tv0] (v : _tv0) : List (BoundedNat (2^8)) :=
  Universe.serialize hc.code (cast hc.proof.symm v)

-- sui::bcs's cursor API (the `BCS` struct, `new`, `into_remainder_bytes`,
-- and the `peel_*` family) is now GENERATED from source in `Sui/Bcs.lean`
-- (real byte-level decode, not the old opaque `default` stubs). Only the
-- genuine std native `to_bytes` (above) remains modeled here. Both still
-- render to `namespace Bcs`; the names are disjoint so they compose.

end Bcs
