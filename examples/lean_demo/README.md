# Lean generation example

This package translates specified Move functions to Lean.

## Move

```move
module lean_demo::math;

#[spec_only]
use prover::prover::{ensures, implies, requires};

public fun max(a: u64, b: u64): u64 {
    if (a >= b) a else b
}

#[spec(prove)]
fun max_spec(a: u64, b: u64): u64 {
    let result = max(a, b);
    ensures(result >= a);
    ensures(result >= b);
    ensures(result == a || result == b);
    result
}
```

The same [`math.move`](sources/math.move) module also contains:

- `clamp`, with nested branches and a precondition.
- `distance`, with guarded subtraction and path-sensitive underflow checks.
- `withdraw`, which updates a `Balance` under an insufficient-funds abort contract.
- `transfer`, which updates two balances and preserves their combined `u128` value.

## Generate and prove

```bash
cd examples/lean_demo
sui-prover --backend lean --generate-only
lake -d output build
```

The checked-in [translation](output/lean_demo/Math.lean) and
[correctness wiring](output/Correctness/Math.lean) are refreshed by generation.
The [proofs](sources/lean/Proofs/MathProofs.lean) use Z3 through `lean-auto`;
SMT results are trusted rather than reconstructed. Z3 must be on `PATH`.

```lean
@[reducible] def max (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : BoundedNat (2^64) :=
  if decide (a ≥ b) then
    a
  else
    b

def max_spec.ensures (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : Prop :=
  ((decide ((_root_.Math.max a b) ≥ a)) = true)
```
