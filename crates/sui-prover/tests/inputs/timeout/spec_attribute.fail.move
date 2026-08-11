// The spec caps itself at 1s, far below the global limit the run is given, and
// the goal (modular multiplication distributing over the residues) is nonlinear,
// so the solver hits that cap. The diagnostic must name the spec's own limit.
module 0x42::foo;

#[spec_only]
use prover::prover::{ensures, requires};

public fun mod_mul(a: u64, b: u64, m: u64): u64 {
    (((a as u128) * (b as u128)) % (m as u128)) as u64
}

#[spec(prove, timeout = 1)]
public fun mod_mul_spec(a: u64, b: u64, m: u64): u64 {
    requires(m > 0);
    let res = mod_mul(a, b, m);
    ensures(res == (((a % m) as u128) * ((b % m) as u128) % (m as u128)) as u64);
    res
}
