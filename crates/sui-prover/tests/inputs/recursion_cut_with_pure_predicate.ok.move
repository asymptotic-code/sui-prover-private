module 0x42::tree {
    fun depth(n: u64): u64 {
        if (n == 0) { 0 } else { 1 + depth(n - 1) }
    }

    public fun measure(n: u64): u64 {
        depth(n)
    }
}

module 0x42::tree_cut_specs {
    use prover::prover::{requires, ensures};

    #[mode(spec), ext(spec(target = 0x42::tree::depth))]
    fun depth_spec(n: u64): u64 {
        requires(n <= 1000);
        let result = 0x42::tree::depth(n);
        ensures(result == n);
        result
    }
}

// Deepbook's shape: a scenario spec reaches the recursion through a target
// whose own spec is verified, so in the scenario's pass `depth` is kept only as
// reachable (never translated) and its cut spec is pruned. Recursion among
// functions a pass does not translate must not be reported there.
#[mode(spec), ext(spec_only(include = 0x42::tree_cut_specs))]
module 0x42::tree_specs {
    use prover::prover::{requires, ensures};

    #[mode(spec), ext(spec_only, pure)]
    public fun always_valid(_n: u64): bool {
        true
    }

    // A scenario spec (no target) whose closure reaches the recursion.
    #[mode(spec), ext(spec(prove))]
    fun measure_scenario() {
        let n = 3;
        ensures(0x42::tree::measure(n) == n);
    }

    #[mode(spec), ext(spec(prove, target = 0x42::tree::measure))]
    public fun measure_spec(n: u64): u64 {
        requires(n <= 1000);
        let result = 0x42::tree::measure(n);
        ensures(result == n);
        result
    }
}
