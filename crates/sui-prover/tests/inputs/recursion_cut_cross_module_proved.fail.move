module 0x42::tree {
    // Private and recursive; the cutting spec lives in another module and is
    // proved, which must be rejected like the single-module case.
    fun depth(n: u64): u64 {
        if (n == 0) { 0 } else { 1 + depth(n - 1) }
    }

    public fun measure(n: u64): u64 {
        depth(n)
    }
}

module 0x42::tree_cut_specs {
    use prover::prover::{requires, ensures};

    #[mode(spec), ext(spec(prove, target = 0x42::tree::depth))]
    fun depth_spec(n: u64): u64 {
        requires(n <= 1000);
        let result = 0x42::tree::depth(n);
        ensures(result == n);
        result
    }
}

#[mode(spec), ext(spec_only(include = 0x42::tree_cut_specs))]
module 0x42::tree_specs {
    use prover::prover::{requires, ensures};

    #[mode(spec), ext(spec(prove, target = 0x42::tree::measure))]
    public fun measure_spec(n: u64): u64 {
        requires(n <= 1000);
        let result = 0x42::tree::measure(n);
        ensures(result == n);
        result
    }
}
