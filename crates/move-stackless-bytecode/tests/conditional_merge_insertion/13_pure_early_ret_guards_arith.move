// An early `return` that GUARDS downstream arithmetic must leave that
// arithmetic under the guard. The two functions are the same function written
// two ways, and after the pass their bodies must agree: `-` reachable only on
// the `a > b` path. Linearizing the early return (rewriting `Ret` to `Nop`
// instead of jumping to the exit) puts the subtraction on every path and
// invents a no-abort obligation the source cannot reach.
module 0x42::test {
    #[ext(pure)]
    public fun guarded_sub_early(a: u64, b: u64): u64 {
        if (a <= b) {
            return 0
        };
        a - b
    }

    #[ext(pure)]
    public fun guarded_sub_nested(a: u64, b: u64): u64 {
        if (a <= b) {
            0
        } else {
            a - b
        }
    }

    // Two guards in sequence: `a - 1` is guarded by the first return and
    // `x + 10` / `x + c` are the two arms of the second.
    #[ext(pure)]
    public fun three_way_early(a: u64, b: u64, c: u64): u64 {
        if (a == 0) {
            return 0
        };
        let x = a - 1;
        if (b == 0) {
            return x + 10
        };
        x + c
    }
}
