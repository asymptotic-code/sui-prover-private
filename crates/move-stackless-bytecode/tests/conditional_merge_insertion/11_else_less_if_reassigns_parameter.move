// Regression: a `mut` PARAMETER reassigned inside else-less `if`s.
//
// Every other case in this directory reassigns a LOCAL that was assigned
// before the first branch (`let mut result = 0;`), which puts it in
// `assigned_before` and therefore in `else_known`. A parameter is well
// defined on entry but is never "assigned before", so it used to be absent
// from `else_known`; `compute_completed_at` then recorded no merge point for
// it while `process_if_then_else` created a merge anyway, and the two phases
// disagreed.
//
// Shape lifted from `bit_math::most_significant_bit`, which is what this
// actually crashed on:
//
//     else_ver is the original variable 0 at pc 17
//
// `value` is the parameter; `result` is a local, kept so the case exercises
// both kinds of variable through the same ladder.
module 0x42::test {
    public fun f(mut value: u64): u64 {
        let mut result = 0;

        if (value >= 4294967296) {
            value = value >> 32;
            result = result + 32;
        };

        if (value >= 65536) {
            value = value >> 16;
            result = result + 16;
        };

        if (value >= 256) {
            value = value >> 8;
            result = result + 8;
        };

        result
    }
}
