module 0x42::test {
    #[ext(pure)]
    public fun eligible(a: u64, b: u64, cap: u64): bool {
        if (a == 0) {
            return true
        };
        if (b == 0) {
            return true
        };
        let mut room = cap;
        if (cap > a) {
            room = cap - a;
        };
        room >= b
    }
}
