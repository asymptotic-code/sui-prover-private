module 0x42::test {
    #[ext(pure)]
    public fun classify(x: u64, y: u64): bool {
        if (x == 0) {
            return true
        };
        let mut acc = y;
        if (y > 100) {
            acc = y - 100;
        };
        acc > x
    }
}
