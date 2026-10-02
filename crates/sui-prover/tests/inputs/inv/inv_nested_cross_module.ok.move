module 0x42::a {
    public struct Inner has copy, drop {
        v: u64,
    }

    public struct Outer has copy, drop {
        inner: Inner,
    }

    public fun value(o: &Outer): u64 {
        o.inner.v
    }
}

module 0x42::a_specs {
    use 0x42::a::{Self, Inner, Outer};

    #[mode(spec), ext(spec_only(inv_target = a::Inner))]
    #[allow(unused_function)]
    fun inner_inv(_s: &Inner): bool {
        true
    }

    #[mode(spec), ext(spec(prove))]
    fun value_spec(o: &Outer): u64 {
        a::value(o)
    }
}
