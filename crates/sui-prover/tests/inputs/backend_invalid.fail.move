module 0x42::backend_invalid_test;

public fun foo() {
    assert!(true);
}

// This spec has an invalid backend value and should produce an error
#[mode(spec), ext(spec(prove), backend=b"z3")]
public fun foo_spec_invalid() {
    foo();
}
