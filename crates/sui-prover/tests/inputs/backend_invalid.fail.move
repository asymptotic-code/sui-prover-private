module 0x42::backend_invalid_test;

public fun foo() {
    assert!(true);
}

// This spec has an invalid backend value and should produce an error
#[ext(backend=b"z3")]
#[spec(prove)]
public fun foo_spec_invalid() {
    foo();
}
