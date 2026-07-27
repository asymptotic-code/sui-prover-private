module 0x42::run_on_backend_value_test;

public fun foo() {
    assert!(true);
}

// run_on is given a backend name; the error should point at the backend attribute
#[spec(prove, run_on=b"lean")]
public fun foo_spec_invalid() {
    foo();
}
