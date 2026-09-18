module 0x42::backend_run_on_value_test;

public fun foo() {
    assert!(true);
}

// backend is given a run location; the error should point at the run_on attribute
#[mode(spec), ext(spec(prove), backend=b"local")]
public fun foo_spec_invalid() {
    foo();
}
