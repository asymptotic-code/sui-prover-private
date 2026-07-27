module 0x42::backend_run_on_value_test;

public fun foo() {
    assert!(true);
}

// backend is given a run location; the error should point at the run_on attribute
#[ext(backend=b"local")]
#[spec(prove)]
public fun foo_spec_invalid() {
    foo();
}
