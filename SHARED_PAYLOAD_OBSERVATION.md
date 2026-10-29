The share_object_impl success contract now records the last shared object of each concrete type in SpecShareObject<T>. The native ownership transition preserves the Move value bytes; the ghost snapshot observes that value without returning or duplicating a runtime object. SpecShareAddress and SpecShareAddressExists retain their existing meaning.

Callers using the sharing model must declare the three observation globals, including SpecShareObject<SharedType> with value SharedType. The two older address-observation fixtures now declare this additional channel.

This does not model ESharedNonNewObject or claim arbitrary owned objects may be shared. The fresh-object fixture allocates then immediately shares in the same transaction. A generic share wrapper still needs a sound native freshness model for full abort coverage. Gateway parking-lot construction is specifically a fresh-create-then-share path.

Regression coverage includes initialized payload equality, a deliberately false payload inequality, existing address observations, and isolated false-postcondition rejection. Tests must be rerun without INSTA_UPDATE after reviewing snapshots; snapshot acceptance alone is not proof success.
