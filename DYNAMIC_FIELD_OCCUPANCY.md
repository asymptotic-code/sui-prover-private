# Boogie dynamic-field occupancy repair

Dynamic-field keys identify a slot independently of the stored value type. Previously each `(Name, Value)` table supplied its own add guard, so an existing value of a different type did not prevent insertion. Untyped existence was an unrelated uninterpreted predicate with only a typed-to-untyped implication.

The model now stores an occupancy table per name type alongside the typed payload tables. Unknown value types are representable by occupied slots without a tracked payload. Fresh construction initializes every occupancy table empty; ordinary field and payload updates preserve occupancy. Add checks and marks occupancy; successful remove and remove_opt clear it. Untyped existence reads occupancy directly, including programs using only untyped queries. Payload reads and mutable writeback retain their typed semantics.

Object validity relates each typed entry to occupancy and excludes simultaneous entries for distinct closed value types. It deliberately does not declare open generic types disjoint, because they can alias. These are validity conditions, not universal datatype axioms; intermediate updates and arbitrary datatype values remain satisfiable. The existing empty-table base for recursive UID values remains unchanged.

Legacy insertion fixtures that required only typed absence now require untyped absence: this corrects their runtime precondition rather than hiding a failure. A dedicated negative regression preserves typed absence and requires the prover to reject the insufficient precondition.

Validation (release integration runner, real Boogie/Z3):
- 45 dynamic-field tests, including positive exact add/setter guards, fresh absence, remove/re-add across value types, wrong-type collision, unknown-value collision, and a rejected false postcondition.
- 10 dynamic-object-field tests.
- 18 table/object-table tests.
- Prior recursive-UID false-postcondition regression remains rejected.
- Unchanged gateway mint contract f457d6fc2 passes Check, Assume, and SpecNoAbortCheck with this model; an isolated ensures(false) probe fails Check while Assume and SpecNoAbortCheck pass. Full logs are /tmp/gateway-mint-occupancy.log and /tmp/gateway-mint-occupancy-false.log in the development workspace.

No installed binary or production Move implementation is changed. The gateway contract retains its exact `!exists<Name> || exists_with_type<Name, Value>` abort guard.
