// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
// The empty constructor is a genuine recursion base: a dynamic-field value
// may contain the UID that owns this table. Requiring a total array of V even
// for an empty table would make that recursive datatype uninhabited.
datatype Table <K, V> {
    Table(v: [K]V, e: [K]bool, l: int),
    EmptyTableValue()
}

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    EmptyTableValue()
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    if t is Table then t->v[k] else DefaultTableArray()[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    if t is Table then t->l else 0
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    if t is Table then t->e[k] else false
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    if t is Table then Table(t->v[k := v], t->e, t->l)
    else Table(DefaultTableArray()[k := v], DefaultTableKeyExistsArray(), 0)
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    if t is Table then Table(t->v[k := v], t->e[k := true], t->l + 1)
    else Table(DefaultTableArray()[k := v], DefaultTableKeyExistsArray()[k := true], 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    if t is Table then Table(t->v, t->e[k := false], t->l - 1)
    else Table(DefaultTableArray(), DefaultTableKeyExistsArray(), -1)
}

axiom {:ctor "Table"} (forall<K,V> t: Table K V :: {LenTable(t)}
    (exists k: K :: {ContainsTable(t, k)} ContainsTable(t, k)) ==> LenTable(t) >= 1
);
// TODO: we might want to encoder a stronger property that the length of table
// must be more than N given a set of N items. Currently we don't see a need here
// and the above axiom seems to be sufficient.
