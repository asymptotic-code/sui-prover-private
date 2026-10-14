//! Quantifier translation helpers.
//!
//! Maps upstream's 23-variant
//! [`QuantifierType`](move_stackless_bytecode::stackless_bytecode::QuantifierType)
//! into our 11-kind × 3-domain shape
//! ([`QuantifierKind`](crate::ir::QuantifierKind) ×
//! [`QuantDomain`](crate::ir::QuantDomain)). See decision-log §11 in
//! `plans/lean-pipeline/ir.md`.
//!
//! Full quantifier lifting also needs the lambda body --
//! upstream's `Operation::Quantifier(kind, lambda_qid, type_args, slot)`
//! references a callback function whose body contains a
//! `__qi`-marked argument that we substitute with the actual binder.
//! That substitution path lands when the rest of the per-op
//! translator is wired; this module supplies the kind/domain mapping
//! piece in isolation so it has its own tests.

use move_stackless_bytecode::stackless_bytecode::QuantifierType;

use crate::ir::QuantifierKind;

/// Domain hint inferred from the upstream `QuantifierType`. The
/// quantifier op also carries a runtime arg (the actual range or
/// collection); the caller uses this hint to decide how to shape
/// the [`QuantDomain`](crate::ir::QuantDomain) it builds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantDomainHint {
    /// `forall x : T, p(x)` -- no bounded domain. Only `Forall` and
    /// `Exists` upstream variants produce this.
    Unbounded,
    /// `forall i in start..end, p(i)` -- binder is the INDEX
    /// (`range_count!` / `range_map!` / `range_sum_map!`).
    Range,
    /// `forall x in collection, p(x)`.
    Collection,
    /// `<op>_range!(vec, start, end, |x| p(x))` -- binder ranges over
    /// the ELEMENTS of `vec` in the index window `[start, end)`.
    VecRange,
}

/// Lift an upstream [`QuantifierType`] into the
/// (kind, domain hint) pair our IR uses.
pub fn translate_quantifier_kind(qt: QuantifierType) -> (QuantifierKind, QuantDomainHint) {
    use QuantDomainHint::*;
    use QuantifierKind as Q;
    match qt {
        QuantifierType::Forall => (Q::Forall, Unbounded),
        QuantifierType::Exists => (Q::Exists, Unbounded),

        // `*Range` macros take a vec + an index window -> VecRange.
        // `Range*` macros are index-only (no vec) -> Range.
        QuantifierType::Map => (Q::Map, Collection),
        QuantifierType::MapRange => (Q::Map, VecRange),
        QuantifierType::RangeMap => (Q::Map, Range),

        QuantifierType::Filter => (Q::Filter, Collection),
        QuantifierType::FilterRange => (Q::Filter, VecRange),

        QuantifierType::Find => (Q::Find, Collection),
        QuantifierType::FindRange => (Q::Find, VecRange),

        QuantifierType::FindIndex => (Q::FindIndex, Collection),
        QuantifierType::FindIndexRange => (Q::FindIndex, VecRange),

        QuantifierType::FindIndices => (Q::FindIndices, Collection),
        QuantifierType::FindIndicesRange => (Q::FindIndices, VecRange),

        QuantifierType::Count => (Q::Count, Collection),
        QuantifierType::CountRange => (Q::Count, VecRange),
        QuantifierType::RangeCount => (Q::Count, Range),

        QuantifierType::Any => (Q::Any, Collection),
        QuantifierType::AnyRange => (Q::Any, VecRange),

        QuantifierType::All => (Q::All, Collection),
        QuantifierType::AllRange => (Q::All, VecRange),

        QuantifierType::SumMap => (Q::SumMap, Collection),
        QuantifierType::SumMapRange => (Q::SumMap, VecRange),
        QuantifierType::RangeSumMap => (Q::SumMap, Range),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Upstream has 23 variants; verify each lands in our 11-kind ×
    /// 3-domain space and the `Range`/`Unbounded` hint matches the
    /// upstream's own naming convention (`*Range` / `Range*` -> Range,
    /// bare Forall/Exists -> Unbounded, everything else -> Collection).
    #[test]
    fn every_upstream_variant_maps() {
        use QuantDomainHint as D;
        use QuantifierKind as Q;
        use QuantifierType as U;

        let cases: &[(U, Q, D)] = &[
            (U::Forall, Q::Forall, D::Unbounded),
            (U::Exists, Q::Exists, D::Unbounded),
            (U::Map, Q::Map, D::Collection),
            (U::MapRange, Q::Map, D::VecRange),
            (U::RangeMap, Q::Map, D::Range),
            (U::Filter, Q::Filter, D::Collection),
            (U::FilterRange, Q::Filter, D::VecRange),
            (U::Find, Q::Find, D::Collection),
            (U::FindRange, Q::Find, D::VecRange),
            (U::FindIndex, Q::FindIndex, D::Collection),
            (U::FindIndexRange, Q::FindIndex, D::VecRange),
            (U::FindIndices, Q::FindIndices, D::Collection),
            (U::FindIndicesRange, Q::FindIndices, D::VecRange),
            (U::Count, Q::Count, D::Collection),
            (U::CountRange, Q::Count, D::VecRange),
            (U::RangeCount, Q::Count, D::Range),
            (U::Any, Q::Any, D::Collection),
            (U::AnyRange, Q::Any, D::VecRange),
            (U::All, Q::All, D::Collection),
            (U::AllRange, Q::All, D::VecRange),
            (U::SumMap, Q::SumMap, D::Collection),
            (U::SumMapRange, Q::SumMap, D::VecRange),
            (U::RangeSumMap, Q::SumMap, D::Range),
        ];
        // Upstream has 23 variants; pin the count so this test fails
        // loudly if upstream adds another we forgot to map.
        assert_eq!(cases.len(), 23);
        for &(u, expected_kind, expected_domain) in cases {
            let (k, d) = translate_quantifier_kind(u);
            assert_eq!(
                (k, d),
                (expected_kind, expected_domain),
                "upstream {u:?} mapped wrong"
            );
        }
    }

    #[test]
    fn forall_and_exists_are_unbounded() {
        assert_eq!(
            translate_quantifier_kind(QuantifierType::Forall),
            (QuantifierKind::Forall, QuantDomainHint::Unbounded)
        );
        assert_eq!(
            translate_quantifier_kind(QuantifierType::Exists),
            (QuantifierKind::Exists, QuantDomainHint::Unbounded)
        );
    }

    #[test]
    fn vec_range_and_index_range_do_not_unify() {
        // `MapRange` (`map_range!(vec, ..)`, vec over a window) and
        // `RangeMap` (`range_map!(start, end, ..)`, index-only) are
        // DISTINCT domains -- VecRange vs Range -- because the former
        // needs the vec and the latter doesn't.
        let mr = translate_quantifier_kind(QuantifierType::MapRange);
        let rm = translate_quantifier_kind(QuantifierType::RangeMap);
        assert_eq!(mr, (QuantifierKind::Map, QuantDomainHint::VecRange));
        assert_eq!(rm, (QuantifierKind::Map, QuantDomainHint::Range));
        assert_ne!(mr, rm);
    }
}
