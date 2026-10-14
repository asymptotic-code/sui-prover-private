//! Quantifiers (Move spec macros).
//!
//! See `plans/lean-pipeline/ir.md` "Quantifiers" section. The 23 flat
//! variants in the legacy `QuantifierKind` collapse into 11 kinds
//! crossed with 3 domains via `QuantDomain`.

use super::expr::Expr;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum QuantifierKind {
    Forall,
    Exists,
    Any,
    All,
    Find,
    FindIndex,
    FindIndices,
    Map,
    Filter,
    Count,
    SumMap,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum QuantDomain {
    /// `Forall x : T, ...` -- domain is the entire type.
    Unbounded,
    /// `Forall i in start..end, ...`.
    Range { start: Box<Expr>, end: Box<Expr> },
    /// `Forall x in vec, ...`.
    Collection(Box<Expr>),
    /// `<op>_range!(vec, start, end, |x| ...)` -- iterate the elements
    /// of `vec` restricted to the index window `[start, end)`. The
    /// binder ranges over ELEMENTS (not indices); distinct from `Range`,
    /// whose binder is the index (`range_count!`/`range_map!`).
    VecRange {
        vec: Box<Expr>,
        start: Box<Expr>,
        end: Box<Expr>,
    },
}
