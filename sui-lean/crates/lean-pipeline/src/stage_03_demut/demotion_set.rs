//! Demotion-set computation: which functions need stage 3 to demote
//! their signatures, and what shape that demotion takes.
//!
//! SCC-aware: within a strongly connected component of the call
//! graph, if any non-native function takes / returns `&mut`, every
//! non-native function in the SCC is demoted together. Otherwise,
//! signature inconsistencies leak across the SCC boundary and
//! mutually-recursive call sites can't resolve.
//!
//! Native functions are exempt -- they correspond to hand-written
//! Lean prelude code that operates on `Mutable<V, S>` wrappers
//! directly.
//!
//! See `plans/lean-pipeline/stage-03-demut.md` "Sub-pass A" for the
//! algorithm.

use std::collections::{BTreeMap, BTreeSet};

use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;

use crate::ir::visit::{walk_block_default, walk_expr_default, Visitor};
use crate::ir::{Block, Expr, FunId, Function, Program, Type};

use super::signatures::{classify, DemotionPattern};

/// Per-function demotion metadata. Built from the pre-demotion
/// signature so call-site rewriting can locate the original
/// `&mut`-typed param positions even after `demote_signature` has
/// mutated the signature in place.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunDemotion {
    pub pattern: DemotionPattern,
    /// Indices of `&mut`-typed params in the original signature
    /// (before stripping). Order preserved.
    pub mut_param_indices: Vec<usize>,
    /// `inner` types of those `&mut`-typed params. Same length as
    /// `mut_param_indices`. Used by the augmented-return wiring.
    pub mut_param_inner_types: Vec<Type>,
}

/// Demotion-map: every demoted FunId mapped to its demotion shape.
/// Empty entries (e.g. natives, untouched functions) are absent --
/// callers should treat absence as "not demoted".
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DemotionMap {
    funs: BTreeMap<FunId, FunDemotion>,
}

impl DemotionMap {
    /// True if `fid` is in the demotion set.
    pub fn is_demoted(&self, fid: FunId) -> bool {
        self.funs.contains_key(&fid)
    }

    /// Look up `fid`'s demotion shape, or `None` if not demoted.
    pub fn info(&self, fid: FunId) -> Option<&FunDemotion> {
        self.funs.get(&fid)
    }

    /// All demoted FunIds in deterministic order.
    pub fn demoted(&self) -> impl Iterator<Item = FunId> + '_ {
        self.funs.keys().copied()
    }

    /// Number of demoted functions.
    pub fn len(&self) -> usize {
        self.funs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.funs.is_empty()
    }

    /// As a plain `BTreeSet<FunId>` -- the legacy "demotion set"
    /// shape for simple membership-only queries.
    pub fn as_set(&self) -> BTreeSet<FunId> {
        self.funs.keys().copied().collect()
    }
}

/// Compute the demotion map for `program`. Built from the current
/// (un-demoted) state of every signature; safe to call before any
/// signature has been mutated by stage 3.
///
/// A non-native function joins the demotion set if either:
/// - it has a `Type::MutableRef`-typed parameter, or
/// - it has a `Type::MutableRef`-typed return, or
/// - it shares an SCC with another function that does (and is itself
///   non-native -- natives in the SCC are skipped).
pub fn compute(program: &Program) -> DemotionMap {
    let mut graph: DiGraphMap<FunId, ()> = DiGraphMap::new();
    for &id in program.functions.keys() {
        graph.add_node(id);
    }
    for (&caller, func) in &program.functions {
        let mut collector = CalleeCollector {
            callees: BTreeSet::new(),
        };
        collector.visit_block(&func.body);
        for callee in collector.callees {
            if program.functions.contains_key(&callee) {
                graph.add_edge(caller, callee, ());
            }
        }
    }

    let sccs: Vec<Vec<FunId>> = tarjan_scc(&graph);

    // Per-SCC: does any non-native member take or return `&mut`?
    let mut scc_demoted = vec![false; sccs.len()];
    for (idx, scc) in sccs.iter().enumerate() {
        for &fid in scc {
            let func = &program.functions[&fid];
            if has_mut_in_signature(func) {
                scc_demoted[idx] = true;
                break;
            }
        }
    }

    // Build per-function demotion info for every non-native member of
    // a demoted SCC.
    let mut funs: BTreeMap<FunId, FunDemotion> = BTreeMap::new();
    for (idx, scc) in sccs.iter().enumerate() {
        if !scc_demoted[idx] {
            continue;
        }
        for &fid in scc {
            let func = &program.functions[&fid];
            funs.insert(fid, info_for(func));
        }
    }
    DemotionMap { funs }
}

fn info_for(func: &Function) -> FunDemotion {
    let pattern = classify(func);
    let mut mut_param_indices = Vec::new();
    let mut mut_param_inner_types = Vec::new();
    for (i, p) in func.signature.params.iter().enumerate() {
        if let Type::MutableRef { inner, .. } = &p.ty {
            mut_param_indices.push(i);
            mut_param_inner_types.push((**inner).clone());
        }
    }
    FunDemotion {
        pattern,
        mut_param_indices,
        mut_param_inner_types,
    }
}

/// True if `func`'s signature mentions `Type::MutableRef` in any
/// parameter or in the return position.
fn has_mut_in_signature(func: &Function) -> bool {
    if func
        .signature
        .params
        .iter()
        .any(|p| type_contains_mut_ref(&p.ty))
    {
        return true;
    }
    type_contains_mut_ref(&func.signature.return_type)
}

/// True if `t` (or a top-level `Tuple` component of it) is
/// `Type::MutableRef`.
fn type_contains_mut_ref(t: &Type) -> bool {
    match t {
        Type::MutableRef { .. } => true,
        Type::Tuple(items) => items.iter().any(type_contains_mut_ref),
        _ => false,
    }
}

/// Walks a function body and records every `FunId` reached via
/// `Expr::Call`.
struct CalleeCollector {
    callees: BTreeSet<FunId>,
}

impl Visitor for CalleeCollector {
    fn visit_block(&mut self, b: &Block) {
        walk_block_default(self, b);
    }

    fn visit_expr(&mut self, e: &Expr) {
        if let Expr::Call { fun, .. } = e {
            self.callees.insert(*fun);
        }
        walk_expr_default(self, e);
    }
}
