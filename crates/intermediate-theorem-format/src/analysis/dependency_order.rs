// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Topological sorting of functions and structs by dependency order

use crate::data::{Dependable, Program};
use indexmap::IndexMap;
use petgraph::algo::{condensation, toposort};
use petgraph::graphmap::DiGraphMap;
use std::collections::hash_map::RandomState;
use std::collections::HashSet;

pub fn order_by_dependencies(program: &mut Program) {
    topological_sort(&mut program.structs.items);
    topological_sort(program.functions.functions_mut());
}

fn topological_sort<T: Dependable>(items: &mut IndexMap<T::Id, T>) {
    // Build graph including ALL nodes, even those with no edges
    let mut graph = DiGraphMap::<T::Id, (), RandomState>::with_capacity(items.len(), 0);

    // Add all nodes first
    for id in items.keys() {
        graph.add_node(*id);
    }

    // Collect self-edges BEFORE condensation (which strips them with make_acyclic=true)
    let mut has_self_edge: HashSet<T::Id> = HashSet::new();

    // Then add edges (only where both endpoints exist)
    for (id, item) in items.iter() {
        for dep in item.dependencies() {
            if items.contains_key(&dep) {
                graph.add_edge(dep, *id, ());
                if dep == *id {
                    has_self_edge.insert(*id);
                }
            }
        }
    }

    let mut condensed = condensation(graph.into_graph::<u32>(), true);

    let sorted_groups: Vec<_> = toposort(&condensed, None)
        .unwrap()
        .into_iter()
        .map(|node| condensed.remove_node(node).unwrap())
        .enumerate()
        .collect();

    *items = sorted_groups
        .into_iter()
        .flat_map(|(group_id, group)| {
            let group_size = group.len();
            group.into_iter().map(move |id| (id, group_id, group_size))
        })
        .map(|(id, group_id, group_size)| {
            let item = items.swap_remove(&id).unwrap();
            let is_recursive = group_size > 1 || has_self_edge.contains(&id);

            // Always recompute mutual_group_id from the current SCC analysis. (We
            // used to preserve existing values for "while/after_while functions" but
            // nothing pre-sets these any more — and preserving leaves stale groups
            // around after `optimize_all` removes calls that previously formed
            // cycles.)
            let mutual_group_id = if group_size > 1 || has_self_edge.contains(&id) {
                Some(group_id)
            } else {
                None
            };
            (id, item.with_recursion_info(mutual_group_id, is_recursive))
        })
        .collect();
}
