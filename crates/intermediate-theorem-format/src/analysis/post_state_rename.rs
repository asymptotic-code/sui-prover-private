// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Distinguish post-state rebinds of `&mut` parameters in `.ensures` functions.
//!
//! `mutable_threading` rebinds a `&mut` parameter to its post-call value by
//! SHADOWING it: `let self := __mut_ret`. A pre-state snapshot the spec author
//! captured before the call (`let old := value(self)`) is then unsafe to inline
//! past that shadow — the inlined `value(self)` would read the post-state. This
//! is exactly the bug that made `join_fungible_staked_sui.ensures` /
//! `split_fungible_staked_sui.ensures_1` generate the false goal `(v) == (v) + …`.
//!
//! This pass gives the post-call rebind a DISTINCT name (`<p>_post`) instead of
//! shadowing, and rewrites the downstream (post-call) references to it. Pre-call
//! references — the snapshots — keep the original parameter name, so they remain
//! pre-state no matter how the optimizer later inlines them. Scoped to
//! `.ensures` functions (where pre-state snapshots live); runs after
//! `extract_all_specs` and before `optimize_all`.

use crate::data::Program;
use crate::{IRNode, TempId};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

pub fn distinguish_param_rebinds_in_ensures(program: &mut Program) {
    let ids: Vec<usize> = program
        .functions
        .iter()
        .filter(|(_, f)| !f.is_native && f.name.contains(".ensures"))
        .map(|(id, _)| id)
        .collect();
    for id in ids {
        let params: BTreeSet<String> = {
            let f = program.functions.get(&id);
            f.signature
                .parameters
                .iter()
                .flat_map(|p| [p.ssa_value.to_string(), p.name.clone()])
                .collect()
        };
        if params.is_empty() {
            continue;
        }
        let body = std::mem::take(&mut program.functions.get_mut(id).body);
        let mut counter = 0usize;
        let new_body = rename_rebinds(body, &params, &mut counter);
        program.functions.get_mut(id).body = new_body;
    }
}

fn fresh(base: &str, counter: &mut usize) -> TempId {
    let n = *counter;
    *counter += 1;
    let suffix = if n == 0 {
        String::new()
    } else {
        format!("{}", n)
    };
    Rc::from(format!("{}_post{}", base, suffix).as_str())
}

/// Recursively rename the first rebind of each `&mut` parameter (and downstream
/// uses) to a fresh `_post` name. A pre-state snapshot before the rebind keeps
/// the original name.
fn rename_rebinds(node: IRNode, params: &BTreeSet<String>, counter: &mut usize) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // WriteBack rebind: empty pattern, parent is a parameter. The render
            // honors the (now non-empty) pattern as the bind name; the WriteBack
            // value still sources the pre-state `parent`.
            if pattern.is_empty() {
                if let IRNode::WriteBack { parent, .. } = value.as_ref() {
                    if params.contains(parent.as_ref()) {
                        let post = fresh(parent.as_ref(), counter);
                        let subs: BTreeMap<String, String> =
                            [(parent.to_string(), post.to_string())]
                                .into_iter()
                                .collect();
                        let body = body.substitute_vars(&subs);
                        let body = rename_rebinds(body, params, counter);
                        return IRNode::Let {
                            pattern: vec![post],
                            value,
                            body: Box::new(body),
                        };
                    }
                }
            }
            // Plain rebind: a parameter name appears in the Let pattern.
            let rebinds: Vec<(usize, String)> = pattern
                .iter()
                .enumerate()
                .filter(|(_, p)| params.contains(p.as_ref()))
                .map(|(i, p)| (i, p.to_string()))
                .collect();
            if !rebinds.is_empty() {
                let value = Box::new(rename_rebinds(*value, params, counter));
                let mut new_pattern = pattern;
                let mut subs: BTreeMap<String, String> = BTreeMap::new();
                for (i, p) in &rebinds {
                    let post = fresh(p, counter);
                    subs.insert(p.clone(), post.to_string());
                    new_pattern[*i] = post;
                }
                let body = body.substitute_vars(&subs);
                let body = rename_rebinds(body, params, counter);
                return IRNode::Let {
                    pattern: new_pattern,
                    value,
                    body: Box::new(body),
                };
            }
            IRNode::Let {
                pattern,
                value: Box::new(rename_rebinds(*value, params, counter)),
                body: Box::new(rename_rebinds(*body, params, counter)),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(rename_rebinds(*then_branch, params, counter)),
            else_branch: Box::new(rename_rebinds(*else_branch, params, counter)),
        },
        other => other,
    }
}
