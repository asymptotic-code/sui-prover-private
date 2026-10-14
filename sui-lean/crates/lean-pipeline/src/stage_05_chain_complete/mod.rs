//! Stage 5c -- writeback chain COMPLETION
//! (`plans/lean-pipeline/writeback-lowering.md`, S4b).
//!
//! Upstream's memory instrumentation emits isParent-dispatched root
//! writeback chains at most merge sites, but leaves the LOOP-TAIL
//! merge clusters tracker-deep: the alias trackers are written back,
//! the roots never are, and the loop recurses with stale roots
//! (MoveSTL skip_list insert/remove -- formerly compensated by
//! byte-exact render-text patches in `render/mod.rs`).
//!
//! The completion WIDENS THE EXISTING CLUSTER MERGES IN PLACE,
//! replicating the (empirically proven) patch structure with chains
//! and participants extracted from the function's own COMPLETE merge
//! templates:
//!
//! - merge-A (updates the root-reaching tracker U_A, e.g. the level
//!   vector `$t5`): its then-arm gains a path dispatch
//!   `if is_parent(headBridge, U_A') { root.f_head := .. } else
//!   { node.f_nexts := U_A'; table[key] := node; root.f_inner := .. }`
//!   yielding `root'`; A widens by one slot.
//! - merge-B (updates the node-nexts tracker U_B == the node
//!   template's bridge): its then-arm gains, UNCONDITIONALLY under
//!   B's own guard, the U_B node chain rooted at `root'`, PLUS the
//!   cross-tracker sync `U_A := U_B'` (tail sites don't re-borrow,
//!   unlike the complete inner sites); B widens by
//!   (root'', tableMut', U_A_sync).
//!
//! Runs post-SSA (fresh `__wbc` binders keep uniqueness) and
//! pre-stage-7 (the loop tail IS the threading). Cluster sites inside
//! SSA phi arms get the enclosing phi pattern EXTENDED and downstream
//! uses of the pre-phi versions substituted (sound post-SSA).
//!
//! Conservative skip-on-doubt: missing templates, unresolved roles,
//! missing versions, or unexpected shapes leave the site untouched.

use std::collections::BTreeMap;

use crate::ir::borrow::{BorrowEdge, BorrowNode};
use crate::ir::expr::{Block, BlockTail, Expr, Stmt};
use crate::ir::{Program, Type, VarId};
use crate::stage_06_let_inline::substitute::{substitute_var_in_stmt, substitute_var_in_tail};

pub fn run(program: &mut Program) {
    let fids: Vec<_> = program.functions.keys().copied().collect();
    for fid in fids {
        let f = program.functions.get_mut(&fid).expect("fid present");
        let roots: Vec<String> = f
            .signature
            .params
            .iter()
            .filter_map(|p| match &p.ty {
                Type::MutableRef { inner, root } if inner == root => Some(family(&p.var)),
                _ => None,
            })
            .collect();
        if roots.is_empty() {
            continue;
        }
        let mut templates: Vec<Template> = Vec::new();
        collect_templates(&f.body, &roots, &mut templates);
        // Need a head route (2-chain) and a node route (4-chain) for
        // the same child family.
        let pairs: Vec<(Template, Template)> = templates
            .iter()
            .filter(|t| t.chain.len() == 2)
            .flat_map(|h| {
                templates
                    .iter()
                    .filter(|n| n.chain.len() == 4 && n.child_family == h.child_family)
                    .map(|n| (h.clone(), n.clone()))
            })
            .collect();
        if pairs.is_empty() {
            continue;
        }
        let mut fresh = 0usize;
        let mut cur: BTreeMap<String, VarId> = f
            .signature
            .params
            .iter()
            .map(|p| (family(&p.var), p.var.clone()))
            .collect();
        complete_block(&mut f.body, &pairs, &mut fresh, &mut cur);
    }
}

fn family(v: &VarId) -> String {
    let s: &str = v.as_ref();
    match s.rfind('_') {
        Some(i) if i > 0 && s[i + 1..].chars().all(|c| c.is_ascii_digit()) => s[..i].to_string(),
        _ => s.to_string(),
    }
}

/// One complete merge shape: dispatch on `child_family` against
/// `bridge_family`; the then-arm chain (in order) targets
/// `chain[k].0` via `chain[k].1`; the last entry is a root family.
#[derive(Clone, Debug)]
struct Template {
    child_family: String,
    bridge_family: String,
    chain: Vec<(String, BorrowEdge)>,
}

struct Merge<'a> {
    if_idx: usize,
    child: &'a VarId,
    bridge: &'a VarId,
    wbs: Vec<(&'a VarId, &'a VarId, &'a VarId, &'a BorrowEdge)>,
    pattern: &'a [Option<VarId>],
}

fn parse_merge<'a>(stmts: &'a [Stmt], i: usize) -> Option<Merge<'a>> {
    let Stmt::Let {
        pattern: cpat,
        value:
            Expr::IsParent {
                node: BorrowNode::Reference(bridge) | BorrowNode::LocalRoot(bridge),
                child,
                ..
            },
    } = &stmts[i]
    else {
        return None;
    };
    let [Some(cvar)] = cpat.as_slice() else {
        return None;
    };
    let Some(Stmt::Let {
        pattern,
        value: Expr::If {
            cond, then_branch, ..
        },
    }) = stmts.get(i + 1)
    else {
        return None;
    };
    if !matches!(cond.as_ref(), Expr::Var(v) if v == cvar) {
        return None;
    }
    let mut wbs = Vec::new();
    for s in &then_branch.stmts {
        if let Stmt::Let {
            pattern: wpat,
            value:
                Expr::WriteBack {
                    node: BorrowNode::Reference(t) | BorrowNode::LocalRoot(t),
                    edge,
                    child: wc,
                    world: None,
                },
        } = s
        {
            if let [Some(out)] = wpat.as_slice() {
                wbs.push((out, t, wc, edge));
            }
        }
    }
    Some(Merge {
        if_idx: i + 1,
        child,
        bridge,
        wbs,
        pattern,
    })
}

fn collect_templates(b: &Block, roots: &[String], out: &mut Vec<Template>) {
    let mut i = 0;
    while i < b.stmts.len() {
        if let Some(m) = parse_merge(&b.stmts, i) {
            if let Some(t) = template_from(&m, roots) {
                if !out
                    .iter()
                    .any(|x| x.child_family == t.child_family && x.chain.len() == t.chain.len())
                {
                    out.push(t);
                }
            }
            i = m.if_idx + 1;
            continue;
        }
        i += 1;
    }
    for s in &b.stmts {
        let e = match s {
            Stmt::Let { value, .. } => value,
            Stmt::Eval(e) => e,
        };
        collect_templates_expr(e, roots, out);
    }
    if let BlockTail::Value(e) = &b.tail {
        collect_templates_expr(e, roots, out);
    }
}

fn collect_templates_expr(e: &Expr, roots: &[String], out: &mut Vec<Template>) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_templates(then_branch, roots, out);
            collect_templates(else_branch, roots, out);
        }
        Expr::Match { cases, .. } => {
            for a in cases {
                collect_templates(&a.body, roots, out);
            }
        }
        Expr::While { header, body, .. } => {
            collect_templates(header, roots, out);
            collect_templates(body, roots, out);
        }
        Expr::LabeledBlock { body, .. } | Expr::Quantifier { body, .. } => {
            collect_templates(body, roots, out)
        }
        _ => {}
    }
}

fn template_from(m: &Merge<'_>, roots: &[String]) -> Option<Template> {
    if m.wbs.is_empty() {
        return None;
    }
    let mut chain = Vec::new();
    let mut prev = m.child;
    for (out, t, wc, e) in &m.wbs {
        if *wc != prev {
            return None;
        }
        chain.push((family(t), (*e).clone()));
        prev = out;
    }
    if !roots.contains(&chain.last().expect("nonempty").0) {
        return None;
    }
    if chain[0].0 != family(m.bridge) {
        return None;
    }
    Some(Template {
        child_family: family(m.child),
        bridge_family: family(m.bridge),
        chain,
    })
}

// ---------------------------------------------------------------
// Completion walk
// ---------------------------------------------------------------

fn complete_block(
    b: &mut Block,
    pairs: &[(Template, Template)],
    fresh: &mut usize,
    cur: &mut BTreeMap<String, VarId>,
) {
    // Forward pass: nested blocks see the running version map.
    for s in b.stmts.iter_mut() {
        let e = match s {
            Stmt::Let { value, .. } => value,
            Stmt::Eval(e) => e,
        };
        complete_expr(e, pairs, fresh, cur);
        if let Stmt::Let { pattern, .. } = s {
            for slot in pattern.iter().flatten() {
                cur.insert(family(slot), slot.clone());
            }
        }
    }
    match &mut b.tail {
        BlockTail::Value(e) => {
            if !matches!(e, Expr::Tuple(_)) {
                complete_expr(e, pairs, fresh, cur);
            }
        }
        BlockTail::Continue { value, .. } => {
            if !matches!(value.as_ref(), Expr::Tuple(_)) {
                complete_expr(value, pairs, fresh, cur);
            }
        }
        _ => {}
    }

    // Phi-arm sites (insert-style clusters inside If arms).
    complete_phi_arms(b, pairs, fresh, cur);

    // Direct tail site (remove-style cluster in a loop body that
    // ends in a loop-state tuple).
    let tail_is_tuple = matches!(&b.tail, BlockTail::Value(Expr::Tuple(_)))
        || matches!(&b.tail, BlockTail::Continue { value, .. } if matches!(value.as_ref(), Expr::Tuple(_)));
    if !tail_is_tuple {
        return;
    }
    let Some(updated) = widen_cluster_in(&mut b.stmts, pairs, fresh, cur) else {
        return;
    };
    let tail_mut: Option<&mut Expr> = match &mut b.tail {
        BlockTail::Continue { value, .. } => Some(value.as_mut()),
        BlockTail::Value(value) => Some(value),
        _ => None,
    };
    if let Some(Expr::Tuple(es)) = tail_mut {
        for slot in es.iter_mut() {
            if let Expr::Var(v) = slot {
                if let Some(nv) = updated.get(&family(v)) {
                    *slot = Expr::Var(nv.clone());
                }
            }
        }
    }
}

fn complete_expr(
    e: &mut Expr,
    pairs: &[(Template, Template)],
    fresh: &mut usize,
    cur: &BTreeMap<String, VarId>,
) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            complete_block(then_branch, pairs, fresh, &mut cur.clone());
            complete_block(else_branch, pairs, fresh, &mut cur.clone());
        }
        Expr::Match { cases, .. } => {
            for a in cases.iter_mut() {
                complete_block(&mut a.body, pairs, fresh, &mut cur.clone());
            }
        }
        Expr::While {
            header,
            body,
            iter_locals,
            ..
        } => {
            let mut c = cur.clone();
            for (binder, _) in iter_locals.iter() {
                c.insert(family(binder), binder.clone());
            }
            complete_block(header, pairs, fresh, &mut c.clone());
            complete_block(body, pairs, fresh, &mut c);
        }
        Expr::LabeledBlock { body, .. } | Expr::Quantifier { body, .. } => {
            complete_block(body, pairs, fresh, &mut cur.clone())
        }
        _ => {}
    }
}

/// Phi-arm completion: widen clusters inside the arms of a
/// multi-binder `let (..) = if .. {..} else {..}`, extend the
/// enclosing pattern for updated families without a slot, and
/// substitute downstream uses of the pre-phi versions.
fn complete_phi_arms(
    b: &mut Block,
    pairs: &[(Template, Template)],
    fresh: &mut usize,
    cur: &BTreeMap<String, VarId>,
) {
    let mut running: BTreeMap<String, VarId> = cur.clone();
    let mut idx = 0;
    while idx < b.stmts.len() {
        let is_phi = matches!(
            &b.stmts[idx],
            Stmt::Let { pattern, value: Expr::If { .. } } if pattern.len() > 1
        );
        if !is_phi {
            if let Stmt::Let { pattern, .. } = &b.stmts[idx] {
                for slot in pattern.iter().flatten() {
                    running.insert(family(slot), slot.clone());
                }
            }
            idx += 1;
            continue;
        }
        let mut all_updated: Vec<BTreeMap<String, VarId>> = Vec::new();
        let mut fired = false;
        {
            let Stmt::Let {
                value:
                    Expr::If {
                        then_branch,
                        else_branch,
                        ..
                    },
                ..
            } = &mut b.stmts[idx]
            else {
                unreachable!()
            };
            for arm in [then_branch.as_mut(), else_branch.as_mut()] {
                let upd = if matches!(&arm.tail, BlockTail::Value(Expr::Tuple(_))) {
                    widen_cluster_in(&mut arm.stmts, pairs, fresh, &running).unwrap_or_default()
                } else {
                    BTreeMap::new()
                };
                if !upd.is_empty() {
                    fired = true;
                }
                all_updated.push(upd);
            }
        }
        if !fired {
            if let Stmt::Let { pattern, .. } = &b.stmts[idx] {
                for slot in pattern.iter().flatten() {
                    running.insert(family(slot), slot.clone());
                }
            }
            idx += 1;
            continue;
        }
        let pattern_fams: Vec<String> = {
            let Stmt::Let { pattern, .. } = &b.stmts[idx] else {
                unreachable!()
            };
            pattern.iter().flatten().map(family).collect()
        };
        let mut extend: Vec<String> = Vec::new();
        for upd in &all_updated {
            for fam in upd.keys() {
                if !pattern_fams.contains(fam) && !extend.contains(fam) {
                    extend.push(fam.clone());
                }
            }
        }
        let mut new_binders: Vec<(String, VarId)> = Vec::new();
        for fam in &extend {
            *fresh += 1;
            let nb: VarId = format!("__wbc_p_{}_{}", fam.trim_start_matches('$'), fresh).into();
            new_binders.push((fam.clone(), nb));
        }
        {
            let Stmt::Let {
                pattern,
                value:
                    Expr::If {
                        then_branch,
                        else_branch,
                        ..
                    },
            } = &mut b.stmts[idx]
            else {
                unreachable!()
            };
            for (arm, upd) in [then_branch.as_mut(), else_branch.as_mut()]
                .into_iter()
                .zip(all_updated.iter())
            {
                let BlockTail::Value(Expr::Tuple(es)) = &mut arm.tail else {
                    return;
                };
                for slot in es.iter_mut() {
                    if let Expr::Var(v) = slot {
                        if let Some(nv) = upd.get(&family(v)) {
                            *slot = Expr::Var(nv.clone());
                        }
                    }
                }
                for (fam, _) in &new_binders {
                    let v = upd.get(fam).cloned().or_else(|| running.get(fam).cloned());
                    let Some(v) = v else { return };
                    es.push(Expr::Var(v));
                }
            }
            for (_, nb) in &new_binders {
                pattern.push(Some(nb.clone()));
            }
        }
        for (fam, nb) in &new_binders {
            if let Some(old_v) = running.get(fam).cloned() {
                let repl = Expr::Var(nb.clone());
                for s2 in b.stmts.iter_mut().skip(idx + 1) {
                    substitute_var_in_stmt(s2, &old_v, &repl);
                }
                substitute_var_in_tail(&mut b.tail, &old_v, &repl);
            }
        }
        if let Stmt::Let { pattern, .. } = &b.stmts[idx] {
            for slot in pattern.iter().flatten() {
                running.insert(family(slot), slot.clone());
            }
        }
        idx += 1;
    }
}

// ---------------------------------------------------------------
// The widening itself
// ---------------------------------------------------------------

/// Find the trailing incomplete cluster in `stmts` and widen merges
/// A and B in place. Returns the updated-family map (root, tableMut,
/// U_A sync) for tail/pattern rewiring.
fn widen_cluster_in(
    stmts: &mut Vec<Stmt>,
    pairs: &[(Template, Template)],
    fresh: &mut usize,
    entry: &BTreeMap<String, VarId>,
) -> Option<BTreeMap<String, VarId>> {
    // Versions + locate A and B.
    let mut versions = entry.clone();
    let mut found: Option<(usize, usize, usize)> = None; // (pair_idx, A if_idx, B if_idx)
    let mut i = 0;
    while i < stmts.len() {
        if let Some(m) = parse_merge(stmts, i) {
            let next = m.if_idx + 1;
            for (pi, (head_t, node_t)) in pairs.iter().enumerate() {
                let updates_ua = m
                    .pattern
                    .iter()
                    .flatten()
                    .any(|v| family(v) == head_t.child_family);
                let is_complete =
                    template_from(&m, &[head_t.chain.last().unwrap().0.clone()]).is_some();
                if updates_ua && !is_complete {
                    found = Some((pi, m.if_idx, usize::MAX));
                }
                if family(m.child) == head_t.child_family {
                    found = None;
                }
                if let Some((fpi, a_idx, b_slot)) = &mut found {
                    if *fpi == pi
                        && *b_slot == usize::MAX
                        && m.if_idx > *a_idx
                        && m.pattern
                            .iter()
                            .flatten()
                            .any(|v| family(v) == node_t.bridge_family)
                    {
                        *b_slot = m.if_idx;
                    }
                }
            }
            for slot in m.pattern.iter().flatten() {
                versions.insert(family(slot), slot.clone());
            }
            i = next;
            continue;
        }
        if let Stmt::Let { pattern, .. } = &stmts[i] {
            for slot in pattern.iter().flatten() {
                versions.insert(family(slot), slot.clone());
            }
        }
        i += 1;
    }
    let (pair_idx, a_if, b_if) = found?;
    if b_if == usize::MAX {
        return None;
    }
    // Idempotence: a cluster already widened (by the phi-arm pass
    // when this block is itself a phi arm reached again through the
    // recursion) carries __wbc binders in A's pattern -- skip.
    if let Stmt::Let { pattern, .. } = &stmts[a_if] {
        if pattern
            .iter()
            .flatten()
            .any(|v| v.as_ref().starts_with("__wbc"))
        {
            return None;
        }
    }
    let (head_t, node_t) = &pairs[pair_idx];
    // Role families.
    let ua_fam = &head_t.child_family; // $t5
    let head_bridge_fam = &head_t.bridge_family; // $t17
    let root_fam = &head_t.chain.last().unwrap().0; // $t0
    let root_edge_head = head_t.chain.last().unwrap().1.clone(); // .f1
    let ub_fam = &node_t.bridge_family; // $t11
    let node_fam = &node_t.chain[1].0; // $t10
    let table_fam = &node_t.chain[2].0; // $t9
    let node_edge = node_t.chain[1].1.clone(); // .f1@322
    let table_edge = node_t.chain[2].1.clone(); // MapKey
    let root_edge_inner = node_t.chain[3].1.clone(); // .f7
    if node_t.chain[3].0 != *root_fam {
        return None;
    }
    // Pre-cluster versions of the participants.
    // (versions map now holds END state; participants must not be
    // rebound between A and the end except by our own widening --
    // verify nothing after B rebinds them.)
    let mut after_b = false;
    for (k, s) in stmts.iter().enumerate() {
        if let Some(m) = parse_merge(stmts, k) {
            if m.if_idx == b_if {
                after_b = true;
                continue;
            }
        }
        if !after_b || k <= b_if {
            continue;
        }
        if let Stmt::Let { pattern, .. } = s {
            for slot in pattern.iter().flatten() {
                let f = family(slot);
                if [
                    ua_fam,
                    head_bridge_fam,
                    root_fam,
                    ub_fam,
                    node_fam,
                    table_fam,
                ]
                .iter()
                .any(|x| **x == f)
                {
                    return None;
                }
            }
        }
    }
    let v = |fam: &str| versions.get(fam).cloned();
    let (Some(head_bridge_v), Some(root_v), Some(node_v), Some(table_v)) =
        (v(head_bridge_fam), v(root_fam), v(node_fam), v(table_fam))
    else {
        return None;
    };
    // A's outputs: pattern slot whose family is U_A; B's: family U_B.
    let a_pat = if let Stmt::Let { pattern, .. } = &stmts[a_if] {
        pattern.clone()
    } else {
        return None;
    };
    let ua_after_a = a_pat
        .iter()
        .flatten()
        .find(|p| family(p) == *ua_fam)?
        .clone();
    let b_pat = if let Stmt::Let { pattern, .. } = &stmts[b_if] {
        pattern.clone()
    } else {
        return None;
    };
    let ub_after_b = b_pat
        .iter()
        .flatten()
        .find(|p| family(p) == *ub_fam)?
        .clone();
    // U_B's pre-B version (for A's else route the patch uses the
    // PRE-B node-nexts tracker; we don't actually need it -- the
    // patch writes node.f_nexts directly from U_A').

    // ---- widen merge A ----
    *fresh += 1;
    let root_after_a: VarId = format!("__wbc_r0a_{}", fresh).into();
    {
        let Stmt::Let { pattern, value } = &mut stmts[a_if] else {
            return None;
        };
        let Expr::If {
            then_branch,
            else_branch,
            ..
        } = value
        else {
            return None;
        };
        // then-arm: inner path dispatch.
        // U_A' inside the arm = the write_back output whose family is
        // U_A (the arm's own fresh version).
        let ua_in_arm = then_branch
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Let { pattern, value } => match (pattern.as_slice(), value) {
                    ([Some(o)], Expr::WriteBack { .. }) if family(o) == *ua_fam => Some(o.clone()),
                    _ => None,
                },
                _ => None,
            })
            .last()?;
        *fresh += 1;
        let c: VarId = format!("__wbc_c{}", fresh).into();
        *fresh += 1;
        let hb_out: VarId = format!("__wbc_hb{}", fresh).into();
        *fresh += 1;
        let r_head: VarId = format!("__wbc_rh{}", fresh).into();
        *fresh += 1;
        let n_out: VarId = format!("__wbc_n{}", fresh).into();
        *fresh += 1;
        let t_out: VarId = format!("__wbc_t{}", fresh).into();
        *fresh += 1;
        let r_node: VarId = format!("__wbc_rn{}", fresh).into();
        let dispatch = vec![
            Stmt::Let {
                pattern: vec![Some(c.clone())],
                value: Expr::IsParent {
                    node: BorrowNode::Reference(head_bridge_v.clone()),
                    edge: BorrowEdge::Direct,
                    child: ua_in_arm.clone(),
                },
            },
            Stmt::Let {
                pattern: vec![Some(root_after_a.clone())],
                value: Expr::If {
                    cond: Box::new(Expr::Var(c)),
                    then_branch: Box::new(Block {
                        stmts: vec![
                            Stmt::Let {
                                pattern: vec![Some(hb_out.clone())],
                                value: Expr::WriteBack {
                                    node: BorrowNode::Reference(head_bridge_v.clone()),
                                    edge: BorrowEdge::Direct,
                                    child: ua_in_arm.clone(),
                                    world: None,
                                },
                            },
                            Stmt::Let {
                                pattern: vec![Some(r_head.clone())],
                                value: Expr::WriteBack {
                                    node: BorrowNode::Reference(root_v.clone()),
                                    edge: root_edge_head.clone(),
                                    child: hb_out,
                                    world: None,
                                },
                            },
                        ],
                        tail: BlockTail::Value(Expr::Var(r_head)),
                    }),
                    else_branch: Box::new(Block {
                        stmts: vec![
                            Stmt::Let {
                                pattern: vec![Some(n_out.clone())],
                                value: Expr::WriteBack {
                                    node: BorrowNode::Reference(node_v.clone()),
                                    edge: node_edge.clone(),
                                    child: ua_in_arm.clone(),
                                    world: None,
                                },
                            },
                            Stmt::Let {
                                pattern: vec![Some(t_out.clone())],
                                value: Expr::WriteBack {
                                    node: BorrowNode::Reference(table_v.clone()),
                                    edge: table_edge.clone(),
                                    child: n_out,
                                    world: None,
                                },
                            },
                            Stmt::Let {
                                pattern: vec![Some(r_node.clone())],
                                value: Expr::WriteBack {
                                    node: BorrowNode::Reference(root_v.clone()),
                                    edge: root_edge_inner.clone(),
                                    child: t_out,
                                    world: None,
                                },
                            },
                        ],
                        tail: BlockTail::Value(Expr::Var(r_node)),
                    }),
                },
            },
        ];
        let BlockTail::Value(Expr::Tuple(tes)) = &mut then_branch.tail else {
            return None;
        };
        then_branch.stmts.extend(dispatch);
        tes.push(Expr::Var(root_after_a.clone()));
        let BlockTail::Value(Expr::Tuple(ees)) = &mut else_branch.tail else {
            return None;
        };
        ees.push(Expr::Var(root_v.clone()));
        pattern.push(Some(root_after_a.clone()));
    }

    // ---- widen merge B ----
    // B's if_idx shifted? A is before B and we didn't insert/remove
    // stmts at block level, only inside A's arms -- b_if unchanged.
    *fresh += 1;
    let root_final: VarId = format!("__wbc_r0_{}", fresh).into();
    *fresh += 1;
    let table_final: VarId = format!("__wbc_t9_{}", fresh).into();
    *fresh += 1;
    let ua_final: VarId = format!("__wbc_sync_{}", fresh).into();
    {
        let Stmt::Let { pattern, value } = &mut stmts[b_if] else {
            return None;
        };
        let Expr::If {
            then_branch,
            else_branch,
            ..
        } = value
        else {
            return None;
        };
        let ub_in_arm = then_branch
            .stmts
            .iter()
            .filter_map(|s| match s {
                Stmt::Let { pattern, value } => match (pattern.as_slice(), value) {
                    ([Some(o)], Expr::WriteBack { .. }) if family(o) == *ub_fam => Some(o.clone()),
                    _ => None,
                },
                _ => None,
            })
            .last()?;
        *fresh += 1;
        let n_out: VarId = format!("__wbc_n{}", fresh).into();
        *fresh += 1;
        let t_out: VarId = format!("__wbc_t{}", fresh).into();
        *fresh += 1;
        let r_out: VarId = format!("__wbc_r{}", fresh).into();
        *fresh += 1;
        let sync_out: VarId = format!("__wbc_s{}", fresh).into();
        let ext = vec![
            Stmt::Let {
                pattern: vec![Some(n_out.clone())],
                value: Expr::WriteBack {
                    node: BorrowNode::Reference(node_v.clone()),
                    edge: node_edge.clone(),
                    child: ub_in_arm.clone(),
                    world: None,
                },
            },
            Stmt::Let {
                pattern: vec![Some(t_out.clone())],
                value: Expr::WriteBack {
                    node: BorrowNode::Reference(table_v.clone()),
                    edge: table_edge.clone(),
                    child: n_out,
                    world: None,
                },
            },
            Stmt::Let {
                pattern: vec![Some(r_out.clone())],
                value: Expr::WriteBack {
                    node: BorrowNode::Reference(root_after_a.clone()),
                    edge: root_edge_inner.clone(),
                    child: t_out.clone(),
                    world: None,
                },
            },
            Stmt::Let {
                pattern: vec![Some(sync_out.clone())],
                value: Expr::WriteBack {
                    node: BorrowNode::Reference(ua_after_a.clone()),
                    edge: BorrowEdge::Direct,
                    child: ub_in_arm.clone(),
                    world: None,
                },
            },
        ];
        let BlockTail::Value(Expr::Tuple(tes)) = &mut then_branch.tail else {
            return None;
        };
        then_branch.stmts.extend(ext);
        tes.push(Expr::Var(r_out));
        tes.push(Expr::Var(t_out));
        tes.push(Expr::Var(sync_out));
        let BlockTail::Value(Expr::Tuple(ees)) = &mut else_branch.tail else {
            return None;
        };
        ees.push(Expr::Var(root_after_a.clone()));
        ees.push(Expr::Var(table_v.clone()));
        ees.push(Expr::Var(ua_after_a.clone()));
        pattern.push(Some(root_final.clone()));
        pattern.push(Some(table_final.clone()));
        pattern.push(Some(ua_final.clone()));
    }
    let mut updated = BTreeMap::new();
    updated.insert(root_fam.clone(), root_final);
    updated.insert(table_fam.clone(), table_final);
    updated.insert(ua_fam.clone(), ua_final);
    Some(updated)
}
