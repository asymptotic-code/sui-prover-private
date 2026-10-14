//! Path-update construction for stage 3's WriteRef / WriteBack rebinds.
//!
//! `path_to_update` is the value-form mirror of an upstream
//! `WriteBack`'s edge-chain projection: given a base value, a chain
//! of `BorrowEdge`s, and an inner replacement value, it produces an
//! expression that returns the base with the inner-most projection
//! replaced.
//!
//! Phase 1 scope: pure-function helper. Handles `Direct`, `Field`,
//! leaf `EnumField`, and `Hyper`. Nested enum projection and container
//! edges are explicit activation blockers because this retained prototype
//! has no pure tagged-value projection or runtime key/index source.
//!
//! See `plans/lean-pipeline/stage-03-demut.md` for the algorithm and
//! `plans/lean-pipeline/stage-03-demut-impl.md` for the phase plan.

use crate::ir::{Block, BlockTail, BorrowEdge, BorrowNode, Expr, MatchArm, Program, Stmt, VarId};

use super::borrow_state::{build as build_borrow_state, BorrowState};

/// Build a value-form update expression: project `inner` into `base`
/// along `edges`, returning a new `Expr` of the same type as `base`.
///
/// Pure recursion. `Hyper(sub)` flattens at the head of the chain and
/// `Direct` is the identity step. Struct fields recurse through ordinary
/// value projection. A leaf enum field preserves its declared tag in a
/// `PathStep::VariantField`; nested enum projection fails closed.
pub fn path_to_update(base: Expr, edges: &[BorrowEdge], inner: Expr) -> Expr {
    if edges.is_empty() {
        return inner;
    }
    match &edges[0] {
        BorrowEdge::Direct => path_to_update(base, &edges[1..], inner),
        BorrowEdge::StructField {
            struct_id,
            field_index,
        } => {
            let field_base = Expr::Field {
                struct_id: *struct_id,
                field_index: *field_index,
                base: Box::new(base.clone()),
            };
            let inner_update = path_to_update(field_base, &edges[1..], inner);
            Expr::Update {
                step: crate::ir::path::PathStep::Field {
                    struct_id: *struct_id,
                    field_index: *field_index,
                },
                base: Box::new(base),
                value: Box::new(inner_update),
            }
        }
        BorrowEdge::EnumField {
            struct_id,
            variant,
            field_index,
        } => {
            if edges.len() != 1 {
                unimplemented!(
                    "path_to_update: nested BorrowEdge::EnumField requires a tagged value projection"
                );
            }
            Expr::Update {
                step: crate::ir::path::PathStep::VariantField {
                    struct_id: *struct_id,
                    variant: *variant,
                    field_index: *field_index,
                },
                base: Box::new(base),
                value: Box::new(inner),
            }
        }
        BorrowEdge::VecIndex => {
            // Vector-index updates need a runtime index expression
            // (`Expr::UpdateVec { index, .. }`) that this pure
            // helper has no source for. Phase 4 either threads an
            // index source through `path_to_update` or synthesises
            // the `UpdateVec` directly at the WriteBack rewrite
            // site. Until then, panic so callers can't silently
            // produce malformed IR.
            unimplemented!("path_to_update: BorrowEdge::VecIndex deferred to Phase 4")
        }
        BorrowEdge::MapKey { .. } => {
            // Map-key updates need a runtime key expression and the
            // container kind to dispatch to the right
            // `TypedMap.set` / native setter. The deferred stage-3
            // demut pass does not handle these; the active
            // (Boogie-style) path routes them through the
            // `Mutation` prelude at the renderer instead.
            unimplemented!(
                "path_to_update: BorrowEdge::MapKey deferred -- active path uses Mutation prelude"
            )
        }
        BorrowEdge::Hyper(sub) => {
            // Flatten: prepend the Hyper's inner edges to the rest
            // of the chain and recurse. Equivalent to inlining
            // Hyper at the head.
            let mut flat: Vec<BorrowEdge> = sub.clone();
            flat.extend_from_slice(&edges[1..]);
            path_to_update(base, &flat, inner)
        }
    }
}

// ---------------------------------------------------------------------------
// WriteRef / WriteBack rewriters
// ---------------------------------------------------------------------------

/// Rewrite every `Expr::WriteRef` / `Expr::WriteBack` op in every
/// non-native function body in `program` to a value-form
/// `Stmt::Let { pattern: [root], value: path_to_update(...) }`.
///
/// `WriteRef`'s chain is recovered from the per-function borrow-state
/// map (see `borrow_state.rs`); `WriteBack`'s chain is the single
/// `edge` it carries plus the immediate parent `node` -- the parent
/// temp / local is rebound directly from the incoming `child`'s value
/// (via `Expr::ReadRef(Var(child))`, which stage 4 lowers to a
/// projection).
///
/// Vector-index updates (any chain that lowers through
/// `BorrowEdge::VecIndex` / `BorrowEdge::MapKey`) panic via [`path_to_update`] -- they need a
/// runtime-index source the pure helper has no access to. Phase 4
/// fixtures avoid these chains; production support lands in a
/// follow-up.
pub fn rewrite_writebacks(program: &mut Program) {
    let funcs: Vec<crate::ir::FunId> = program.functions.keys().copied().collect();
    for fid in funcs {
        let state = build_borrow_state(&program.functions[&fid]);
        let func = program.functions.get_mut(&fid).unwrap();
        rewrite_block(&mut func.body, &state);
    }
}

fn rewrite_block(block: &mut Block, state: &BorrowState) {
    let stmts = std::mem::take(&mut block.stmts);
    block.stmts = stmts.into_iter().map(|s| rewrite_stmt(s, state)).collect();
    rewrite_tail(&mut block.tail, state);
}

fn rewrite_stmt(stmt: Stmt, state: &BorrowState) -> Stmt {
    match stmt {
        Stmt::Eval(Expr::WriteRef { reference, value }) => {
            rewrite_write_ref(*reference, *value, state)
        }
        Stmt::Eval(Expr::WriteBack {
            node, edge, child, ..
        }) => rewrite_write_back(node, edge, child),
        Stmt::Eval(other) => Stmt::Eval(rewrite_subblocks(other, state)),
        Stmt::Let { pattern, value } => Stmt::Let {
            pattern,
            value: rewrite_subblocks(value, state),
        },
    }
}

fn rewrite_tail(tail: &mut BlockTail, state: &BorrowState) {
    match tail {
        BlockTail::Value(e) => *e = rewrite_subblocks(std::mem::replace(e, Expr::Unit), state),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => {
            **value = rewrite_subblocks(std::mem::replace(&mut **value, Expr::Unit), state);
        }
        BlockTail::Abort { code } => {
            **code = rewrite_subblocks(std::mem::replace(&mut **code, Expr::Unit), state);
        }
    }
}

fn rewrite_subblocks(expr: Expr, state: &BorrowState) -> Expr {
    match expr {
        Expr::If {
            cond,
            mut then_branch,
            mut else_branch,
        } => {
            rewrite_block(&mut then_branch, state);
            rewrite_block(&mut else_branch, state);
            Expr::If {
                cond,
                then_branch,
                else_branch,
            }
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
            ..
        } => Expr::Match {
            struct_id,
            selector,
            cases: cases
                .into_iter()
                .map(|arm| {
                    let MatchArm {
                        variant,
                        bindings,
                        mut body,
                    } = arm;
                    rewrite_block(&mut body, state);
                    MatchArm {
                        variant,
                        bindings,
                        body,
                    }
                })
                .collect(),
        },
        Expr::While {
            mut header,
            cond,
            mut body,
            ..
        } => {
            rewrite_block(&mut header, state);
            rewrite_block(&mut body, state);
            Expr::While {
                header,
                cond,
                body,
                iter_locals: Vec::new(),
                header_exit_locals: Vec::new(),
                live_out: Vec::new(),
            }
        }
        Expr::Quantifier {
            kind,
            binder,
            binder_type,
            domain,
            mut body,
        } => {
            rewrite_block(&mut body, state);
            Expr::Quantifier {
                kind,
                binder,
                binder_type,
                domain,
                body,
            }
        }
        other => other,
    }
}

fn rewrite_write_ref(reference: Expr, value: Expr, state: &BorrowState) -> Stmt {
    let r_var = match &reference {
        Expr::Var(v) => v.clone(),
        other => panic!(
            "stage 3 WriteRef rebinder: reference must be Expr::Var, got {:?}",
            other
        ),
    };
    let chain = state.get(&r_var).unwrap_or_else(|| {
        panic!(
            "stage 3 WriteRef rebinder: no borrow-state entry for ref {:?} -- did stage 2 emit a non-BorrowLoc/BorrowField source?",
            r_var
        )
    });
    let new_value = path_to_update(Expr::Var(chain.root.clone()), &chain.edges, value);
    Stmt::Let {
        pattern: vec![Some(chain.root.clone())],
        value: new_value,
    }
}

fn rewrite_write_back(node: BorrowNode, edge: BorrowEdge, child: VarId) -> Stmt {
    // The surviving ReadRef(Var(child)) is stage 4's concern.
    let inner = Expr::ReadRef(Box::new(Expr::Var(child)));
    let parent_var = match node {
        BorrowNode::LocalRoot(v) => v,
        BorrowNode::Reference(v) => v,
        BorrowNode::GlobalRoot(global) => panic!(
            "stage 3 WriteBack rebinder: GlobalRoot({global}) must be lowered by thread_globals"
        ),
        BorrowNode::SpecGlobalRoot { .. } => panic!(
            "stage 3 WriteBack rebinder: SpecGlobalRoot is out of stage-3 scope -- ghost-state writebacks are renderer-side"
        ),
    };
    let edges = vec![edge];
    let new_value = path_to_update(Expr::Var(parent_var.clone()), &edges, inner);
    Stmt::Let {
        pattern: vec![Some(parent_var)],
        value: new_value,
    }
}
