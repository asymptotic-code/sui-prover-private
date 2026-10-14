//! Lift stage-1's asymmetric "every arm terminates" IR into a symmetric
//! tail-If/Match. Stage 7 runs it first on regular loop helpers before
//! `return_lift`, then across the whole program before `return_collapse`.
//!
//! See `plans/lean-pipeline/asymmetric-terminating-arms.md` for the
//! full design.
//!
//! ## What stage 1 emits
//!
//! When every arm of an `If` / `VariantSwitch` terminates (e.g.
//! `if c { return X } else { return Y }`), stage 1's structurer
//! collapses the *last* arm to `Seq([])` and hoists that arm's
//! body into the surrounding region. Stage 2 lifts this into:
//!
//! ```text
//! Block {
//!     stmts: [
//!         // ... pre-If stmts (cond computation, etc.)
//!         Stmt::Eval(Expr::If {
//!             then_branch: Block { ..., tail: Value(X) },     // non-collapsed
//!             else_branch: Block { stmts: [], tail: Value(Unit) },  // collapsed
//!         }),
//!         // ... post-If stmts computing the hoisted else-body
//!     ],
//!     tail: Value(Y) | Abort{N},   // final value / terminator
//! }
//! ```
//!
//! Earlier stage-7 rewrites may already have turned a terminating arm into a
//! `Value`; the targeted pre-pass can also see a surviving `Return`. The
//! shape is otherwise unchanged. The crucial point is that the
//! `Stmt::Eval(If)` is **not** necessarily the last stmt -- the
//! hoisted body's computation can sit after it as ordinary stmts,
//! with the outer tail carrying the final value.
//!
//! ## The rewrite
//!
//! Find the first `Stmt::Eval(Expr::If | Expr::Match)` in the block's
//! stmts whose arms exhibit stage 1's asymmetric collapse pattern:
//!
//! - **If**: exactly one arm is `Block { stmts: [], tail: Value(Unit) }`
//!   (the collapsed arm); the other arm has a non-`Value(Unit)` tail.
//! - **Match**: exactly one case is `Block { stmts: [], tail: Value(Unit) }`;
//!   every other case has a non-`Value(Unit)` tail.
//!
//! Additionally the outer block's tail must be non-`Value(Unit)`.
//!
//! Lift the `Eval(If/Match)` into the outer block's tail position.
//! Everything that came *after* the `Eval(If/Match)` (post-If stmts
//! plus the outer tail) forms a new Block that replaces the
//! previously-collapsed arm's body:
//!
//! ```text
//! Block {
//!     stmts: <pre-If stmts>,                  // unchanged
//!     tail: Value(Expr::If {
//!         cond,
//!         then_branch: <unchanged>,
//!         else_branch: Block {                // was Block{stmts:[], tail: Value(Unit)}
//!             stmts: <post-If stmts>,
//!             tail: <outer tail>,
//!         },
//!     }),
//! }
//! ```
//!
//! ## Cases handled (uniform)
//!
//! - **Both arms `return`** (the `abs_diff` case): outer tail
//!   `Value(Y)`; collapsed arm adopts `Value(Y)` (possibly with
//!   post-If stmts computing intermediate values).
//! - **One `return`, one `abort`**: outer tail `Abort{N}`; collapsed
//!   arm adopts `Abort{N}`. The renderer maps Abort-tailed inner
//!   blocks to `sorry`, which unifies polymorphically with the other
//!   arm's type.
//! - **Both arms `abort`**: outer tail `Abort{N1}`; collapsed arm
//!   becomes `Abort{N1}`. Both inner arms render to `sorry`;
//!   `spec_extract`'s `.aborts` derivation folds both into the abort
//!   predicate.
//! - **Asymmetric break inside a loop**: per-While extraction (slice
//!   B) rewrites `Break(X)` to `Value(Call(LoopAfter, X))` *before*
//!   we run, so by then the pattern is uniformly `Value(...)` and
//!   the same rewrite applies.
//! - **Match (variant switch)**: same shape with N-1 non-`Value(Unit)`
//!   cases and one collapsed `Block{stmts:[], tail: Value(Unit)}`
//!   case. The collapsed case adopts the outer tail.
//! - **Nested asymmetric chains** (`if a {ret X} else if b {ret Y}
//!   else {ret Z}`): top-down traversal handles consecutive
//!   `Stmt::Eval(If)`s as siblings, then descends into the moved
//!   arm to handle the next level of the chain.
//!
//! ## Detection precision
//!
//! Requiring the collapsed arm to be **structurally**
//! `Block{stmts: [], tail: Value(Unit)}` (not just `Value(Unit)`-tailed)
//! distinguishes stage 1's asymmetric collapse from legitimate
//! Move shapes like `if c { foo() }; rest` where the else-arm is
//! also `Block{stmts:[], tail: Value(Unit)}` but the then-arm is
//! also `Value(Unit)`-tailed (with side-effects in stmts). In that
//! legitimate case the "other arm" condition fails (its tail is
//! `Value(Unit)`) and the rewrite correctly stays its hand.
//!
//! ## Idempotency
//!
//! Once a Block has been rewritten, its `Stmt::Eval(If/Match)` is
//! gone -- the If/Match lives in the tail position. A second pass
//! finds no asymmetric pattern in stmts and exits.

use crate::ir::expr::{Block, BlockTail, Expr, Stmt};
use crate::ir::function::{FunctionKind, SpecKind};
use crate::ir::visit::{walk_block_mut_default, MutVisitor};
use crate::ir::Program;

use super::Stage7Error;

/// Walk every function body and rewrite the asymmetric collapse
/// pattern wherever it appears, descending into nested blocks.
///
/// Spec(Aborts) bodies are processed too: the source assert pattern
/// `Stmt::Eval(If{cond, then: Value(Unit), else: Abort{code}})`
/// becomes (after `aborts_variant`'s per-tail rewrites)
/// `Stmt::Eval(If{cond, then: Value(Unit), else: Return(Some(code))})`,
/// which `try_rewrite_block` recognises and lifts to function-tail
/// position (surrounding tail `Value(None)`, else-arm delivering the
/// abort code). The Match-with-Return-arm splice patterns the
/// `.aborts` variant carries are NOT stmt-level `Eval(If/Match)`, so
/// they don't trigger this rewrite.
pub fn run(program: &mut Program) -> Result<(), Stage7Error> {
    let mut rewriter = AsymRewriter;
    for f in program.functions.values_mut() {
        rewriter.visit_block_mut(&mut f.body);
    }
    Ok(())
}

pub(super) fn run_regular_loop_helpers(program: &mut Program) {
    let abort_result_ty =
        super::option_aborts::ensure_aborts_types(program).option_abort_code_type();
    let helpers: Vec<_> = program
        .functions
        .iter()
        .filter_map(|(id, function)| {
            if function.signature.return_type == abort_result_ty {
                return None;
            }
            let parent = match function.kind {
                FunctionKind::LoopBody { parent, .. } | FunctionKind::LoopAfter { parent, .. } => {
                    parent
                }
                _ => return None,
            };
            let is_aborts_helper = program.functions.get(&parent).is_some_and(|function| {
                matches!(
                    function.kind,
                    FunctionKind::Spec {
                        kind: SpecKind::Aborts,
                        ..
                    }
                )
            });
            (!is_aborts_helper).then_some(*id)
        })
        .collect();
    let mut rewriter = AsymRewriter;
    for id in helpers {
        rewriter.visit_block_mut(&mut program.functions.get_mut(&id).expect("known helper").body);
    }
}

/// Top-down rewriter: apply the collapse at each block first (looping
/// until no more matches), then descend into children. Descending
/// after the rewrite catches asymmetric patterns inside stmts the
/// rewrite just moved into a freshly-created inner arm.
struct AsymRewriter;

impl MutVisitor for AsymRewriter {
    fn visit_block_mut(&mut self, b: &mut Block) {
        while try_rewrite_block(b) {}
        walk_block_mut_default(self, b);
    }
}

#[derive(Clone, Copy)]
enum AsymKind {
    If,
    Match,
}

#[derive(Clone, Copy)]
enum AsymArm {
    Then,
    Else,
    Case(usize),
}

/// Detect + apply one rewrite to `b`. Returns `true` if a rewrite was
/// applied, `false` if no asymmetric pattern matched.
fn try_rewrite_block(b: &mut Block) -> bool {
    if is_value_unit_tail(&b.tail) {
        return false;
    }

    // Find the first Stmt::Eval(If/Match) whose arms exhibit stage 1's
    // asymmetric collapse pattern.
    let mut found: Option<(usize, AsymKind, AsymArm)> = None;
    for (i, s) in b.stmts.iter().enumerate() {
        match s {
            Stmt::Eval(Expr::If {
                then_branch,
                else_branch,
                ..
            }) => {
                let then_collapsed = is_collapsed_arm(then_branch);
                let else_collapsed = is_collapsed_arm(else_branch);
                let then_non_unit_tail = !is_value_unit_tail(&then_branch.tail);
                let else_non_unit_tail = !is_value_unit_tail(&else_branch.tail);
                // Exactly one arm is the stage-1 "Seq([])" collapse
                // (empty stmts + Value(Unit) tail) AND the other arm
                // has a non-Value(Unit) tail. The stmts-empty check
                // avoids firing on legitimate side-effect arms.
                if then_collapsed && else_non_unit_tail {
                    found = Some((i, AsymKind::If, AsymArm::Then));
                    break;
                }
                if else_collapsed && then_non_unit_tail {
                    found = Some((i, AsymKind::If, AsymArm::Else));
                    break;
                }
            }
            Stmt::Eval(Expr::Match { cases, .. }) => {
                let collapsed_indices: Vec<usize> = cases
                    .iter()
                    .enumerate()
                    .filter_map(|(j, arm)| is_collapsed_arm(&arm.body).then_some(j))
                    .collect();
                if collapsed_indices.len() == 1 {
                    let idx = collapsed_indices[0];
                    let others_non_unit_tail = cases
                        .iter()
                        .enumerate()
                        .all(|(j, arm)| j == idx || !is_value_unit_tail(&arm.body.tail));
                    if others_non_unit_tail {
                        found = Some((i, AsymKind::Match, AsymArm::Case(idx)));
                        break;
                    }
                }
            }
            _ => {}
        }
    }

    let Some((idx, kind, asym_arm)) = found else {
        return false;
    };

    // Drain stmts after the asymmetric site. They (plus the outer
    // tail) form the "rest" block that replaces the collapsed arm.
    let stmts_after: Vec<Stmt> = b.stmts.drain((idx + 1)..).collect();
    let outer_tail = std::mem::replace(&mut b.tail, BlockTail::Value(Expr::Unit));
    let rest_block = Block {
        stmts: stmts_after,
        tail: outer_tail,
    };

    let stmt = b.stmts.remove(idx);

    match kind {
        AsymKind::If => {
            let (cond, mut then_branch, mut else_branch) = match stmt {
                Stmt::Eval(Expr::If {
                    cond,
                    then_branch,
                    else_branch,
                }) => (cond, then_branch, else_branch),
                _ => unreachable!(),
            };
            match asym_arm {
                AsymArm::Then => *then_branch = rest_block,
                AsymArm::Else => *else_branch = rest_block,
                AsymArm::Case(_) => unreachable!(),
            }
            b.tail = BlockTail::Value(Expr::If {
                cond,
                then_branch,
                else_branch,
            });
        }
        AsymKind::Match => {
            let (struct_id, selector, mut cases) = match stmt {
                Stmt::Eval(Expr::Match {
                    struct_id,
                    selector,
                    cases,
                }) => (struct_id, selector, cases),
                _ => unreachable!(),
            };
            let AsymArm::Case(case_idx) = asym_arm else {
                unreachable!()
            };
            *cases[case_idx].body = rest_block;
            b.tail = BlockTail::Value(Expr::Match {
                struct_id,
                selector,
                cases,
            });
        }
    }

    true
}

fn is_value_unit_tail(t: &BlockTail) -> bool {
    matches!(t, BlockTail::Value(Expr::Unit))
}

/// Stage-1's "asymmetric collapsed" arm shape:
/// `Block { stmts: [], tail: Value(Unit) }`. Distinguishing this from
/// the more general `Value(Unit)`-tailed Block avoids firing on
/// legitimate side-effect Unit arms.
fn is_collapsed_arm(b: &Block) -> bool {
    b.stmts.is_empty() && is_value_unit_tail(&b.tail)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::function::{Function, Signature};
    use crate::ir::ty::Type;

    fn var(n: &str) -> Expr {
        Expr::Var(crate::ir::VarId::from(n))
    }

    fn block(stmts: Vec<Stmt>, tail: BlockTail) -> Block {
        Block { stmts, tail }
    }

    fn run_block(b: &mut Block) {
        let mut rewriter = AsymRewriter;
        rewriter.visit_block_mut(b);
    }

    fn function(kind: FunctionKind, return_type: Type, body: Block) -> Function {
        Function {
            module: 0,
            name: "f".into(),
            signature: Signature {
                type_params: Vec::new(),
                params: Vec::new(),
                return_type,
            },
            body,
            kind,
            effects: crate::ir::Effects::CONSERVATIVE,
            explicit_pure: false,
        }
    }

    fn asymmetric_body() -> Block {
        block(
            vec![Stmt::Eval(Expr::If {
                cond: Box::new(var("c")),
                then_branch: Box::new(block(Vec::new(), BlockTail::Value(var("z")))),
                else_branch: Box::new(block(Vec::new(), BlockTail::Value(Expr::Unit))),
            })],
            BlockTail::Value(var("w")),
        )
    }

    /// `Stmt::Eval(if c { z } else { <collapsed> })` followed by a
    /// non-unit outer tail `w` lifts the If into tail position, with
    /// `w` becoming the (previously-collapsed) else arm.
    #[test]
    fn lifts_top_level_asymmetric_if() {
        let if_stmt = Stmt::Eval(Expr::If {
            cond: Box::new(var("c")),
            then_branch: Box::new(block(Vec::new(), BlockTail::Value(var("z")))),
            else_branch: Box::new(block(Vec::new(), BlockTail::Value(Expr::Unit))),
        });
        let mut b = block(vec![if_stmt], BlockTail::Value(var("w")));
        run_block(&mut b);
        match &b.tail {
            BlockTail::Value(Expr::If {
                then_branch,
                else_branch,
                ..
            }) => {
                assert!(b.stmts.is_empty(), "the Eval(If) stmt should be lifted out");
                assert!(matches!(then_branch.tail, BlockTail::Value(Expr::Var(_))));
                assert!(matches!(else_branch.tail, BlockTail::Value(Expr::Var(_))));
            }
            other => panic!("expected lifted tail If, got {other:?}"),
        }
    }

    /// The rewriter descends into nested blocks: an asymmetric pattern
    /// inside an outer If's then-arm is lifted during descent.
    #[test]
    fn lifts_nested_asymmetric_if() {
        let inner = Stmt::Eval(Expr::If {
            cond: Box::new(var("c1")),
            then_branch: Box::new(block(Vec::new(), BlockTail::Value(var("z")))),
            else_branch: Box::new(block(Vec::new(), BlockTail::Value(Expr::Unit))),
        });
        let outer = Expr::If {
            cond: Box::new(var("c0")),
            then_branch: Box::new(block(vec![inner], BlockTail::Value(var("w")))),
            else_branch: Box::new(block(Vec::new(), BlockTail::Value(var("q")))),
        };
        let mut b = block(Vec::new(), BlockTail::Value(outer));
        run_block(&mut b);
        match &b.tail {
            BlockTail::Value(Expr::If { then_branch, .. }) => {
                assert!(
                    then_branch.stmts.is_empty(),
                    "nested asymmetric If should be lifted during descent"
                );
                assert!(matches!(
                    then_branch.tail,
                    BlockTail::Value(Expr::If { .. })
                ));
            }
            other => panic!("unexpected root tail: {other:?}"),
        }
    }

    #[test]
    fn early_loop_pass_excludes_aborts_helpers() {
        let mut program = Program::default();
        let abort_result =
            super::super::option_aborts::ensure_aborts_types(&mut program).option_abort_code_type();
        program.functions.insert(
            0,
            function(
                FunctionKind::Source,
                Type::UInt(64),
                Block::just(Expr::Unit),
            ),
        );
        program.functions.insert(
            1,
            function(
                FunctionKind::LoopBody { parent: 0, slot: 0 },
                abort_result,
                asymmetric_body(),
            ),
        );
        program.functions.insert(
            2,
            function(
                FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    target: 0,
                },
                Type::UInt(64),
                Block::just(Expr::Unit),
            ),
        );
        program.functions.insert(
            3,
            function(
                FunctionKind::LoopBody { parent: 2, slot: 0 },
                Type::UInt(64),
                asymmetric_body(),
            ),
        );
        program.functions.insert(
            4,
            function(
                FunctionKind::LoopBody { parent: 0, slot: 1 },
                Type::UInt(64),
                asymmetric_body(),
            ),
        );

        run_regular_loop_helpers(&mut program);

        assert_eq!(program.functions[&1].body.stmts.len(), 1);
        assert_eq!(program.functions[&3].body.stmts.len(), 1);
        assert!(program.functions[&4].body.stmts.is_empty());
    }

    #[test]
    fn early_loop_pass_does_not_embed_a_function_tail_return() {
        let mut program = Program::default();
        program.functions.insert(
            0,
            function(
                FunctionKind::Source,
                Type::UInt(64),
                Block::just(Expr::Unit),
            ),
        );
        let mut body = asymmetric_body();
        body.tail = BlockTail::Return(Box::new(var("loop_result")));
        program.functions.insert(
            1,
            function(
                FunctionKind::LoopBody { parent: 0, slot: 0 },
                Type::UInt(64),
                body,
            ),
        );

        super::super::return_collapse::run(&mut program).unwrap();
        run_regular_loop_helpers(&mut program);

        let BlockTail::Value(Expr::If { else_branch, .. }) = &program.functions[&1].body.tail
        else {
            panic!("expected reconstructed tail If")
        };
        assert!(matches!(else_branch.tail, BlockTail::Value(Expr::Var(_))));
    }
}
