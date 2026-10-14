//! Phase 2 slice 1 -- function-tail return collapse.
//!
//! Function-tail return collapse, extended to also process
//! `Spec(Aborts)` companion bodies (which phase 1
//! produces with `BlockTail::Return(_)` at the function tail).
//!
//! See `plans/lean-pipeline/stage-07-rewrite.md` "Phase 2 — Unified
//! control-flow extraction" step 3c.
//!
//! ## Rule
//!
//! - **Function-tail** `BlockTail::Return(v) → BlockTail::Value(v)`
//!   (and the same for `ReturnFromBlock { value: v, .. }`).
//! - A `Return(v)` in an `If`/`Match` arm reached recursively through the
//!   function-tail value expression also becomes `Value(v)`. Producing `v`
//!   from that final expression and then returning it is equivalent to the
//!   early return.
//! - Returns in statement and let-value expressions remain for
//!   `return_lift` to handle. Collapsing them would incorrectly execute the
//!   enclosing block's continuation.
//!
//! Idempotent: a second run on already-collapsed IR is a no-op.

use crate::ir::expr::{BlockTail, Expr};
use crate::ir::function::{FunctionKind, SpecKind};
use crate::ir::Program;

use super::Stage7Error;

/// Collapse the function-tail `BlockTail::Return(v)` /
/// `BlockTail::ReturnFromBlock { value: v, .. }` to
/// `BlockTail::Value(v)` in every non-helper, non-predicate body.
///
/// Applies to: `FunctionKind::Source`, `FunctionKind::Test`, loop helpers,
/// `FunctionKind::Spec { Aborts, .. }`, and `FunctionKind::Synthetic`
/// (return_lift's `cont_N` continuations + labeled-block helpers, whose
/// post-Return bodies can themselves end in a function-tail Return).
/// Spec(Requires) / Spec(Ensures) are pure predicates with no Returns. The
/// stage-07 postcondition flags a lingering
/// function-tail Return in ANY of these kinds, so they must all be
/// collapsed here.
pub fn run(program: &mut Program) -> Result<(), Stage7Error> {
    for f in program.functions.values_mut() {
        let process = matches!(
            f.kind,
            FunctionKind::Source
                | FunctionKind::Test { .. }
                | FunctionKind::Synthetic
                | FunctionKind::LoopBody { .. }
                | FunctionKind::LoopAfter { .. }
                | FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    ..
                }
        );
        if process {
            collapse_function_tail(&mut f.body.tail);
        } else {
            collapse_returns_in_tail_value(&mut f.body.tail);
        }
    }
    Ok(())
}

/// Convert a function-tail `Return` / `ReturnFromBlock` to `Value`,
/// moving the payload across unchanged. Any other tail is left as-is.
fn collapse_function_tail(tail: &mut BlockTail) {
    match tail {
        BlockTail::Return(value) | BlockTail::ReturnFromBlock { value, .. } => {
            let payload = std::mem::replace(value, Box::new(Expr::Unit));
            *tail = BlockTail::Value(*payload);
        }
        _ => {}
    }
    collapse_returns_in_tail_value(tail);
}

fn collapse_returns_in_tail_value(tail: &mut BlockTail) {
    let BlockTail::Value(expr) = tail else {
        return;
    };
    collapse_returns_in_tail_expr(expr);
}

fn collapse_returns_in_tail_expr(expr: &mut Expr) {
    match expr {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            collapse_return_in_tail_block(then_branch);
            collapse_return_in_tail_block(else_branch);
        }
        Expr::Match { cases, .. } => {
            for arm in cases {
                collapse_return_in_tail_block(&mut arm.body);
            }
        }
        _ => {}
    }
}

fn collapse_return_in_tail_block(block: &mut crate::ir::expr::Block) {
    if let BlockTail::Return(value) = &mut block.tail {
        let payload = std::mem::replace(value, Box::new(Expr::Unit));
        block.tail = BlockTail::Value(*payload);
    }
    collapse_returns_in_tail_value(&mut block.tail);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Block, Function, Module, Param, Signature, Type, VarId};

    fn source_with_tail(tail: BlockTail) -> Program {
        program_with_tail(tail, FunctionKind::Source)
    }

    fn program_with_tail(tail: BlockTail, kind: FunctionKind) -> Program {
        let f = Function {
            module: 0,
            name: "f".to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: vec![Param {
                    name: "x".to_string(),
                    var: VarId::from("x"),
                    ty: Type::UInt(64),
                }],
                return_type: Type::UInt(64),
            },
            body: Block {
                stmts: Vec::new(),
                tail,
            },
            kind,
            effects: crate::ir::Effects::CONSERVATIVE,
            explicit_pure: false,
        };
        let mut p = Program::default();
        p.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        p.functions.insert(0, f);
        p
    }

    fn tail_of(p: &Program) -> &BlockTail {
        &p.functions.values().next().unwrap().body.tail
    }

    #[test]
    fn root_tail_return_collapses_to_value() {
        let mut p = source_with_tail(BlockTail::Return(Box::new(Expr::Var(VarId::from("r")))));
        run(&mut p).unwrap();
        assert!(
            matches!(tail_of(&p), BlockTail::Value(Expr::Var(_))),
            "root-tail Return must collapse to Value, preserving the payload"
        );
    }

    #[test]
    fn root_tail_return_from_block_collapses_to_value() {
        let mut p = source_with_tail(BlockTail::ReturnFromBlock {
            level: 0,
            value: Box::new(Expr::Var(VarId::from("r"))),
        });
        run(&mut p).unwrap();
        assert!(matches!(tail_of(&p), BlockTail::Value(Expr::Var(_))));
    }

    #[test]
    fn loop_helper_tail_return_collapses_before_asymmetric_reconstruction() {
        let mut p = program_with_tail(
            BlockTail::Return(Box::new(Expr::Var(VarId::from("r")))),
            FunctionKind::LoopBody {
                parent: 99,
                slot: 0,
            },
        );

        run(&mut p).unwrap();

        assert!(matches!(tail_of(&p), BlockTail::Value(Expr::Var(_))));
    }

    #[test]
    fn return_in_function_tail_if_arm_collapses() {
        // body.tail = Value(If { then: { tail: Return(a) }, else: { tail: Value(b) } }).
        // Each arm delivers the function's final value, so returning `a` from
        // the then-arm is equivalent to making that arm's value `a`.
        let if_expr = Expr::If {
            cond: Box::new(Expr::Var(VarId::from("c"))),
            then_branch: Box::new(Block {
                stmts: Vec::new(),
                tail: BlockTail::Return(Box::new(Expr::Var(VarId::from("a")))),
            }),
            else_branch: Box::new(Block {
                stmts: Vec::new(),
                tail: BlockTail::Value(Expr::Var(VarId::from("b"))),
            }),
        };
        let mut p = source_with_tail(BlockTail::Value(if_expr));
        run(&mut p).unwrap();
        match tail_of(&p) {
            BlockTail::Value(Expr::If { then_branch, .. }) => {
                assert!(
                    matches!(then_branch.tail, BlockTail::Value(Expr::Var(_))),
                    "tail-position arm Return must collapse to Value"
                );
            }
            other => panic!("root tail changed unexpectedly: {other:?}"),
        }
    }

    #[test]
    fn return_in_function_tail_match_arm_collapses_recursively() {
        let nested_if = Expr::If {
            cond: Box::new(Expr::Var(VarId::from("c"))),
            then_branch: Box::new(Block {
                stmts: Vec::new(),
                tail: BlockTail::Return(Box::new(Expr::Var(VarId::from("a")))),
            }),
            else_branch: Box::new(Block::just(Expr::Var(VarId::from("b")))),
        };
        let match_expr = Expr::Match {
            struct_id: 0,
            selector: Box::new(Expr::Var(VarId::from("x"))),
            cases: vec![crate::ir::MatchArm {
                variant: 0,
                bindings: Vec::new(),
                body: Box::new(Block::just(nested_if)),
            }],
        };
        let mut p = source_with_tail(BlockTail::Value(match_expr));

        run(&mut p).unwrap();

        let BlockTail::Value(Expr::Match { cases, .. }) = tail_of(&p) else {
            panic!("expected function-tail Match")
        };
        let BlockTail::Value(Expr::If { then_branch, .. }) = &cases[0].body.tail else {
            panic!("expected nested function-tail If")
        };
        assert!(matches!(then_branch.tail, BlockTail::Value(Expr::Var(_))));
    }

    #[test]
    fn return_in_statement_expression_is_left_untouched() {
        let if_expr = Expr::If {
            cond: Box::new(Expr::Var(VarId::from("c"))),
            then_branch: Box::new(Block {
                stmts: Vec::new(),
                tail: BlockTail::Return(Box::new(Expr::Var(VarId::from("a")))),
            }),
            else_branch: Box::new(Block::just(Expr::Unit)),
        };
        let mut p = source_with_tail(BlockTail::Value(Expr::Var(VarId::from("b"))));
        p.functions.get_mut(&0).unwrap().body.stmts = vec![crate::ir::Stmt::Eval(if_expr)];

        run(&mut p).unwrap();

        let crate::ir::Stmt::Eval(Expr::If { then_branch, .. }) = &p.functions[&0].body.stmts[0]
        else {
            panic!("expected statement-position If")
        };
        assert!(matches!(then_branch.tail, BlockTail::Return(_)));
    }
}
