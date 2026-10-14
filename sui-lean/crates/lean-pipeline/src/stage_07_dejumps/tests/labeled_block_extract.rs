//! Tests for `stage_07_dejumps::labeled_block_extract::run()`.
//!
//! Covers both labeled-block dispositions:
//!  - inlinable (degenerate, no `ReturnFromBlock`) -> stmts hoisted,
//!    no helper, and the inner bindings stay typeable for following
//!    statements.
//!  - non-inlinable (a nested `ReturnFromBlock` reaches the label) ->
//!    extracted into a `<parent>.labeled_N` helper, with the escaping
//!    result temp bound by the replacement `let` so a following copy
//!    types correctly (the single-pass scope-fold contract).

use crate::ir::{
    Block, BlockTail, Const, Effects, Expr, Function, FunctionKind, Module, Param, Program,
    Signature, Stmt, Type, VarId,
};
use ethnum::U256;

use crate::stage_07_dejumps::labeled_block_extract;

fn lit_u64(n: u64) -> Expr {
    Expr::Const(Const::UInt {
        bits: 64,
        value: U256::from(n),
    })
}

fn vid(s: &str) -> VarId {
    VarId::from(s)
}

/// A single `Source` function `f(x: u64) -> u64` with the given body.
fn one_fn_program(body: Block) -> Program {
    let f = Function {
        module: 0,
        name: "f".to_string(),
        signature: Signature {
            type_params: Vec::new(),
            params: vec![Param {
                name: "x".to_string(),
                var: vid("x"),
                ty: Type::UInt(64),
            }],
            return_type: Type::UInt(64),
        },
        body,
        kind: FunctionKind::Source,
        effects: Effects::CONSERVATIVE,
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

fn labeled_helper(p: &Program) -> Option<(usize, &Function)> {
    p.functions
        .iter()
        .find(|(_, f)| f.name.starts_with("f.labeled_"))
        .map(|(id, f)| (*id, f))
}

#[test]
fn inlinable_block_inner_binding_typeable_for_following_let() {
    // Degenerate (no ReturnFromBlock) labeled block binds `y`, which a
    // FOLLOWING top-level `let c = y` consumes. Inlining hoists `let y`
    // ahead of the copy, so `y` must be in scope when the copy is
    // typed. (Regression guard for the single-pass scope build, which
    // asserts every let value is typeable.)
    let lb_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(vid("y"))],
            value: lit_u64(7),
        }],
        tail: BlockTail::Value(Expr::Unit),
    };
    let f_body = Block {
        stmts: vec![
            Stmt::Eval(Expr::LabeledBlock {
                body: Box::new(lb_body),
                result_ty: Type::Unit,
            }),
            Stmt::Let {
                pattern: vec![Some(vid("c"))],
                value: Expr::Var(vid("y")),
            },
        ],
        tail: BlockTail::Value(Expr::Var(vid("c"))),
    };
    let mut p = one_fn_program(f_body);

    labeled_block_extract::run(&mut p).expect("run");

    // No helper: the block was inlined, not extracted.
    assert!(
        labeled_helper(&p).is_none(),
        "inlinable block must not spawn a helper"
    );
    let stmts = &p.functions[&0].body.stmts;
    // `let y` is hoisted ahead of `let c = y`.
    assert!(
        matches!(&stmts[0], Stmt::Let { pattern, .. } if pattern == &vec![Some(vid("y"))]),
        "expected hoisted `let y`, got {:?}",
        stmts[0]
    );
    assert!(
        matches!(&stmts[1], Stmt::Let { pattern, value }
            if pattern == &vec![Some(vid("c"))] && matches!(value, Expr::Var(v) if *v == vid("y"))),
        "expected `let c = y` preserved, got {:?}",
        stmts[1]
    );
    // No labeled block survives.
    assert!(
        !stmts
            .iter()
            .any(|s| matches!(s, Stmt::Eval(Expr::LabeledBlock { .. }))),
        "no LabeledBlock should remain"
    );
}

#[test]
fn non_inlinable_block_extracts_and_binds_escaping_result() {
    // A nested `ReturnFromBlock` makes the block non-inlinable. Its
    // result temp `r` is set on the natural exit and consumed by a
    // FOLLOWING `let c = r`. Extraction must bind `r` via the helper
    // call so the copy still resolves (the find-index shape that drove
    // the single-pass fix).
    let lb_body = Block {
        stmts: vec![
            // Nested early exit -> non-inlinable.
            Stmt::Eval(Expr::If {
                cond: Box::new(Expr::Const(Const::Bool(true))),
                then_branch: Box::new(Block {
                    stmts: vec![],
                    tail: BlockTail::ReturnFromBlock {
                        level: 0,
                        value: Box::new(Expr::Unit),
                    },
                }),
                else_branch: Box::new(Block {
                    stmts: vec![],
                    tail: BlockTail::Value(Expr::Unit),
                }),
            }),
            // Result temp, set on the fall-through path.
            Stmt::Let {
                pattern: vec![Some(vid("r"))],
                value: lit_u64(0),
            },
        ],
        // Shape (b): RFB(0, Unit) natural tail with a preceding result let.
        tail: BlockTail::ReturnFromBlock {
            level: 0,
            value: Box::new(Expr::Unit),
        },
    };
    let f_body = Block {
        stmts: vec![
            Stmt::Eval(Expr::LabeledBlock {
                body: Box::new(lb_body),
                result_ty: Type::Unit,
            }),
            Stmt::Let {
                pattern: vec![Some(vid("c"))],
                value: Expr::Var(vid("r")),
            },
        ],
        tail: BlockTail::Value(Expr::Var(vid("c"))),
    };
    let mut p = one_fn_program(f_body);

    labeled_block_extract::run(&mut p).expect("run");

    // A `f.labeled_N` helper was created.
    let (helper_id, helper) = labeled_helper(&p).expect("labeled helper created");
    assert!(matches!(helper.kind, FunctionKind::Synthetic));

    let stmts = &p.functions[&0].body.stmts;
    // The labeled block is replaced by `let r = f.labeled_N(..)`.
    match &stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(vid("r"))]);
            match value {
                Expr::Call { fun, .. } => assert_eq!(*fun, helper_id),
                other => panic!("expected helper Call, got {other:?}"),
            }
        }
        other => panic!("expected `let r = helper(..)`, got {other:?}"),
    }
    // The following copy survives and references the now-bound `r`.
    assert!(
        matches!(&stmts[1], Stmt::Let { pattern, value }
            if pattern == &vec![Some(vid("c"))] && matches!(value, Expr::Var(v) if *v == vid("r"))),
        "expected `let c = r` preserved, got {:?}",
        stmts[1]
    );
    assert!(
        !stmts
            .iter()
            .any(|s| matches!(s, Stmt::Eval(Expr::LabeledBlock { .. }))),
        "no LabeledBlock should remain"
    );
}
