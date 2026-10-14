use crate::ir::{BorrowEdge, BorrowNode, Expr, Type};
use crate::stage_03_mut_to_let::{run, Stage3Error};

use super::fixtures::{one_fn_program, param};

#[test]
fn stage3_rejects_residual_borrow_global() {
    let mut program = one_fn_program(vec![], Expr::BorrowGlobal(7), vec![], Type::Unit);
    assert_eq!(
        run(&mut program),
        Err(Stage3Error::ResidualGlobal {
            function: 0,
            global: 7,
        })
    );
}

#[test]
fn stage3_rejects_residual_global_root_before_rewriting() {
    let expr = Expr::WriteBack {
        node: BorrowNode::GlobalRoot(3),
        edge: BorrowEdge::Direct,
        child: "child".into(),
        world: None,
    };
    let mut program = one_fn_program(
        vec![],
        expr.clone(),
        vec![param("child", Type::UInt(8))],
        Type::UInt(8),
    );
    assert_eq!(
        run(&mut program),
        Err(Stage3Error::ResidualGlobal {
            function: 0,
            global: 3,
        })
    );
    assert_eq!(
        program.functions[&0].body.tail,
        crate::ir::BlockTail::Value(expr)
    );
}
