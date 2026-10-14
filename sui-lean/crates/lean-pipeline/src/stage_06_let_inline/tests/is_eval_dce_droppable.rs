//! Tests for `effects_predicate::is_eval_dce_droppable`.
//!
//! This predicate exists alongside `is_pure_total` (commit 66444c41).
//! Its purpose is narrow: `eval_dce_once` uses it to decide whether
//! a `Stmt::Eval(<expr>)` can be deleted from a block. It is *broader*
//! than `is_pure_total` -- it sees through `Call`s to pure-total
//! **native** functions, whereas `is_pure_total` does NOT (the
//! stricter predicate is what `single_use_inline` uses, and inlining
//! a pure-total native call across a tuple boundary would mis-render
//! the resulting expression -- see the commit message on 66444c41
//! for the navi-lending:oracle regression history).
//!
//! Every test here pins one of:
//!   1. Atoms / pure shapes: both predicates agree.
//!   2. Pure-total NATIVE callee: droppable is `true`, `is_pure_total`
//!      is `false`. This is the load-bearing difference.
//!   3. Pure-total TRANSLATED callee: both predicates agree (`true`).
//!   4. Partial / impure callees: both are `false`.
//!   5. Recursion through composite shapes (Tuple, Pack, If, Match,
//!      ReadRef) preserves the differentiation.

use super::fixtures::*;
use crate::ir::{
    AbortBit, Block, BlockTail, DetBit, Effects, Expr, FunId, MatchArm, MutLevel, NativeDecl,
    Signature, Stmt, Type, VarId,
};
use crate::stage_06_let_inline::effects_predicate::{is_eval_dce_droppable, is_pure_total};

fn pure_total_native(name: &str, return_type: Type) -> NativeDecl {
    NativeDecl {
        module: 0,
        name: name.to_string(),
        signature: Signature {
            type_params: Vec::new(),
            params: Vec::new(),
            return_type,
        },
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
        is_framework: true,
        spec_target: None,
        user_native: None,
    }
}

fn partial_native(name: &str, return_type: Type) -> NativeDecl {
    NativeDecl {
        effects: crate::ir::Effects {
            aborts: crate::ir::AbortBit::Partial,
            det: crate::ir::DetBit::Det,
            mutation: crate::ir::MutLevel::NoMut,
            world_writes: false,
        },
        ..pure_total_native(name, return_type)
    }
}

fn impure_native(name: &str, return_type: Type) -> NativeDecl {
    NativeDecl {
        effects: crate::ir::Effects::CONSERVATIVE,
        ..pure_total_native(name, return_type)
    }
}

fn register_native(p: &mut crate::ir::Program, id: FunId, d: NativeDecl) {
    p.natives.decls.insert(id, d);
}

#[test]
fn atoms_are_droppable() {
    let p = empty_program();
    assert!(is_eval_dce_droppable(&var("x"), &p));
    assert!(is_eval_dce_droppable(&u64_const(7), &p));
    assert!(is_eval_dce_droppable(&Expr::Unit, &p));
    assert!(is_eval_dce_droppable(&bool_const(true), &p));
}

#[test]
fn arithmetic_aborts_so_not_droppable() {
    // BinOp::Add on UInt can overflow; dropping the Eval would
    // hide a potential abort. Same as is_pure_total.
    let p = empty_program();
    let e = add(u64_const(1), u64_const(2));
    assert!(!is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn call_to_pure_total_native_is_droppable_but_not_pure_total() {
    // The load-bearing difference. `is_pure_total` does NOT consult
    // program.natives.decls, so a pure-total native call is
    // (conservatively) classified as NOT pure-total. `is_eval_dce_droppable`
    // DOES consult natives, so the same call IS droppable.
    let mut p = empty_program();
    register_native(&mut p, 7, pure_total_native("pure_native", Type::UInt(64)));

    let e = call(7, vec![]);
    assert!(
        is_eval_dce_droppable(&e, &p),
        "pure-total native call should be droppable"
    );
    assert!(
        !is_pure_total(&e, &p),
        "is_pure_total intentionally does NOT see through natives"
    );
}

#[test]
fn call_to_partial_native_is_not_droppable() {
    // Aborting natives carry the abort effect; not droppable.
    let mut p = empty_program();
    register_native(&mut p, 7, partial_native("partial_native", Type::UInt(64)));

    let e = call(7, vec![]);
    assert!(!is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn call_to_impure_native_is_not_droppable() {
    // Impure natives have observable side-effects beyond their args
    // (event::emit, transfer::*, random::*). Not droppable.
    let mut p = empty_program();
    register_native(&mut p, 7, impure_native("impure_native", Type::Unit));

    let e = call(7, vec![]);
    assert!(!is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn call_to_pure_total_translated_callee_is_droppable_and_pure_total() {
    // For *translated* callees both predicates agree. Test the
    // overlap region.
    let callee = stub_callee("pure", Effects::PURE, Type::UInt(64));
    let p = program_with(vec![(7, callee)]);

    let e = call(7, vec![]);
    assert!(is_eval_dce_droppable(&e, &p));
    assert!(is_pure_total(&e, &p));
}

#[test]
fn call_to_pure_partial_translated_callee_is_not_droppable() {
    let callee = stub_callee(
        "partial",
        Effects {
            aborts: AbortBit::Partial,
            det: DetBit::Det,
            mutation: MutLevel::NoMut,
            world_writes: false,
        },
        Type::UInt(64),
    );
    let p = program_with(vec![(7, callee)]);

    let e = call(7, vec![]);
    assert!(!is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn call_to_missing_callee_is_not_droppable() {
    // No entry in either translated or native maps -> conservatively
    // reject (matches the `_ => return false` arm).
    let p = empty_program();
    let e = call(99, vec![]);
    assert!(!is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn call_with_partial_arg_is_not_droppable_even_if_callee_pure() {
    // The recursion into args must reject when an arg can abort.
    // `is_eval_dce_droppable` recurses with itself, so the arithmetic
    // arg poisons the whole call.
    let mut p = empty_program();
    register_native(&mut p, 7, pure_total_native("pure_native", Type::UInt(64)));

    let e = call(7, vec![add(u64_const(1), u64_const(2))]);
    assert!(!is_eval_dce_droppable(&e, &p));
}

#[test]
fn tuple_recurses_through_native_call() {
    // A Tuple whose element is a pure-total native call should be
    // droppable -- the Tuple recurses with `is_eval_dce_droppable`
    // on each element.
    let mut p = empty_program();
    register_native(&mut p, 7, pure_total_native("pure_native", Type::UInt(64)));

    let e = Expr::Tuple(vec![var("a"), call(7, vec![])]);
    assert!(is_eval_dce_droppable(&e, &p));
    // `is_pure_total` recurses the same way but rejects the inner
    // native call, so the whole Tuple is not pure-total.
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn pack_recurses_through_native_call() {
    // Same as tuple but through `Expr::Pack`.
    let mut p = empty_program();
    register_native(&mut p, 7, pure_total_native("pure_native", Type::UInt(64)));

    let e = Expr::Pack {
        struct_id: 0,
        type_args: Vec::new(),
        variant: None,
        fields: vec![call(7, vec![])],
    };
    assert!(is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn if_both_arms_droppable_through_native_call() {
    // Both arms have value tails calling pure-total natives; the
    // recursion into both arms must classify the whole `if` as
    // droppable.
    let mut p = empty_program();
    register_native(&mut p, 7, pure_total_native("pure_native", Type::UInt(64)));

    let then_b = block_value(vec![], call(7, vec![]));
    let else_b = block_value(vec![], call(7, vec![]));
    let e = Expr::If {
        cond: Box::new(bool_const(true)),
        then_branch: Box::new(then_b),
        else_branch: Box::new(else_b),
    };
    assert!(is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn if_with_non_value_tail_is_not_droppable() {
    // Block tails other than `Value` (Break / Continue / Return /
    // Abort) cannot be safely dropped -- the block's tail effect is
    // observable.
    let p = empty_program();
    let then_b = block_value(vec![], u64_const(0));
    let else_b = block_abort(vec![], u64_const(42));
    let e = Expr::If {
        cond: Box::new(bool_const(true)),
        then_branch: Box::new(then_b),
        else_branch: Box::new(else_b),
    };
    assert!(!is_eval_dce_droppable(&e, &p));
}

#[test]
fn if_with_break_tail_arm_is_not_droppable() {
    // `Break` is a control-flow exit. Dropping a Stmt::Eval whose
    // expression's arm can break would lose the jump effect.
    let p = empty_program();
    let then_b = block_break(vec![], 0, Expr::Unit);
    let else_b = block_value(vec![], u64_const(0));
    let e = Expr::If {
        cond: Box::new(bool_const(true)),
        then_branch: Box::new(then_b),
        else_branch: Box::new(else_b),
    };
    assert!(!is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn if_with_continue_tail_arm_is_not_droppable() {
    // `Continue` is a control-flow exit. Dropping a Stmt::Eval whose
    // expression's arm can continue would lose the jump effect.
    let p = empty_program();
    let then_b = block_value(vec![], u64_const(0));
    let else_b = block_continue(vec![], 0, Expr::Unit);
    let e = Expr::If {
        cond: Box::new(bool_const(true)),
        then_branch: Box::new(then_b),
        else_branch: Box::new(else_b),
    };
    assert!(!is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn if_with_return_tail_arm_is_not_droppable() {
    // `Return` is a control-flow exit. Dropping a Stmt::Eval whose
    // expression's arm can return would lose the jump effect.
    let p = empty_program();
    let then_b = block_return(vec![], u64_const(0));
    let else_b = block_value(vec![], u64_const(0));
    let e = Expr::If {
        cond: Box::new(bool_const(true)),
        then_branch: Box::new(then_b),
        else_branch: Box::new(else_b),
    };
    assert!(!is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn if_with_both_arms_breaking_is_not_droppable() {
    // Even when BOTH arms terminate (the canonicalize_terminators
    // shape -- a terminating-arm If is itself the surrounding
    // block's terminator), the Stmt::Eval form must not be
    // dropped. `canonicalize_terminators` hoists this into Value
    // tail position; but if for some reason it survives in
    // Stmt::Eval position, eval_dce must not silently delete it.
    let p = empty_program();
    let then_b = block_break(vec![], 0, Expr::Unit);
    let else_b = block_continue(vec![], 0, Expr::Unit);
    let e = Expr::If {
        cond: Box::new(bool_const(true)),
        then_branch: Box::new(then_b),
        else_branch: Box::new(else_b),
    };
    assert!(!is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn if_with_nested_stmt_eval_break_bubbles_up_is_not_droppable() {
    // The outer If's arms both have `Value(Unit)` tails -- looks
    // pure on the surface -- BUT one arm contains a nested
    // `Stmt::Eval(If{ then: Break, else: ... })` whose inner If has
    // a Break-tailed arm. is_pure_total_block_with walks every
    // stmt's expression, so the inner Break must propagate
    // non-purity up to the outer If.
    let p = empty_program();
    let inner_if = Expr::If {
        cond: Box::new(bool_const(false)),
        then_branch: Box::new(block_break(vec![], 0, Expr::Unit)),
        else_branch: Box::new(block_value(vec![], Expr::Unit)),
    };
    let outer_then = Block {
        stmts: vec![Stmt::Eval(inner_if)],
        tail: BlockTail::Value(Expr::Unit),
    };
    let outer_else = block_value(vec![], Expr::Unit);
    let e = Expr::If {
        cond: Box::new(bool_const(true)),
        then_branch: Box::new(outer_then),
        else_branch: Box::new(outer_else),
    };
    assert!(
        !is_eval_dce_droppable(&e, &p),
        "outer If must be non-droppable because a deeply-nested arm contains a Break"
    );
}

#[test]
fn match_with_break_in_one_case_is_not_droppable() {
    let p = empty_program();
    let cases = vec![
        MatchArm {
            variant: 0,
            bindings: vec![],
            body: Box::new(block_break(vec![], 0, Expr::Unit)),
        },
        MatchArm {
            variant: 1,
            bindings: vec![],
            body: Box::new(block_value(vec![], u64_const(0))),
        },
    ];
    let e = Expr::Match {
        struct_id: 0,
        selector: Box::new(var("v")),
        cases,
    };
    assert!(!is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn match_all_arms_droppable_through_native_call() {
    let mut p = empty_program();
    register_native(&mut p, 7, pure_total_native("pure_native", Type::UInt(64)));

    let e = Expr::Match {
        struct_id: 0,
        selector: Box::new(var("v")),
        cases: vec![
            MatchArm {
                variant: 0,
                bindings: vec![],
                body: Box::new(Block {
                    stmts: vec![],
                    tail: BlockTail::Value(call(7, vec![])),
                }),
            },
            MatchArm {
                variant: 1,
                bindings: vec![],
                body: Box::new(Block {
                    stmts: vec![],
                    tail: BlockTail::Value(u64_const(0)),
                }),
            },
        ],
    };
    assert!(is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn readref_recurses_through_native_call() {
    // `Expr::ReadRef(inner)` must recurse with `is_eval_dce_droppable`,
    // not the stricter `is_pure_total` -- otherwise dropping a
    // `Stmt::Eval(ReadRef(<pure-total native>))` would be missed.
    let mut p = empty_program();
    register_native(&mut p, 7, pure_total_native("pure_native", Type::UInt(64)));

    let e = Expr::ReadRef(Box::new(call(7, vec![])));
    assert!(is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn let_in_inner_block_recurses_through_native_call() {
    // The block-level helper visits both stmts and the tail. A
    // `Stmt::Let { value: pure-total native call }` in an inner
    // block must classify the block as droppable.
    let mut p = empty_program();
    register_native(&mut p, 7, pure_total_native("pure_native", Type::UInt(64)));

    let then_b = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(VarId::from("a"))],
            value: call(7, vec![]),
        }],
        var("a"),
    );
    let else_b = block_value(vec![], u64_const(0));
    let e = Expr::If {
        cond: Box::new(bool_const(true)),
        then_branch: Box::new(then_b),
        else_branch: Box::new(else_b),
    };
    assert!(is_eval_dce_droppable(&e, &p));
}

#[test]
fn nested_let_with_partial_value_blocks_drop() {
    // Mixing a partial stmt inside the inner block must reject.
    let mut p = empty_program();
    register_native(&mut p, 7, pure_total_native("pure_native", Type::UInt(64)));

    let then_b = block_value(
        vec![Stmt::Let {
            pattern: vec![Some(VarId::from("a"))],
            // `1 + 2` -- arithmetic, partial.
            value: add(u64_const(1), u64_const(2)),
        }],
        var("a"),
    );
    let else_b = block_value(vec![], u64_const(0));
    let e = Expr::If {
        cond: Box::new(bool_const(true)),
        then_branch: Box::new(then_b),
        else_branch: Box::new(else_b),
    };
    assert!(!is_eval_dce_droppable(&e, &p));
}

#[test]
fn cast_op_is_not_droppable() {
    // UnOp::Cast can fail (e.g. u64 -> u8 overflow). Not droppable.
    let p = empty_program();
    let e = Expr::UnOp {
        op: crate::ir::UnOp::Cast(8),
        operand: Box::new(u64_const(300)),
    };
    assert!(!is_eval_dce_droppable(&e, &p));
    assert!(!is_pure_total(&e, &p));
}

#[test]
fn not_op_is_droppable() {
    // UnOp::Not is total over Bool.
    let p = empty_program();
    let e = Expr::UnOp {
        op: crate::ir::UnOp::Not,
        operand: Box::new(bool_const(true)),
    };
    assert!(is_eval_dce_droppable(&e, &p));
    assert!(is_pure_total(&e, &p));
}
