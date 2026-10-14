use crate::ir::{Expr, Module, Stmt, Type};
use crate::render::render_program;

use super::fixtures::*;

fn mutable_u64() -> Type {
    Type::MutableRef {
        inner: Box::new(Type::UInt(64)),
        root: Box::new(Type::UInt(64)),
    }
}

fn call(fun: crate::ir::FunId, args: Vec<Expr>) -> Expr {
    Expr::Call {
        fun,
        type_args: vec![],
        args,
    }
}

fn add_sui_module(program: &mut crate::ir::Program) {
    program.modules.insert(
        1,
        Module {
            name: "bridge".to_string(),
            package_name: "Sui".to_string(),
            address: String::new(),
            required_imports: vec![],
            is_native: false,
        },
    );
}

fn add_mutation_leaf(program: &mut crate::ir::Program, fun: crate::ir::FunId, module: usize) {
    add_function(
        program,
        fun,
        func(
            "mutation_leaf",
            sig(vec![param("r", mutable_u64())], Type::Unit),
            body(vec![], Expr::Unit),
            module,
        ),
    );
}

fn add_transitive_target(
    program: &mut crate::ir::Program,
    fun: crate::ir::FunId,
    leaf: crate::ir::FunId,
    module: usize,
) {
    add_function(
        program,
        fun,
        func(
            "target",
            sig(vec![param("x", Type::UInt(64))], Type::Unit),
            body(vec![], call(leaf, vec![Expr::BorrowLoc("x".into())])),
            module,
        ),
    );
}

fn add_caller(program: &mut crate::ir::Program, target: crate::ir::FunId) {
    add_function(
        program,
        0,
        func(
            "caller",
            sig(vec![param("x", Type::UInt(64))], Type::Unit),
            body(vec![], call(target, vec![var("x")])),
            0,
        ),
    );
}

fn assert_bridge_count(program: &crate::ir::Program, expected: usize) {
    let output = render_program(program).expect("render");
    assert_eq!(
        output.matches("(__MutKey := AnyKey)").count(),
        expected,
        "unexpected MutKey bridge count:\n{output}"
    );
}

#[test]
fn cross_function_lemma_mutation_user_without_mutable_signature_slot_gets_bridge() {
    let mut program = empty_program();
    add_sui_module(&mut program);
    add_caller(&mut program, 1);
    add_transitive_target(&mut program, 1, 2, 1);
    add_mutation_leaf(&mut program, 2, 1);

    assert_bridge_count(&program, 1);
}

#[test]
fn user_package_callee_does_not_get_bridge() {
    let mut program = empty_program();
    add_caller(&mut program, 1);
    add_transitive_target(&mut program, 1, 2, 0);
    add_mutation_leaf(&mut program, 2, 0);

    assert_bridge_count(&program, 0);
}

#[test]
fn non_mutation_user_does_not_get_bridge() {
    let mut program = empty_program();
    add_sui_module(&mut program);
    add_caller(&mut program, 1);
    add_function(
        &mut program,
        1,
        func(
            "target",
            sig(vec![param("x", Type::UInt(64))], Type::Unit),
            body(vec![], Expr::Unit),
            1,
        ),
    );

    assert_bridge_count(&program, 0);
}

#[test]
fn mutable_param_determines_key_without_bridge() {
    let mut program = empty_program();
    add_sui_module(&mut program);
    add_mutation_leaf(&mut program, 1, 1);
    add_function(
        &mut program,
        0,
        func(
            "caller",
            sig(vec![param("x", Type::UInt(64))], Type::Unit),
            body(vec![], call(1, vec![Expr::BorrowLoc("x".into())])),
            0,
        ),
    );

    assert_bridge_count(&program, 0);
}

#[test]
fn mutable_result_without_mutable_parameter_gets_bridge() {
    let mut program = empty_program();
    add_sui_module(&mut program);
    add_function(
        &mut program,
        1,
        func(
            "target",
            sig(vec![param("x", Type::UInt(64))], mutable_u64()),
            body(vec![], Expr::BorrowLoc("x".into())),
            1,
        ),
    );
    add_function(
        &mut program,
        0,
        func(
            "caller",
            sig(vec![param("x", Type::UInt(64))], mutable_u64()),
            body(vec![], call(1, vec![var("x")])),
            0,
        ),
    );

    assert_bridge_count(&program, 1);
}

#[test]
fn discarded_mutable_result_gets_bridge() {
    let mut program = empty_program();
    add_sui_module(&mut program);
    add_function(
        &mut program,
        1,
        func(
            "target",
            sig(vec![param("x", Type::UInt(64))], mutable_u64()),
            body(vec![], Expr::BorrowLoc("x".into())),
            1,
        ),
    );
    add_function(
        &mut program,
        0,
        func(
            "caller",
            sig(vec![param("x", Type::UInt(64))], Type::Unit),
            body(vec![Stmt::Eval(call(1, vec![var("x")]))], Expr::Unit),
            0,
        ),
    );

    let output = render_program(&program).expect("render");
    assert_eq!(output.matches("(__MutKey := AnyKey)").count(), 1);
    assert!(output.contains("let _ :="));
}

#[test]
fn erased_inner_call_does_not_create_a_phantom_bridge() {
    let mut program = empty_program();
    add_sui_module(&mut program);
    add_caller(&mut program, 1);
    add_function(
        &mut program,
        1,
        func(
            "target",
            sig(vec![param("x", Type::UInt(64))], Type::Unit),
            body(
                vec![],
                Expr::If {
                    cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
                    then_branch: Box::new(crate::ir::Block {
                        stmts: vec![Stmt::Eval(call(2, vec![Expr::BorrowLoc("x".into())]))],
                        tail: crate::ir::BlockTail::Value(Expr::Unit),
                    }),
                    else_branch: Box::new(crate::ir::Block::just(Expr::Unit)),
                },
            ),
            1,
        ),
    );
    add_mutation_leaf(&mut program, 2, 1);

    let output = render_program(&program).expect("render");
    assert_eq!(output.matches("(__MutKey := AnyKey)").count(), 0);
    assert!(
        !output.contains("Bridge.mutation_leaf"),
        "erased call must not influence rendered scope:\n{output}"
    );
}

#[test]
fn eval_position_inner_call_keeps_its_required_bridge() {
    let mut program = empty_program();
    add_sui_module(&mut program);
    add_caller(&mut program, 1);
    add_function(
        &mut program,
        1,
        func(
            "target",
            sig(vec![param("x", Type::UInt(64))], Type::Unit),
            body(
                vec![Stmt::Eval(Expr::If {
                    cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
                    then_branch: Box::new(crate::ir::Block {
                        stmts: vec![Stmt::Eval(call(2, vec![Expr::BorrowLoc("x".into())]))],
                        tail: crate::ir::BlockTail::Value(Expr::Unit),
                    }),
                    else_branch: Box::new(crate::ir::Block::just(Expr::Unit)),
                })],
                Expr::Unit,
            ),
            1,
        ),
    );
    add_mutation_leaf(&mut program, 2, 1);

    let output = render_program(&program).expect("render");
    assert_eq!(output.matches("(__MutKey := AnyKey)").count(), 1);
    assert!(output.contains("Bridge.mutation_leaf"));
}

#[test]
fn recursive_self_call_does_not_get_bridge() {
    let mut program = empty_program();
    add_sui_module(&mut program);
    add_mutation_leaf(&mut program, 2, 1);
    add_function(
        &mut program,
        1,
        func(
            "target",
            sig(vec![param("x", Type::UInt(64))], Type::Unit),
            body(
                vec![Stmt::Eval(call(2, vec![Expr::BorrowLoc("x".into())]))],
                call(1, vec![var("x")]),
            ),
            1,
        ),
    );

    assert_bridge_count(&program, 0);
}

fn generic_key_borrow(module: usize) -> crate::ir::Function {
    use crate::ir::{Block, BlockTail, Param, Signature, VarId};

    crate::ir::Function {
        module,
        name: "bk".to_string(),
        signature: Signature {
            type_params: vec!["K".to_string()],
            params: vec![
                Param {
                    name: "t".to_string(),
                    var: VarId::from("t"),
                    ty: Type::MutableRef {
                        inner: Box::new(Type::TypeParam(0)),
                        root: Box::new(Type::TypeParam(0)),
                    },
                },
                Param {
                    name: "k".to_string(),
                    var: VarId::from("k"),
                    ty: Type::TypeParam(0),
                },
            ],
            return_type: Type::TypeParam(0),
        },
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Borrow {
                step: crate::ir::path::PathStep::MapKey {
                    key: Box::new(var("k")),
                    key_type: Type::TypeParam(0),
                    value_type: Type::TypeParam(0),
                    df_value: None,
                },
                base: Box::new(var("t")),
            }),
        },
        kind: crate::ir::FunctionKind::Source,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    }
}

fn def_line<'a>(output: &'a str, name: &str) -> &'a str {
    output
        .lines()
        .find(|l| l.trim_start().starts_with(&format!("def {name} ")))
        .unwrap_or_else(|| panic!("no `def {name}` line:\n{output}"))
}

#[test]
fn lemma_generic_map_key_uses_prelude_key_classes_not_user_anykey_classes() {
    // Framework (lemma) modules never import the per-package
    // `Generated.AnyKey`, where `ToAnyKey` / `FromAnyKey` live -- so a
    // `[ToAnyKey K]` binder there names an unknown class and Lean fails with
    // `invalid binder annotation, type is not a class instance` (hashi:
    // `Sui/Linked_table.lean`, reached via `linked_table::pop_front`). A generic
    // key in a lemma package must go through the prelude's `IntoKey` /
    // `FromKey` over the abstract `AnyKey := __MutKey`, like concrete keys do.
    let mut program = empty_program();
    add_sui_module(&mut program);
    add_function(&mut program, 1, generic_key_borrow(1));

    let output = render_program(&program).expect("render");
    let line = def_line(&output, "bk");

    assert!(
        line.contains("[IntoKey AnyKey K] [FromKey AnyKey K]"),
        "lemma binder:\n{line}"
    );
    assert!(
        !line.contains("ToAnyKey") && !line.contains("FromAnyKey"),
        "lemma binder:\n{line}"
    );
    assert!(
        output.contains("(IntoKey.intoKey k)"),
        "lemma key wrap:\n{output}"
    );
}

#[test]
fn user_generic_map_key_keeps_the_anykey_classes() {
    let mut program = empty_program();
    add_function(&mut program, 1, generic_key_borrow(0));

    let output = render_program(&program).expect("render");
    let line = def_line(&output, "bk");

    assert!(
        line.contains("[ToAnyKey K] [FromAnyKey K]"),
        "user binder:\n{line}"
    );
    assert!(
        output.contains("(ToAnyKey.toAnyKey k)"),
        "user key wrap:\n{output}"
    );
}

#[test]
fn generated_anykey_bridges_user_key_classes_to_the_prelude_ones() {
    // A user function generic over `K` (carrying `[ToAnyKey K] [FromAnyKey K]`)
    // that calls a lemma function generic over the same key must supply
    // `[IntoKey AnyKey K] [FromKey AnyKey K]` -- the bridges derive them.
    let program = empty_program();
    let output = render_program(&program).expect("render");

    assert!(
        output.contains("instance (priority := low) {A : Type} [ToAnyKey A] : IntoKey AnyKey A where intoKey := ToAnyKey.toAnyKey"),
        "missing IntoKey bridge:\n{output}"
    );
    assert!(
        output.contains("instance (priority := low) {A : Type} [FromAnyKey A] : FromKey AnyKey A where fromKey := FromAnyKey.fromAnyKey"),
        "missing FromKey bridge:\n{output}"
    );
}

#[test]
fn prelude_declares_the_inverse_key_class() {
    let prelude = include_str!("../../../lemmas/Prelude/Mutation.lean");
    assert!(
        prelude.contains("class FromKey (Key : Type) (A : Type) where"),
        "FromKey missing"
    );
}
