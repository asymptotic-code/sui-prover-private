//! Dynamic-field universe (`{__TyU} [Universe __TyU]` + `[HasCode __TyU T]`)
//! must follow CALL edges inside framework (lemma) packages. A function that
//! calls a df-universe function with its own type params needs the same
//! binders -- otherwise Lean cannot unify the callee's world (its DfEntry slot
//! is `Bag.Entry __TyU`) with the caller's plain `World`, and fails with
//! `failed to synthesize Universe ?m` (hashi: `sui::linked_table::pop_front`
//! calling `remove`, which hits `dynamic_field` directly).

use crate::ir::{Expr, FunId, Module, Signature, Type};
use crate::render::render_program;

use super::fixtures::*;

fn sui_module(name: &str, is_native: bool) -> Module {
    Module {
        name: name.to_string(),
        package_name: "Sui".to_string(),
        address: String::new(),
        required_imports: vec![],
        is_native,
    }
}

fn kv_sig(params: Vec<crate::ir::Param>) -> Signature {
    Signature {
        type_params: vec!["K".to_string(), "V".to_string()],
        params,
        return_type: Type::Unit,
    }
}

fn call_kv(fun: FunId, args: Vec<Expr>) -> Expr {
    Expr::Call {
        fun,
        type_args: vec![Type::TypeParam(0), Type::TypeParam(1)],
        args,
    }
}

fn program() -> crate::ir::Program {
    let mut program = empty_program();
    program.modules.insert(1, sui_module("dynamic_field", true));
    program.modules.insert(2, sui_module("linked", false));
    let kv = || {
        vec![
            param("k", Type::TypeParam(0)),
            param("v", Type::TypeParam(1)),
        ]
    };
    add_native(
        &mut program,
        10,
        native(
            "add",
            kv_sig(kv()),
            1,
            crate::ir::Effects::CONSERVATIVE,
            true,
        ),
    );
    add_function(
        &mut program,
        1,
        func(
            "leaf",
            kv_sig(kv()),
            body(vec![], call_kv(10, vec![var("k"), var("v")])),
            2,
        ),
    );
    add_function(
        &mut program,
        2,
        func(
            "mid",
            kv_sig(kv()),
            body(vec![], call_kv(1, vec![var("k"), var("v")])),
            2,
        ),
    );
    program
}

fn def_line<'a>(output: &'a str, name: &str) -> &'a str {
    output
        .lines()
        .find(|l| l.trim_start().starts_with(&format!("def {name} ")))
        .unwrap_or_else(|| panic!("no `def {name}` line:\n{output}"))
}

#[test]
fn a_direct_dynamic_field_caller_binds_the_universe() {
    let output = render_program(&program()).expect("render");
    let line = def_line(&output, "leaf");
    assert!(line.contains("{__TyU : Type} [Universe __TyU]"), "{line}");
    assert!(
        line.contains("[HasCode __TyU K]") && line.contains("[HasCode __TyU V]"),
        "{line}"
    );
}

#[test]
fn a_caller_of_a_dynamic_field_function_inherits_its_universe_binders() {
    let output = render_program(&program()).expect("render");
    let line = def_line(&output, "mid");
    assert!(line.contains("{__TyU : Type} [Universe __TyU]"), "{line}");
    assert!(
        line.contains("[HasCode __TyU K]") && line.contains("[HasCode __TyU V]"),
        "{line}"
    );
}

fn node_program(caller_params: [&str; 2]) -> crate::ir::Program {
    use crate::ir::{Struct, StructId};

    let mut program = empty_program();
    program.modules.insert(1, sui_module("dynamic_field", true));
    program.modules.insert(2, sui_module("linked", false));
    let node: StructId = 0;
    add_struct(
        &mut program,
        node,
        Struct {
            module_id: 2,
            name: "Node".to_string(),
            qualified_name: "0x2::linked::Node".to_string(),
            type_params: vec!["K".to_string(), "V".to_string()],
            fields: vec![],
            variants: None,
            is_native: false,
        },
    );
    let node_kv = Type::Struct {
        struct_id: node,
        type_args: vec![Type::TypeParam(0), Type::TypeParam(1)],
    };
    let kv = || {
        vec![
            param("k", Type::TypeParam(0)),
            param("v", Type::TypeParam(1)),
        ]
    };
    add_native(
        &mut program,
        10,
        native(
            "add",
            kv_sig(kv()),
            1,
            crate::ir::Effects::CONSERVATIVE,
            true,
        ),
    );
    // leaf<K, V> stores a `Node<K, V>` value: a concrete df type over its params.
    add_function(
        &mut program,
        1,
        func(
            "leaf",
            kv_sig(kv()),
            body(
                vec![],
                Expr::Call {
                    fun: 10,
                    type_args: vec![Type::TypeParam(0), node_kv],
                    args: vec![var("k"), var("v")],
                },
            ),
            2,
        ),
    );
    let mut caller_sig = kv_sig(kv());
    caller_sig.type_params = caller_params.iter().map(|s| s.to_string()).collect();
    add_function(
        &mut program,
        2,
        func(
            "mid",
            caller_sig,
            body(vec![], call_kv(1, vec![var("k"), var("v")])),
            2,
        ),
    );
    program
}

#[test]
fn a_callee_concrete_type_over_its_params_is_mapped_into_the_caller() {
    let output = render_program(&node_program(["K", "V"])).expect("render");
    let leaf = def_line(&output, "leaf");
    assert!(leaf.contains("Linked.Node K V"), "{leaf}");
    let mid = def_line(&output, "mid");
    assert!(mid.contains("Linked.Node K V"), "{mid}");
}

#[test]
fn the_mapped_concrete_type_uses_the_callers_own_param_names() {
    let output = render_program(&node_program(["A", "B"])).expect("render");
    let mid = def_line(&output, "mid");
    assert!(mid.contains("Linked.Node A B"), "{mid}");
    assert!(!mid.contains("Linked.Node K V"), "{mid}");
}
