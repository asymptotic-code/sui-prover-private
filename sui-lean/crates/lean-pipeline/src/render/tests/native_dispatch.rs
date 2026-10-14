use crate::ir::{
    AbortBit, DetBit, Effects, Expr, Function, FunctionKind, Module, MutLevel, Param, Signature,
    Struct, Type,
};
use crate::render::render_program;
use crate::stage_10_bounded_nat::prelude_fids::{ensure_main_fid, Op};

use super::fixtures::{add_function, add_native, empty_program, param, sig, var};

fn bounded_add_effects() -> Effects {
    Effects {
        aborts: AbortBit::Partial,
        det: DetBit::Det,
        mutation: MutLevel::NoMut,
        world_writes: false,
    }
}

fn bounded_caller(fun: crate::ir::FunId) -> Function {
    Function {
        module: 0,
        name: "caller".to_string(),
        signature: sig(
            vec![param("a", Type::UInt(64)), param("b", Type::UInt(64))],
            Type::UInt(64),
        ),
        body: crate::ir::Block::just(Expr::Call {
            fun,
            type_args: Vec::new(),
            args: vec![var("a"), var("b")],
        }),
        kind: FunctionKind::Source,
        effects: Effects::PURE,
        explicit_pure: true,
    }
}

fn theorem(name: &str, signature: Signature, body: Expr) -> Function {
    Function {
        module: 0,
        name: name.to_string(),
        signature,
        body: crate::ir::Block::just(body),
        kind: FunctionKind::Theorem {
            target: 0,
            source: 0,
        },
        effects: Effects::PURE,
        explicit_pure: false,
    }
}

#[test]
fn exact_stage10_intrinsic_uses_bounded_nat_override() {
    let mut program = empty_program();
    add_function(&mut program, 0, bounded_caller(1));
    let intrinsic = ensure_main_fid(&mut program, Op::Add, 64);
    assert_eq!(intrinsic, 1);

    let output = render_program(&program).unwrap();
    assert!(output.contains("BoundedNat.add a b"), "{output}");
    assert!(!output.contains("BoundedU64_add"), "{output}");
}

#[test]
fn reserved_name_user_native_does_not_use_bounded_nat_override() {
    let mut program = empty_program();
    add_function(&mut program, 0, bounded_caller(1));
    let mut decl = crate::ir::NativeDecl {
        module: 0,
        name: "BoundedU64_add".to_string(),
        signature: sig(
            vec![param("a", Type::UInt(64)), param("b", Type::UInt(64))],
            Type::UInt(64),
        ),
        effects: bounded_add_effects(),
        explicit_pure: true,
        is_framework: false,
        spec_target: None,
        user_native: Some(false),
    };
    add_native(&mut program, 1, decl.clone());

    let output = render_program(&program).unwrap();
    assert!(output.contains("p.M.BoundedU64_add a b"), "{output}");
    assert!(!output.contains("BoundedNat.add a b"), "{output}");

    decl.name = "BoundedU64_unknown".to_string();
    decl.is_framework = true;
    decl.user_native = None;
    program.natives.decls.insert(1, decl);
    let output = render_program(&program).unwrap();
    assert!(output.contains("p.M.BoundedU64_unknown a b"), "{output}");
    assert!(!output.contains("BoundedNat.add a b"), "{output}");
}

#[test]
fn reserved_connective_name_does_not_render_as_prop_intrinsic() {
    use crate::ir::connectives::Connective;

    let mut program = empty_program();
    add_function(
        &mut program,
        0,
        Function {
            module: 0,
            name: "target".to_string(),
            signature: sig(Vec::new(), Type::Bool),
            body: crate::ir::Block::just(Expr::Const(crate::ir::Const::Bool(true))),
            kind: FunctionKind::Source,
            effects: Effects::PURE,
            explicit_pure: true,
        },
    );
    add_native(
        &mut program,
        1,
        crate::ir::NativeDecl {
            module: 0,
            name: Connective::Imp.native_name().to_string(),
            signature: Connective::Imp.signature(),
            effects: Effects::PURE,
            explicit_pure: true,
            is_framework: false,
            spec_target: None,
            user_native: Some(true),
        },
    );
    add_function(
        &mut program,
        2,
        theorem(
            "fake_imp_correct",
            sig(Vec::new(), Type::Bool),
            Expr::Call {
                fun: 1,
                type_args: Vec::new(),
                args: vec![
                    Expr::Const(crate::ir::Const::Bool(true)),
                    Expr::Const(crate::ir::Const::Bool(false)),
                ],
            },
        ),
    );

    let output = render_program(&program).unwrap();
    let theorem = output
        .split("\n\n")
        .find(|declaration| declaration.contains("fake_imp_correct"))
        .expect("theorem declaration");
    assert!(theorem.contains("= true"), "{theorem}");
    assert!(!theorem.contains('→'), "{theorem}");
}

#[test]
fn reserved_world_wf_name_does_not_render_as_prop_intrinsic() {
    let mut program = empty_program();
    program.modules.insert(
        1,
        Module {
            name: "dynamic_field".to_string(),
            package_name: "Sui".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    let signature = sig(vec![param("world", Type::Unit)], Type::Bool);
    add_function(
        &mut program,
        0,
        Function {
            module: 0,
            name: "target".to_string(),
            signature: signature.clone(),
            body: crate::ir::Block::just(Expr::Const(crate::ir::Const::Bool(true))),
            kind: FunctionKind::Source,
            effects: Effects::PURE,
            explicit_pure: true,
        },
    );
    add_native(
        &mut program,
        1,
        crate::ir::NativeDecl {
            module: 1,
            name: crate::stage_12_obligations::WORLD_WF_NAME.to_string(),
            signature: signature.clone(),
            effects: Effects::PURE,
            explicit_pure: true,
            is_framework: false,
            spec_target: None,
            user_native: Some(true),
        },
    );
    add_function(
        &mut program,
        2,
        theorem(
            "fake_world_wf_correct",
            signature,
            Expr::Call {
                fun: 1,
                type_args: Vec::new(),
                args: vec![var("world")],
            },
        ),
    );

    let output = render_program(&program).unwrap();
    let theorem = output
        .split("\n\n")
        .find(|declaration| declaration.contains("fake_world_wf_correct"))
        .expect("theorem declaration");
    assert!(theorem.contains("world_wf"), "{theorem}");
    assert!(theorem.contains("= true"), "{theorem}");
}

fn bcs_program(package: &str, module_name: &str, address: &str) -> crate::ir::Program {
    let mut program = empty_program();
    program.modules.insert(
        1,
        Module {
            name: module_name.to_string(),
            package_name: package.to_string(),
            address: address.to_string(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    program.modules.insert(
        2,
        Module {
            name: "type_name".to_string(),
            package_name: "MoveStdlib".to_string(),
            address: "1".to_string(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    program.structs.insert(
        0,
        Struct {
            module_id: 2,
            name: "TypeName".to_string(),
            qualified_name: "0x1::type_name::TypeName".to_string(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: None,
            is_native: true,
        },
    );
    let type_name = Type::Struct {
        struct_id: 0,
        type_args: Vec::new(),
    };
    add_native(
        &mut program,
        1,
        crate::ir::NativeDecl {
            module: 1,
            name: "to_bytes".to_string(),
            signature: Signature {
                type_params: vec!["X".to_string()],
                params: vec![Param {
                    name: "v".to_string(),
                    var: "v".into(),
                    ty: Type::Reference(Box::new(Type::TypeParam(0))),
                }],
                return_type: Type::Vector(Box::new(Type::UInt(8))),
            },
            effects: Effects::PURE,
            explicit_pure: false,
            is_framework: true,
            spec_target: None,
            user_native: None,
        },
    );
    add_function(
        &mut program,
        0,
        Function {
            module: 0,
            name: "caller".to_string(),
            signature: sig(
                vec![param("tn", type_name.clone())],
                Type::Vector(Box::new(Type::UInt(8))),
            ),
            body: crate::ir::Block::just(Expr::Call {
                fun: 1,
                type_args: vec![type_name],
                args: vec![var("tn")],
            }),
            kind: FunctionKind::Source,
            effects: Effects::PURE,
            explicit_pure: true,
        },
    );
    program
}

#[test]
fn type_name_bcs_override_requires_exact_framework_identity() {
    let exact = render_program(&bcs_program("MoveStdlib", "bcs", "1")).unwrap();
    assert!(exact.contains("_root_.Type_name.to_bytes tn"), "{exact}");

    let exact = render_program(&bcs_program("Sui", "bcs", "2")).unwrap();
    assert!(exact.contains("_root_.Type_name.to_bytes tn"), "{exact}");

    let lookalike = render_program(&bcs_program("Lookalike", "bcs", "1")).unwrap();
    assert!(
        lookalike.contains("_root_.Lookalike.Bcs.to_bytes"),
        "{lookalike}"
    );
    assert!(
        !lookalike.contains("_root_.Type_name.to_bytes"),
        "{lookalike}"
    );
    assert!(!lookalike.contains("(U := _root_.TyCode)"), "{lookalike}");

    for program in [
        bcs_program("MoveStdlib", "bcs_lookalike", "1"),
        bcs_program("MoveStdlib", "bcs", "2"),
        bcs_program("Sui", "bcs", "1"),
    ] {
        let output = render_program(&program).unwrap();
        assert!(!output.contains("_root_.Type_name.to_bytes"), "{output}");
        assert!(!output.contains("(U := _root_.TyCode)"), "{output}");
    }

    let mut malformed = bcs_program("MoveStdlib", "bcs", "1");
    malformed
        .natives
        .decls
        .get_mut(&1)
        .unwrap()
        .signature
        .return_type = Type::Unit;
    let output = render_program(&malformed).unwrap();
    assert!(!output.contains("_root_.Type_name.to_bytes"), "{output}");
    assert!(!output.contains("(U := _root_.TyCode)"), "{output}");

    let mut malformed = bcs_program("MoveStdlib", "bcs", "1");
    malformed
        .natives
        .decls
        .get_mut(&1)
        .unwrap()
        .signature
        .params[0]
        .ty = Type::TypeParam(0);
    let output = render_program(&malformed).unwrap();
    assert!(!output.contains("_root_.Type_name.to_bytes"), "{output}");
    assert!(!output.contains("(U := _root_.TyCode)"), "{output}");
}

#[test]
fn type_name_bcs_override_allows_mixed_framework_module() {
    let mut program = bcs_program("MoveStdlib", "bcs", "1");
    program.modules.get_mut(&1).unwrap().is_native = false;
    program.natives.decls.get_mut(&1).unwrap().is_framework = false;

    let output = render_program(&program).unwrap();
    assert!(output.contains("_root_.Type_name.to_bytes tn"), "{output}");
}

#[test]
fn mixed_framework_bcs_value_call_keeps_tycode_pin() {
    let mut program = bcs_program("Sui", "bcs", "2");
    program.modules.get_mut(&1).unwrap().is_native = false;
    program.natives.decls.get_mut(&1).unwrap().is_framework = false;
    let caller = program.functions.get_mut(&0).unwrap();
    caller.signature.params[0] = param("value", Type::UInt(16));
    caller.body = crate::ir::Block::just(Expr::Call {
        fun: 1,
        type_args: vec![Type::UInt(16)],
        args: vec![var("value")],
    });

    let output = render_program(&program).unwrap();
    assert!(
        output.contains("_root_.Bcs.to_bytes (U := _root_.TyCode) (BoundedNat (2^16)) value"),
        "{output}"
    );
}

#[test]
fn bcs_override_rejects_every_noncanonical_contract_field() {
    let base = bcs_program("Sui", "bcs", "2");
    let mut cases = Vec::new();

    let mut program = base.clone();
    program.natives.decls.get_mut(&1).unwrap().name = "to_bytes_lookalike".to_string();
    cases.push(("name", program));

    let mut program = base.clone();
    program.natives.decls.get_mut(&1).unwrap().user_native = Some(false);
    cases.push(("user native", program));

    let mut program = base.clone();
    program.natives.decls.get_mut(&1).unwrap().spec_target = Some(0);
    cases.push(("spec target", program));

    let mut program = base.clone();
    program.natives.decls.get_mut(&1).unwrap().effects = bounded_add_effects();
    cases.push(("effects", program));

    let mut program = base;
    program
        .natives
        .decls
        .get_mut(&1)
        .unwrap()
        .signature
        .type_params
        .clear();
    cases.push(("generic arity", program));

    for (field, program) in cases {
        assert!(
            !crate::render::native_models::is_bcs_to_bytes_model(&program, 1),
            "accepted noncanonical {field}"
        );
    }
}
