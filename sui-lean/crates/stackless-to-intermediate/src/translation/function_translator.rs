// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Function assembly — takes raw IR from structure discovery and produces
//! complete Function structs with phi detection, optimization passes, etc.

use crate::program_builder::ProgramBuilder;
use intermediate_theorem_format::{
    Function, FunctionSignature, IRNode, Parameter, TempId, TestExpectation, Type,
};
use move_compiler::shared::known_attributes::AttributeKind_;
use move_model::model::FunctionEnv;
use move_stackless_bytecode::function_target::FunctionTarget;
use std::collections::BTreeMap;

use crate::translation::ir_translator::temp_id;
use std::rc::Rc;

/// Build complete Function structs from raw (body, aborts) IR.
/// Returns a list of functions to emit: the main function and aborts.
/// Requires/ensures extraction happens later in finalize() after mutable threading.
pub fn build_function(
    builder: &mut ProgramBuilder,
    target: &FunctionTarget,
    mut variables: BTreeMap<TempId, Type>,
    mut signature: FunctionSignature,
    mut body: IRNode,
    mut aborts: IRNode,
) -> Vec<Function> {
    let func_env = target.func_env;
    let module_id = builder
        .program
        .modules
        .id_for_key(func_env.module_env.get_id());
    let name = builder.symbol_str(func_env.get_name()).to_string();
    let is_native = func_env.is_native();
    let test_expectation = detect_test_expectation(func_env);
    let is_uninterpreted = detect_uninterpreted(func_env);

    // NOTE: fold_early_returns is NOT run on `body` here. It runs
    // post-mutable-threading in the optimize_all() pass. Running it
    // before mutable threading would fold sequential if-statements into
    // nested ifs, breaking mutable threading's ability to distinguish
    // fall-through ifs from branching returns.

    // Replace Let values containing Inhabited with dummy false tuples
    // in the aborts side. Smarter than replacing individual Inhabited
    // nodes because it avoids type mismatches in function call arguments.
    aborts = intermediate_theorem_format::analysis::replace_inhabited_let_values(aborts);
    aborts = intermediate_theorem_format::analysis::fold_early_returns(aborts);
    // Rewrite Prover.asserts(p) calls into conditional abort conditions
    // so that ¬(func.aborts ...) means "all asserts hold".
    let assert_fn_ids: std::collections::HashSet<intermediate_theorem_format::FunctionID> =
        builder.program.asserts_function_id.into_iter().collect();
    aborts =
        intermediate_theorem_format::analysis::rewrite_asserts_in_aborts(aborts, &assert_fn_ids);
    aborts = intermediate_theorem_format::analysis::simplify_aborts(aborts);

    // Rename `_` variables to match parameter names
    let underscore_renames: std::collections::BTreeMap<String, String> = signature
        .parameters
        .iter()
        .filter(|p| p.name.as_str() != p.ssa_value.as_ref())
        .map(|p| (p.ssa_value.to_string(), p.name.clone()))
        .collect();
    if !underscore_renames.is_empty() {
        body = body.substitute_vars(&underscore_renames);
        aborts = aborts.substitute_vars(&underscore_renames);
        for p in signature.parameters.iter_mut() {
            if let Some(new_name) = underscore_renames.get(&p.ssa_value.to_string()) {
                p.ssa_value = Rc::from(new_name.as_str());
            }
        }
    }

    // Fix MutableReference types in the variable registry
    for node in body.iter() {
        if let IRNode::Let { pattern, value, .. } = node {
            if pattern.len() == 1 {
                if let IRNode::MutableBorrow {
                    val_expr,
                    state_type,
                    ..
                } = value.as_ref()
                {
                    // Always register MutableReference type for MutableBorrow assignments.
                    // The Move model's local_types may not reflect the mutable reference
                    // type correctly (e.g., TypeParameter instead of MutableReference),
                    // so we derive the type from the MutableBorrow structure itself.
                    let val_type = if let IRNode::Field {
                        struct_id,
                        field_index,
                        ..
                    } = val_expr.as_ref()
                    {
                        let s = builder.program.structs.get(struct_id);
                        s.fields[*field_index].field_type.clone()
                    } else {
                        state_type.clone()
                    };
                    variables.insert(
                        pattern[0].clone(),
                        Type::MutableReference(Box::new(val_type), Box::new(state_type.clone())),
                    );
                }
                if let IRNode::Call { function, .. } = value.as_ref() {
                    if let Some(func) = builder.program.functions.try_get(function) {
                        if let Type::MutableReference(inner, state) = &func.signature.return_type {
                            variables.insert(
                                pattern[0].clone(),
                                Type::MutableReference(inner.clone(), state.clone()),
                            );
                        }
                    }
                }
            }
        }
    }

    // Propagate MutableReference through variable copies
    loop {
        let mut changed = false;
        for node in body.iter() {
            if let IRNode::Let { pattern, value, .. } = node {
                if pattern.len() == 1 {
                    if let IRNode::Var(src_name) = value.as_ref() {
                        if let Some(ty @ Type::MutableReference(_, _)) =
                            variables.get(src_name.as_ref())
                        {
                            if !matches!(
                                variables.get(pattern[0].as_ref()),
                                Some(Type::MutableReference(_, _))
                            ) {
                                variables.insert(pattern[0].clone(), ty.clone());
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    let mut functions = Vec::new();

    // Main function (spec calls still in body — extracted later after mutable threading)
    functions.push(Function {
        module_id,
        name: name.clone(),
        signature: signature.clone(),
        body,

        theorem: None,
        is_native,
        mutual_group_id: None,
        test_expectation,
        is_uninterpreted,
    });

    // Aborts function
    functions.push(Function {
        module_id,
        name: format!("{}.aborts", name),
        signature: FunctionSignature {
            type_params: signature.type_params.clone(),
            parameters: signature.parameters.clone(),
            proof_params: Vec::new(),
            return_type: Type::Bool,
        },
        body: aborts,

        theorem: None,
        is_native: false,
        test_expectation: None,
        mutual_group_id: None,
        is_uninterpreted: false,
    });

    functions
}

/// Detect a `#[ext(..., uninterpreted, ...)]` attribute on `func_env`: the
/// function is an uninterpreted spec helper — its placeholder Move body is
/// never emitted; the renderer declares a Lean `opaque` constant instead.
fn detect_uninterpreted(func_env: &FunctionEnv) -> bool {
    use move_compiler::shared::known_attributes::KnownAttribute;
    if let Some(attr) = func_env
        .get_toplevel_attributes()
        .get_(&AttributeKind_::External)
    {
        if let KnownAttribute::External(ext) = &attr.value {
            return ext
                .attrs
                .iter()
                .any(|(_, name, _)| name.as_str() == "uninterpreted");
        }
    }
    false
}

/// Detect a `#[test]` attribute on `func_env` and, if present, return the
/// expectation encoded by any accompanying `#[expected_failure]`. Returns
/// `None` for non-test functions.
fn detect_test_expectation(func_env: &FunctionEnv) -> Option<TestExpectation> {
    let attrs = func_env.get_toplevel_attributes();
    attrs.get_(&AttributeKind_::Test)?;
    if attrs.get_(&AttributeKind_::ExpectedFailure).is_some() {
        Some(TestExpectation::MustAbort)
    } else {
        Some(TestExpectation::MustSucceed)
    }
}

/// Build a variable type map from a FunctionTarget.
pub fn build_variables(
    builder: &mut ProgramBuilder,
    target: &FunctionTarget,
) -> BTreeMap<TempId, Type> {
    target
        .data
        .local_types
        .iter()
        .enumerate()
        .map(|(index, move_type)| (temp_id(target, index), builder.convert_type(move_type)))
        .collect()
}

pub fn build_signature(
    builder: &mut ProgramBuilder,
    func_env: &FunctionEnv,
    target: &FunctionTarget,
) -> FunctionSignature {
    FunctionSignature {
        type_params: func_env
            .get_type_parameters()
            .iter()
            .map(|p| builder.symbol_str(p.0).to_string())
            .collect(),
        parameters: func_env
            .get_parameters()
            .iter()
            .enumerate()
            .map(|(i, param)| {
                let name = builder.symbol_str(param.0).to_string();
                let ty = builder.convert_type(&param.1);
                let ssa_value = temp_id(target, i);
                let name = if name == "_" {
                    format!("param{}", i)
                } else {
                    name
                };
                Parameter {
                    name,
                    param_type: ty,
                    ssa_value,
                }
            })
            .collect(),
        proof_params: Vec::new(),
        return_type: {
            let types: Vec<_> = func_env
                .get_return_types()
                .iter()
                .map(|t| builder.convert_type(t))
                .collect();
            match types.len() {
                0 => Type::Tuple(vec![]),
                1 => types.into_iter().next().unwrap(),
                _ => Type::Tuple(types),
            }
        },
    }
}
