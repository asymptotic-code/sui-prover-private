// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Post-threading spec extraction — extracts requires/ensures specs from
//! function bodies AFTER mutable threading has run, so that the spec preamble
//! includes mutation rebindings (e.g. `let table := __mut_ret_0`).

use crate::data::functions::{Function, FunctionID, FunctionSignature};
use crate::data::types::Type;
use crate::data::Program;
use crate::{Const, IRNode};
use std::rc::Rc;

#[derive(Debug, Clone, Copy)]
enum SpecKind {
    Requires,
    Ensures,
    Asserts,
}

struct CollectedSpec {
    kind: SpecKind,
    condition: IRNode,
    preamble: Vec<(Vec<Rc<str>>, IRNode)>,
}

/// Extract requires/ensures specs from all function bodies.
/// Must be called AFTER mutable threading so that spec preambles include
/// mutation rebindings.
pub fn extract_all_specs(program: &mut Program) {
    let requires_id = program.requires_function_id;
    let ensures_id = program.ensures_function_id;
    let asserts_id = program.asserts_function_id;

    if requires_id.is_none() && ensures_id.is_none() && asserts_id.is_none() {
        return;
    }

    let func_ids: Vec<usize> = program.functions.iter_ids().collect();
    let mut new_functions: Vec<Function> = Vec::new();

    for func_id in func_ids {
        let func = program.functions.get(&func_id);

        if func.is_native {
            continue;
        }

        // For aborts functions, just strip spec calls without creating new functions
        if func.name.contains(".aborts") {
            let cleaned = strip_spec_calls(&func.body, requires_id, ensures_id, asserts_id);
            let func_mut = program.functions.get_mut(func_id);
            func_mut.body = cleaned;
            continue;
        }

        // Skip already-extracted spec functions
        if func.name.contains(".requires") || func.name.contains(".ensures") {
            continue;
        }

        let mut specs = Vec::new();
        let cleaned_body = extract_specs_recursive(
            &func.body,
            &mut specs,
            &[],
            requires_id,
            ensures_id,
            asserts_id,
            0,
        );

        if specs.is_empty() {
            continue;
        }

        let module_id = func.module_id;
        let name = func.name.clone();
        let signature = func.signature.clone();
        let func_mut = program.functions.get_mut(func_id);
        func_mut.body = cleaned_body;

        let mut requires_count = 0usize;
        let mut ensures_count = 0usize;
        let mut asserts_count = 0usize;
        for collected in specs {
            let spec_body = build_spec_body_with_preamble(collected.condition, collected.preamble);

            match collected.kind {
                SpecKind::Requires => {
                    let req_name = if requires_count == 0 {
                        format!("{}.requires", name)
                    } else {
                        format!("{}.requires_{}", name, requires_count)
                    };
                    requires_count += 1;
                    new_functions.push(Function {
                        module_id,
                        name: req_name,
                        signature: FunctionSignature {
                            type_params: signature.type_params.clone(),
                            parameters: signature.parameters.clone(),
                            proof_params: Vec::new(),
                            return_type: Type::Prop,
                        },
                        body: spec_body,

                        theorem: None,
                        is_native: false,
                        mutual_group_id: None,
                        test_expectation: None,
                    });
                }
                SpecKind::Ensures => {
                    let ens_name = if ensures_count == 0 {
                        format!("{}.ensures", name)
                    } else {
                        format!("{}.ensures_{}", name, ensures_count)
                    };
                    ensures_count += 1;
                    new_functions.push(Function {
                        module_id,
                        name: ens_name,
                        signature: FunctionSignature {
                            type_params: signature.type_params.clone(),
                            parameters: signature.parameters.clone(),
                            proof_params: Vec::new(),
                            return_type: Type::Prop,
                        },
                        body: spec_body,

                        theorem: None,
                        is_native: false,
                        mutual_group_id: None,
                        test_expectation: None,
                    });
                }
                SpecKind::Asserts => {
                    let assert_name = if asserts_count == 0 {
                        format!("{}.asserts_cond", name)
                    } else {
                        format!("{}.asserts_cond_{}", name, asserts_count)
                    };
                    asserts_count += 1;
                    new_functions.push(Function {
                        module_id,
                        name: assert_name,
                        signature: FunctionSignature {
                            type_params: signature.type_params.clone(),
                            parameters: signature.parameters.clone(),
                            proof_params: Vec::new(),
                            return_type: Type::Prop,
                        },
                        body: spec_body,

                        theorem: None,
                        is_native: false,
                        mutual_group_id: None,
                        test_expectation: None,
                    });
                }
            }
        }
    }

    for func in new_functions {
        program.functions.add(func);
    }
}

fn extract_specs_recursive(
    node: &IRNode,
    specs: &mut Vec<CollectedSpec>,
    current_preamble: &[(Vec<Rc<str>>, IRNode)],
    requires_id: Option<FunctionID>,
    ensures_id: Option<FunctionID>,
    asserts_id: Option<FunctionID>,
    depth: usize,
) -> IRNode {
    if depth > 10000 {
        panic!("extract_specs_recursive exceeded depth limit of 10000");
    }

    // Check if this is a spec function call
    if let IRNode::Call { function, args, .. } = node {
        let spec_kind = if Some(*function) == requires_id {
            Some(SpecKind::Requires)
        } else if Some(*function) == ensures_id {
            Some(SpecKind::Ensures)
        } else if Some(*function) == asserts_id {
            Some(SpecKind::Asserts)
        } else {
            None
        };

        if let Some(kind) = spec_kind {
            if let Some(cond) = args.first() {
                specs.push(CollectedSpec {
                    kind,
                    condition: cond.clone(),
                    preamble: current_preamble.to_vec(),
                });
                // Asserts are no-ops in the body; requires/ensures get stripped
                if matches!(kind, SpecKind::Asserts) {
                    return node.clone();
                }
                return IRNode::default();
            }
        }
    }

    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // Build preamble including this Let if it either binds a real name
            // OR carries a rebinding side effect. The latter covers the
            // empty-pattern `let () := WriteBack { child: __mut_ret, parent: p }`
            // (and `WriteRef`) that mutable threading emits to rebind a caller's
            // `&mut` after a void call: e.g. `staking_pool::split_staked_sui(stake, ..)`
            // lowers to `let [__mut_ret_0, ..] := call; let () := WriteBack { __mut_ret_0 -> stake }`.
            // Dropping that WriteBack from the preamble would leave a lifted
            // `ensures(staked_sui_amount(stake))` reading the pre-call `stake`,
            // silently turning a true postcondition into an unprovable one.
            let mut new_preamble = current_preamble.to_vec();
            let binds_name = !pattern.is_empty() && !pattern.iter().all(|p| p.as_ref() == "_");
            let is_rebinding_effect = matches!(
                value.as_ref(),
                IRNode::WriteBack { .. } | IRNode::WriteRef { .. }
            );
            if binds_name || is_rebinding_effect {
                new_preamble.push((pattern.clone(), (**value).clone()));
            }

            // Recurse into value and body with the extended preamble
            let new_value = extract_specs_recursive(
                value,
                specs,
                &new_preamble,
                requires_id,
                ensures_id,
                asserts_id,
                depth + 1,
            );
            let new_body = extract_specs_recursive(
                body,
                specs,
                &new_preamble,
                requires_id,
                ensures_id,
                asserts_id,
                depth + 1,
            );
            IRNode::Let {
                pattern: pattern.clone(),
                value: Box::new(new_value),
                body: Box::new(new_body),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Track specs before recursing into each branch so we can wrap
            // newly-found specs with the branch condition.
            let specs_before = specs.len();
            let new_then = extract_specs_recursive(
                then_branch,
                specs,
                current_preamble,
                requires_id,
                ensures_id,
                asserts_id,
                depth + 1,
            );
            let then_specs_end = specs.len();
            let new_else = extract_specs_recursive(
                else_branch,
                specs,
                current_preamble,
                requires_id,
                ensures_id,
                asserts_id,
                depth + 1,
            );
            let else_specs_end = specs.len();

            // Wrap then-branch specs: `if cond then spec_condition else True`
            for spec in &mut specs[specs_before..then_specs_end] {
                spec.condition = IRNode::If {
                    cond: cond.clone(),
                    then_branch: Box::new(spec.condition.clone()),
                    else_branch: Box::new(IRNode::Const(Const::Bool(true))),
                };
            }
            // Wrap else-branch specs: `if cond then True else spec_condition`
            for spec in &mut specs[then_specs_end..else_specs_end] {
                spec.condition = IRNode::If {
                    cond: cond.clone(),
                    then_branch: Box::new(IRNode::Const(Const::Bool(true))),
                    else_branch: Box::new(spec.condition.clone()),
                };
            }

            let new_cond = extract_specs_recursive(
                cond,
                specs,
                current_preamble,
                requires_id,
                ensures_id,
                asserts_id,
                depth + 1,
            );

            IRNode::If {
                cond: Box::new(new_cond),
                then_branch: Box::new(new_then),
                else_branch: Box::new(new_else),
            }
        }
        other => other.clone(),
    }
}

/// Strip requires/ensures/asserts calls from a function body, replacing them with Unit.
/// Used for aborts functions where spec calls should be removed but not extracted.
fn strip_spec_calls(
    node: &IRNode,
    requires_id: Option<FunctionID>,
    ensures_id: Option<FunctionID>,
    asserts_id: Option<FunctionID>,
) -> IRNode {
    // Recurse through every node type (bottom-up). The hand-rolled
    // `Let`/`If`-only walk used previously missed spec calls nested in
    // `Match`/`MatchOption` arms, which is exactly the shape the
    // option-aborts derivation (`inject_arithmetic_aborts`) produces — a
    // chained `match <option> with | some => .. | none => ..`. A stray
    // `let _ := Prover.ensures <Prop>` left inside such an arm then fails
    // to typecheck (`Prover.ensures` wants `Bool`). `map` covers all
    // variants, so spec calls are stripped wherever they appear.
    node.clone().map(&mut |n| match &n {
        IRNode::Call { function, .. }
            if Some(*function) == requires_id
                || Some(*function) == ensures_id
                || Some(*function) == asserts_id =>
        {
            IRNode::default()
        }
        _ => n,
    })
}

/// Build a spec body by wrapping the condition in the necessary Let bindings from the preamble
fn build_spec_body_with_preamble(cond: IRNode, preamble: Vec<(Vec<Rc<str>>, IRNode)>) -> IRNode {
    let mut body = cond;
    for (pattern, value) in preamble.into_iter().rev() {
        body = IRNode::Let {
            pattern,
            value: Box::new(value),
            body: Box::new(body),
        };
    }
    body
}
