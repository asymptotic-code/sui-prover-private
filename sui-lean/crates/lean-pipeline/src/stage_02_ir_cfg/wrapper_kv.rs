//! Fixed-point analysis of map-key types carried through user borrow wrappers.
//!
//! Each entry is the ordered sequence of `(K, V)` pairs used by map-style
//! borrows in a wrapper's transitive body. Every pass reads a snapshot so
//! module iteration order cannot affect propagation, and callee types are
//! instantiated in the caller's type-argument frame. The eight-pass bound is
//! deliberate: recursive wrapper cycles can grow ordered sequences forever;
//! acyclic chains deeper than eight edges remain unresolved at the outer end.

use move_model::model::GlobalEnv;
use move_stackless_bytecode::function_target_pipeline::{FunctionTargetsHolder, FunctionVariant};
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Operation};

use crate::ir::ProgramBuilder;

const MAX_PASSES: usize = 8;

pub(super) fn build(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    program: &mut ProgramBuilder,
) {
    for _ in 0..MAX_PASSES {
        let mut changed = false;
        let snapshot = program.user_wrapper_kvs().clone();
        for module in env.get_modules() {
            for function in module.get_functions() {
                if function.is_native() {
                    continue;
                }
                let Some(target) = targets.get_target_opt(&function, &FunctionVariant::Baseline)
                else {
                    continue;
                };
                let own_qid = (module.get_id(), function.get_id());
                let mut kvs = Vec::new();
                for bytecode in target.get_bytecode() {
                    let Bytecode::Call(_, _, Operation::Function(mid, fid, type_args), _, _) =
                        bytecode
                    else {
                        continue;
                    };
                    let callee_qid = (*mid, *fid);
                    let is_map_key_native = matches!(
                        super::translate_op::recognize_borrow_native(env, *mid, *fid),
                        Some(super::translate_op::BorrowNativeKind::MapKey),
                    );
                    let callee_module = env.get_module(*mid);
                    let callee = callee_module.get_function(*fid);
                    let is_dynamic_field = callee.is_well_known("dynamic_field::borrow_mut")
                        || callee.is_well_known("dynamic_object_field::borrow_mut");
                    if (is_map_key_native || is_dynamic_field) && type_args.len() >= 2 {
                        kvs.push((type_args[0].clone(), type_args[1].clone()));
                        continue;
                    }
                    if callee_qid != own_qid {
                        if let Some(inner_kvs) = snapshot.get(&callee_qid) {
                            for (key, value) in inner_kvs {
                                kvs.push((
                                    key.instantiate(type_args),
                                    value.instantiate(type_args),
                                ));
                            }
                        }
                    }
                }
                let previous = snapshot.get(&own_qid).cloned().unwrap_or_default();
                if kvs != previous {
                    changed = true;
                    if kvs.is_empty() {
                        program.user_wrapper_kvs_mut().remove(&own_qid);
                    } else {
                        program.user_wrapper_kvs_mut().insert(own_qid, kvs);
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use move_binary_format::file_format::basic_test_module;
    use move_model::{
        model::{FunId, GlobalEnv, QualifiedId},
        ty::{PrimitiveType, Type},
    };
    use move_stackless_bytecode::{
        function_target_pipeline::{FunctionHolderTarget, FunctionTargetsHolder, FunctionVariant},
        options::ProverOptions,
        package_targets::PackageTargets,
        stackless_bytecode::{AttrId, Bytecode, Operation},
        target_filter::TargetFilterOptions,
    };

    use super::*;

    type FunctionQid = QualifiedId<FunId>;
    type Call<'a> = (&'a str, &'a str, Vec<Type>);

    fn prim(primitive: PrimitiveType) -> Type {
        Type::Primitive(primitive)
    }

    fn fixture(
        functions: &[(&str, bool)],
        calls: &[Call<'_>],
    ) -> (
        GlobalEnv,
        FunctionTargetsHolder,
        BTreeMap<String, FunctionQid>,
    ) {
        let modules = functions
            .iter()
            .map(|(_, is_native)| {
                let mut module = basic_test_module();
                if *is_native {
                    module.function_defs[0].code = None;
                }
                module
            })
            .collect::<Vec<_>>();
        let env = move_model::run_bytecode_model_builder(&modules).expect("test model");
        let qids = functions
            .iter()
            .zip(env.get_modules())
            .map(|((name, _), module)| {
                let function = module.get_functions().next().expect("test function");
                ((*name).to_string(), function.get_qualified_id())
            })
            .collect::<BTreeMap<_, _>>();
        let package_targets =
            PackageTargets::new(&env, TargetFilterOptions::default(), false, None);
        let mut targets = FunctionTargetsHolder::new(
            ProverOptions::default(),
            &package_targets,
            FunctionHolderTarget::All,
        );
        for module in env.get_modules() {
            for function in module
                .get_functions()
                .filter(|function| !function.is_native())
            {
                targets.add_target(&function);
                targets
                    .get_data_mut(&function.get_qualified_id(), &FunctionVariant::Baseline)
                    .expect("baseline target")
                    .code
                    .clear();
            }
        }
        for (attr, (caller, callee, type_args)) in calls.iter().enumerate() {
            let caller = qids[*caller];
            let callee = qids[*callee];
            targets
                .get_data_mut(&caller, &FunctionVariant::Baseline)
                .expect("caller baseline target")
                .code
                .push(Bytecode::Call(
                    AttrId::new(attr),
                    Vec::new(),
                    Operation::Function(callee.module_id, callee.id, type_args.clone()),
                    Vec::new(),
                    None,
                ));
        }

        (env, targets, qids)
    }

    fn seed(
        program: &mut ProgramBuilder,
        qids: &BTreeMap<String, FunctionQid>,
        function: &str,
        kvs: Vec<(Type, Type)>,
    ) {
        let qid = qids[function];
        program
            .user_wrapper_kvs_mut()
            .insert((qid.module_id, qid.id), kvs);
    }

    fn kvs<'a>(
        program: &'a ProgramBuilder,
        qids: &BTreeMap<String, FunctionQid>,
        function: &str,
    ) -> Option<&'a Vec<(Type, Type)>> {
        let qid = qids[function];
        program.user_wrapper_kvs().get(&(qid.module_id, qid.id))
    }

    #[test]
    fn instantiates_generic_leaf_types_in_the_callers_frame() {
        let (env, targets, qids) = fixture(
            &[("wrapper", false), ("leaf", true)],
            &[(
                "wrapper",
                "leaf",
                vec![prim(PrimitiveType::U64), prim(PrimitiveType::Bool)],
            )],
        );
        let mut program = ProgramBuilder::new();
        seed(
            &mut program,
            &qids,
            "leaf",
            vec![(
                Type::TypeParameter(0),
                Type::Vector(Box::new(Type::TypeParameter(1))),
            )],
        );

        build(&env, &targets, &mut program);

        assert_eq!(
            kvs(&program, &qids, "wrapper"),
            Some(&vec![(
                prim(PrimitiveType::U64),
                Type::Vector(Box::new(prim(PrimitiveType::Bool))),
            )])
        );
    }

    #[test]
    fn resolves_transitive_wrappers_when_callers_precede_callees() {
        let (env, targets, qids) = fixture(
            &[("outer", false), ("middle", false), ("leaf", true)],
            &[
                (
                    "outer",
                    "middle",
                    vec![prim(PrimitiveType::Bool), prim(PrimitiveType::U64)],
                ),
                (
                    "middle",
                    "leaf",
                    vec![
                        Type::TypeParameter(1),
                        Type::Vector(Box::new(Type::TypeParameter(0))),
                    ],
                ),
            ],
        );
        let mut program = ProgramBuilder::new();
        seed(
            &mut program,
            &qids,
            "leaf",
            vec![(Type::TypeParameter(0), Type::TypeParameter(1))],
        );

        build(&env, &targets, &mut program);

        assert_eq!(
            kvs(&program, &qids, "middle"),
            Some(&vec![(
                Type::TypeParameter(1),
                Type::Vector(Box::new(Type::TypeParameter(0))),
            )])
        );
        assert_eq!(
            kvs(&program, &qids, "outer"),
            Some(&vec![(
                prim(PrimitiveType::U64),
                Type::Vector(Box::new(prim(PrimitiveType::Bool))),
            )])
        );
    }

    #[test]
    fn direct_recursion_does_not_duplicate_leaf_knowledge() {
        let (env, targets, qids) = fixture(
            &[("recursive", false), ("leaf", true)],
            &[
                ("recursive", "recursive", Vec::new()),
                ("recursive", "leaf", Vec::new()),
            ],
        );
        let expected = vec![(prim(PrimitiveType::U8), prim(PrimitiveType::Address))];
        let mut program = ProgramBuilder::new();
        seed(&mut program, &qids, "leaf", expected.clone());

        build(&env, &targets, &mut program);

        assert_eq!(kvs(&program, &qids, "recursive"), Some(&expected));
    }

    #[test]
    fn mutual_cycle_is_bounded_and_preserves_anchor_knowledge() {
        let (env, targets, qids) = fixture(
            &[("left", false), ("right", false), ("leaf", true)],
            &[
                ("left", "right", Vec::new()),
                ("right", "left", Vec::new()),
                ("right", "leaf", Vec::new()),
            ],
        );
        let pair = (prim(PrimitiveType::U8), prim(PrimitiveType::Bool));
        let mut program = ProgramBuilder::new();
        seed(&mut program, &qids, "leaf", vec![pair.clone()]);

        build(&env, &targets, &mut program);

        for function in ["left", "right"] {
            let actual = kvs(&program, &qids, function).expect("anchor reaches cycle");
            assert!(!actual.is_empty());
            assert!(actual.len() <= MAX_PASSES);
            assert!(actual.iter().all(|actual_pair| actual_pair == &pair));
        }
    }

    #[test]
    fn propagation_stops_after_eight_wrapper_edges() {
        let functions = [
            ("w0", false),
            ("w1", false),
            ("w2", false),
            ("w3", false),
            ("w4", false),
            ("w5", false),
            ("w6", false),
            ("w7", false),
            ("w8", false),
            ("leaf", true),
        ];
        let calls = vec![
            ("w0", "w1", Vec::new()),
            ("w1", "w2", Vec::new()),
            ("w2", "w3", Vec::new()),
            ("w3", "w4", Vec::new()),
            ("w4", "w5", Vec::new()),
            ("w5", "w6", Vec::new()),
            ("w6", "w7", Vec::new()),
            ("w7", "w8", Vec::new()),
            ("w8", "leaf", Vec::new()),
        ];
        let (env, targets, qids) = fixture(&functions, &calls);
        let expected = vec![(prim(PrimitiveType::U16), prim(PrimitiveType::U32))];
        let mut program = ProgramBuilder::new();
        seed(&mut program, &qids, "leaf", expected.clone());

        build(&env, &targets, &mut program);

        assert_eq!(kvs(&program, &qids, "w1"), Some(&expected));
        assert_eq!(kvs(&program, &qids, "w0"), None);
    }
}
