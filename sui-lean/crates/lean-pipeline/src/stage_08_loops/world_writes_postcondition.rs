use std::collections::BTreeSet;

use crate::ir::visit::{walk_expr_default, Visitor};
use crate::ir::{Expr, FunId, FunctionKind, Program};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MissingWorldWrite {
    pub function: FunId,
}

pub fn check(program: &Program) -> Result<(), Vec<MissingWorldWrite>> {
    let native_writers: BTreeSet<FunId> = program
        .natives
        .decls
        .iter()
        .filter(|(_, decl)| decl.effects.world_writes)
        .map(|(fid, _)| *fid)
        .collect();
    let known_callees: BTreeSet<FunId> = program
        .functions
        .keys()
        .chain(program.natives.decls.keys())
        .copied()
        .collect();
    let mut expected_writers: BTreeSet<FunId> = program
        .functions
        .iter()
        .filter(|(_, function)| participates_in_world_write_closure(function))
        .filter(|(_, function)| {
            function.effects.world_writes || body_has_direct_world_write(&function.body)
        })
        .map(|(fid, _)| *fid)
        .collect();

    loop {
        let mut changed = false;
        for (fid, function) in &program.functions {
            if expected_writers.contains(fid) || !participates_in_world_write_closure(function) {
                continue;
            }
            let calls_writer = body_callees(&function.body).into_iter().any(|callee| {
                expected_writers.contains(&callee)
                    || native_writers.contains(&callee)
                    || !known_callees.contains(&callee)
            });
            if calls_writer {
                expected_writers.insert(*fid);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let missing: Vec<MissingWorldWrite> = expected_writers
        .into_iter()
        .filter(|fid| !program.functions[fid].effects.world_writes)
        .map(|function| MissingWorldWrite { function })
        .collect();
    if missing.is_empty() {
        Ok(())
    } else {
        Err(missing)
    }
}

fn participates_in_world_write_closure(function: &crate::ir::Function) -> bool {
    !crate::ir::names::is_aborts_family_name(&function.name)
        && !matches!(
            function.kind,
            FunctionKind::Theorem { .. } | FunctionKind::Axiom { .. }
        )
}

fn body_has_direct_world_write(block: &crate::ir::Block) -> bool {
    struct Finder(bool);

    impl Visitor for Finder {
        fn visit_expr(&mut self, expr: &Expr) {
            if matches!(expr, Expr::WriteBack { world: Some(_), .. }) {
                self.0 = true;
            }
            walk_expr_default(self, expr);
        }
    }

    let mut finder = Finder(false);
    finder.visit_block(block);
    finder.0
}

fn body_callees(block: &crate::ir::Block) -> Vec<FunId> {
    struct Collector(Vec<FunId>);

    impl Visitor for Collector {
        fn visit_expr(&mut self, expr: &Expr) {
            if let Expr::Call { fun, .. } = expr {
                self.0.push(*fun);
            }
            walk_expr_default(self, expr);
        }
    }

    let mut collector = Collector(Vec::new());
    collector.visit_block(block);
    collector.0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::builder::{call, just};
    use crate::ir::natives::NativeDecl;
    use crate::ir::{Effects, Function, FunctionKind, Module, Signature, Type};

    fn function(name: &str, callee: FunId) -> Function {
        Function {
            module: 0,
            name: name.to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: Vec::new(),
                return_type: Type::Unit,
            },
            body: just(call(callee, Vec::new())),
            kind: FunctionKind::Source,
            effects: Effects::WORLD,
            explicit_pure: false,
        }
    }

    fn chain_program() -> Program {
        let mut program = Program::default();
        program.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        let mut writer_effects = Effects::WORLD;
        writer_effects.world_writes = true;
        program.natives.decls.insert(
            10,
            NativeDecl {
                module: 0,
                name: "write".to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: Type::Unit,
                },
                effects: writer_effects,
                explicit_pure: false,
                is_framework: true,
                spec_target: None,
                user_native: None,
            },
        );
        program.functions.insert(2, function("b", 10));
        program.functions.insert(1, function("a", 2));
        program
    }

    #[test]
    fn rejects_false_negative_transitive_world_write_bits() {
        let program = chain_program();
        let errors = check(&program).unwrap_err();
        assert_eq!(
            errors,
            vec![
                MissingWorldWrite { function: 1 },
                MissingWorldWrite { function: 2 }
            ]
        );
    }

    #[test]
    fn accepts_stage_8_propagated_world_write_closure() {
        let mut program = chain_program();
        super::super::run(&mut program);
        assert!(program.functions[&1].effects.world_writes);
        assert!(program.functions[&2].effects.world_writes);
        assert_eq!(check(&program), Ok(()));
    }

    #[test]
    fn ignores_stage_12_proof_obligations_added_after_stage_8() {
        let mut program = chain_program();
        super::super::run(&mut program);
        for (fid, kind) in [
            (
                3,
                FunctionKind::Theorem {
                    target: 1,
                    source: 1,
                },
            ),
            (
                4,
                FunctionKind::Axiom {
                    target: 1,
                    source: 1,
                    reason: crate::ir::TrustReason::NonProve,
                },
            ),
        ] {
            let mut obligation = function("obligation", 10);
            obligation.kind = kind;
            obligation.effects = Effects::PURE;
            program.functions.insert(fid, obligation);
        }

        assert_eq!(check(&program), Ok(()));
        assert!(!program.functions[&3].effects.world_writes);
        assert!(!program.functions[&4].effects.world_writes);
    }

    #[test]
    fn ignores_logical_abort_family_helpers() {
        let mut program = chain_program();
        super::super::run(&mut program);
        let mut abort_cont = function("source.aborts.cont_0", 10);
        abort_cont.kind = FunctionKind::Synthetic;
        abort_cont.effects = Effects::PURE;
        program.functions.insert(3, abort_cont);

        assert_eq!(check(&program), Ok(()));
        assert!(!program.functions[&3].effects.world_writes);
    }

    #[test]
    fn ordinary_synthetic_continuations_remain_in_the_write_closure() {
        let mut program = chain_program();
        let mut cont = function("source.cont_0", 10);
        cont.kind = FunctionKind::Synthetic;
        cont.effects = Effects::PURE;
        program.functions.insert(3, cont);

        assert_eq!(
            check(&program),
            Err(vec![
                MissingWorldWrite { function: 1 },
                MissingWorldWrite { function: 2 },
                MissingWorldWrite { function: 3 },
            ])
        );
    }

    #[test]
    fn rejects_false_negative_direct_world_writeback() {
        let mut program = chain_program();
        let mut direct = function("direct", 10);
        direct.body = just(crate::ir::builder::write_back(
            "parent",
            "child",
            Some("world"),
        ));
        program.functions.insert(3, direct);

        assert_eq!(
            check(&program),
            Err(vec![
                MissingWorldWrite { function: 1 },
                MissingWorldWrite { function: 2 },
                MissingWorldWrite { function: 3 },
            ])
        );
    }

    #[test]
    fn rejects_false_negative_unknown_callee() {
        let mut program = chain_program();
        program.functions.insert(3, function("unknown", 999));

        assert_eq!(
            check(&program),
            Err(vec![
                MissingWorldWrite { function: 1 },
                MissingWorldWrite { function: 2 },
                MissingWorldWrite { function: 3 },
            ])
        );
    }
}
