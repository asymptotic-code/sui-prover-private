//! Lower first-class globals into explicit hidden function parameters.
//!
//! This pass is the lifecycle boundary between frontend-facing
//! [`Expr::BorrowGlobal`] / [`BorrowNode::GlobalRoot`] nodes and the existing
//! mutable-reference pipeline. It must run before stage 3. For every function,
//! the pass computes the transitive set of globals used by its body or callees,
//! appends one hidden parameter per global in `GlobalId` order, threads those
//! arguments through direct calls, and replaces the global nodes with ordinary
//! parameter references.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::visit::{walk_expr_default, walk_expr_mut_try, TryMutVisitor, Visitor};
use crate::ir::{BorrowNode, Expr, FunId, FunctionGlobalBinding, GlobalId, Param, Program, VarId};

/// Reserved base for generated hidden global parameters.
pub const THREADED_GLOBAL_PARAM_PREFIX: &str = "__c2lean_global_";

/// Failure from [`thread_globals`]. Unknown/readonly/already-threaded input is
/// rejected before mutation; the remaining variants are fail-closed internal
/// consistency checks on the computed rewrite plan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ThreadGlobalsError {
    /// Executable global nodes are a trusted frontend boundary. The frontend
    /// must attest that its schema/identity and borrow/exclusivity certificates
    /// cover them before this pass turns them into ordinary references.
    MissingExternalGlobalBorrowCertification,
    UnknownGlobal {
        function: FunId,
        global: GlobalId,
    },
    ImmutableGlobalWrite {
        function: FunId,
        global: GlobalId,
    },
    /// A program with existing threading metadata cannot be incrementally
    /// re-threaded with newly introduced frontend global nodes.
    AlreadyThreaded,
    MissingCallerGlobal {
        caller: FunId,
        callee: FunId,
        global: GlobalId,
    },
    ResidualGlobal {
        function: FunId,
        global: GlobalId,
    },
}

#[derive(Default)]
struct Facts {
    globals: BTreeSet<GlobalId>,
    global_roots: BTreeSet<GlobalId>,
    callees: BTreeSet<FunId>,
}

impl Visitor for Facts {
    fn visit_global(&mut self, global: GlobalId) {
        self.globals.insert(global);
    }

    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Call { fun, .. } => {
                self.callees.insert(*fun);
            }
            Expr::WriteBack {
                node: BorrowNode::GlobalRoot(global),
                ..
            }
            | Expr::IsParent {
                node: BorrowNode::GlobalRoot(global),
                ..
            } => {
                self.global_roots.insert(*global);
            }
            _ => {}
        }
        walk_expr_default(self, expr);
    }
}

#[derive(Default)]
struct UsedNames(BTreeSet<String>);

impl Visitor for UsedNames {
    fn visit_var(&mut self, var: &VarId) {
        self.0.insert(var.to_string());
    }

    fn visit_expr(&mut self, expr: &Expr) {
        // Generic VarId walking deliberately treats `live_out` as stage-5
        // metadata. Generated hidden parameters still must avoid those names,
        // because both names become ordinary binders during loop extraction.
        if let Expr::While { live_out, .. } = expr {
            for (inside, outside) in live_out {
                self.visit_var(inside);
                self.visit_var(outside);
            }
        }
        walk_expr_default(self, expr);
    }
}

fn fresh_global_var(global: GlobalId, used: &mut BTreeSet<String>) -> VarId {
    let base = format!("{THREADED_GLOBAL_PARAM_PREFIX}{global}");
    let mut candidate = base.clone();
    let mut suffix = 0usize;
    while used.contains(&candidate) {
        suffix = suffix
            .checked_add(1)
            .expect("thread_globals: generated-name suffix overflowed");
        candidate = format!("{base}_{suffix}");
    }
    used.insert(candidate.clone());
    candidate.into()
}

struct Rewriter<'a> {
    caller: FunId,
    caller_vars: &'a BTreeMap<GlobalId, VarId>,
    function_globals: &'a BTreeMap<FunId, Vec<FunctionGlobalBinding>>,
}

impl TryMutVisitor for Rewriter<'_> {
    type Error = ThreadGlobalsError;

    fn visit_expr_mut(&mut self, expr: &mut Expr) -> Result<(), Self::Error> {
        match expr {
            Expr::BorrowGlobal(global) => {
                let var = self.caller_vars.get(global).cloned().ok_or(
                    ThreadGlobalsError::MissingCallerGlobal {
                        caller: self.caller,
                        callee: self.caller,
                        global: *global,
                    },
                )?;
                *expr = Expr::Var(var);
                Ok(())
            }
            Expr::WriteBack { node, .. } | Expr::IsParent { node, .. } => {
                if let BorrowNode::GlobalRoot(global) = node {
                    let var = self.caller_vars.get(global).cloned().ok_or(
                        ThreadGlobalsError::MissingCallerGlobal {
                            caller: self.caller,
                            callee: self.caller,
                            global: *global,
                        },
                    )?;
                    *node = BorrowNode::Reference(var);
                }
                walk_expr_mut_try(self, expr)
            }
            Expr::Call { fun, args, .. } => {
                for arg in args.iter_mut() {
                    self.visit_expr_mut(arg)?;
                }
                if let Some(globals) = self.function_globals.get(fun) {
                    for binding in globals {
                        let var = self.caller_vars.get(&binding.global).cloned().ok_or(
                            ThreadGlobalsError::MissingCallerGlobal {
                                caller: self.caller,
                                callee: *fun,
                                global: binding.global,
                            },
                        )?;
                        args.push(Expr::Var(var));
                    }
                }
                Ok(())
            }
            _ => walk_expr_mut_try(self, expr),
        }
    }
}

/// Return the first executable global node in deterministic function/walk
/// order. Stage 3 uses this to fail closed if the lifecycle boundary was
/// skipped.
pub fn first_residual_global(program: &Program) -> Option<(FunId, GlobalId)> {
    for (&fid, function) in &program.functions {
        #[derive(Default)]
        struct First(Option<GlobalId>);
        impl Visitor for First {
            fn visit_global(&mut self, global: GlobalId) {
                if self.0.is_none() {
                    self.0 = Some(global);
                }
            }
        }
        let mut first = First::default();
        first.visit_block(&function.body);
        if let Some(global) = first.0 {
            return Some((fid, global));
        }
    }
    None
}

/// Assert the post-threading lifecycle invariant: executable bodies contain
/// no [`Expr::BorrowGlobal`] or [`BorrowNode::GlobalRoot`] references.
pub fn check_globals_lowered(program: &Program) -> Result<(), ThreadGlobalsError> {
    match first_residual_global(program) {
        Some((function, global)) => Err(ThreadGlobalsError::ResidualGlobal { function, global }),
        None => Ok(()),
    }
}

/// Thread all directly and transitively used globals through translated
/// functions. Global and function iteration is `BTreeMap`/`BTreeSet` ordered,
/// so identical input produces identical parameter and argument order even for
/// recursive call graphs.
pub fn thread_globals(program: &mut Program) -> Result<(), ThreadGlobalsError> {
    let mut facts_by_function: BTreeMap<FunId, Facts> = BTreeMap::new();
    let mut has_frontend_nodes = false;

    for (&fid, function) in &program.functions {
        let mut facts = Facts::default();
        facts.visit_block(&function.body);
        has_frontend_nodes |= !facts.globals.is_empty();

        for &global in &facts.globals {
            if !program.globals.contains_key(&global) {
                return Err(ThreadGlobalsError::UnknownGlobal {
                    function: fid,
                    global,
                });
            }
        }
        for &global in &facts.global_roots {
            let decl = &program.globals[&global];
            if !decl.mutable {
                return Err(ThreadGlobalsError::ImmutableGlobalWrite {
                    function: fid,
                    global,
                });
            }
        }
        facts_by_function.insert(fid, facts);
    }

    if !has_frontend_nodes {
        return Ok(());
    }
    if !program.external_global_borrows_certified {
        return Err(ThreadGlobalsError::MissingExternalGlobalBorrowCertification);
    }
    if !program.function_globals.is_empty() {
        return Err(ThreadGlobalsError::AlreadyThreaded);
    }

    let mut transitive: BTreeMap<FunId, BTreeSet<GlobalId>> = facts_by_function
        .iter()
        .map(|(&fid, facts)| (fid, facts.globals.clone()))
        .collect();

    loop {
        let snapshot = transitive.clone();
        let mut changed = false;
        for (&fid, facts) in &facts_by_function {
            let globals = transitive
                .get_mut(&fid)
                .expect("every translated function has a transitive-use entry");
            for callee in &facts.callees {
                if let Some(callee_globals) = snapshot.get(callee) {
                    let old_len = globals.len();
                    globals.extend(callee_globals.iter().copied());
                    changed |= globals.len() != old_len;
                }
            }
        }
        if !changed {
            break;
        }
    }

    let function_global_ids: BTreeMap<FunId, Vec<GlobalId>> = transitive
        .into_iter()
        .filter_map(|(fid, globals)| {
            (!globals.is_empty()).then(|| (fid, globals.into_iter().collect()))
        })
        .collect();

    let mut hidden_vars: BTreeMap<FunId, BTreeMap<GlobalId, VarId>> = BTreeMap::new();
    let mut function_globals: BTreeMap<FunId, Vec<FunctionGlobalBinding>> = BTreeMap::new();
    for (&fid, globals) in &function_global_ids {
        let function = program
            .functions
            .get_mut(&fid)
            .expect("threaded function is translated");
        let mut used = UsedNames::default();
        used.visit_block(&function.body);
        for param in &function.signature.params {
            used.0.insert(param.var.to_string());
            used.0.insert(param.name.clone());
        }

        let mut vars = BTreeMap::new();
        let mut bindings = Vec::with_capacity(globals.len());
        for &global_id in globals {
            let var = fresh_global_var(global_id, &mut used.0);
            let decl = &program.globals[&global_id];
            let parameter_index = function.signature.params.len();
            function.signature.params.push(Param {
                name: var.to_string(),
                var: var.clone(),
                ty: decl.threaded_param_type(),
            });
            vars.insert(global_id, var.clone());
            bindings.push(FunctionGlobalBinding {
                global: global_id,
                parameter_index,
            });
        }
        hidden_vars.insert(fid, vars);
        function_globals.insert(fid, bindings);
    }

    // Publish metadata before rewriting calls so the rewriter sees the exact
    // appended-parameter order for every callee.
    program.function_globals = function_globals;
    let function_globals = &program.function_globals;
    for (&fid, vars) in &hidden_vars {
        let function = program
            .functions
            .get_mut(&fid)
            .expect("threaded function is translated");
        let mut rewriter = Rewriter {
            caller: fid,
            caller_vars: vars,
            function_globals,
        };
        rewriter.visit_block_mut(&mut function.body)?;
    }

    check_globals_lowered(program)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{
        Block, BlockTail, BorrowEdge, Effects, Function, FunctionKind, Global, Module, Signature,
        Stmt, Type,
    };

    fn module() -> Module {
        Module {
            name: "m".into(),
            package_name: "c".into(),
            address: String::new(),
            required_imports: vec![],
            is_native: false,
        }
    }

    fn function(name: &str, body: Expr) -> Function {
        Function {
            module: 0,
            name: name.into(),
            signature: Signature {
                type_params: vec![],
                params: vec![],
                return_type: Type::Unit,
            },
            body: Block {
                stmts: vec![],
                tail: BlockTail::Value(body),
            },
            kind: FunctionKind::Source,
            effects: Effects::PURE,
            explicit_pure: false,
        }
    }

    fn program_with_globals() -> Program {
        let mut program = Program {
            external_global_borrows_certified: true,
            ..Program::default()
        };
        program.modules.insert(0, module());
        program.globals.insert(
            0,
            Global {
                module_id: 0,
                name: "counter".into(),
                ty: Type::UInt(32),
                mutable: true,
                definition: crate::ir::GlobalDefinition::BoundarySupplied,
            },
        );
        program.globals.insert(
            1,
            Global {
                module_id: 0,
                name: "limit".into(),
                ty: Type::UInt(32),
                mutable: false,
                definition: crate::ir::GlobalDefinition::BoundarySupplied,
            },
        );
        program
    }

    #[test]
    fn executable_global_nodes_require_external_borrow_certification() {
        let mut program = program_with_globals();
        program.external_global_borrows_certified = false;
        program
            .functions
            .insert(0, function("uncertified", Expr::BorrowGlobal(0)));
        let before = program.clone();

        assert_eq!(
            thread_globals(&mut program),
            Err(ThreadGlobalsError::MissingExternalGlobalBorrowCertification)
        );
        assert_eq!(program, before, "certification failure must be atomic");
    }

    #[test]
    fn programs_without_executable_global_nodes_need_no_certification() {
        let mut program = program_with_globals();
        program.external_global_borrows_certified = false;
        program.functions.insert(0, function("plain", Expr::Unit));

        thread_globals(&mut program).unwrap();

        assert!(program.function_globals.is_empty());
        assert!(program.functions[&0].signature.params.is_empty());
    }

    #[test]
    fn recursive_calls_receive_globals_but_tail_shape_requires_anf_before_stage3() {
        let mut program = program_with_globals();
        // f0 -> f1, while f1 recursively calls itself and reads global 0.
        program.functions.insert(
            0,
            function(
                "caller",
                Expr::Call {
                    fun: 1,
                    type_args: vec![],
                    args: vec![],
                },
            ),
        );
        program.functions.insert(
            1,
            Function {
                body: Block {
                    stmts: vec![Stmt::Eval(Expr::BorrowGlobal(0))],
                    tail: BlockTail::Value(Expr::Call {
                        fun: 1,
                        type_args: vec![],
                        args: vec![],
                    }),
                },
                ..function("recursive", Expr::Unit)
            },
        );

        thread_globals(&mut program).unwrap();

        assert_eq!(
            program.function_globals[&0]
                .iter()
                .map(|binding| binding.global)
                .collect::<Vec<_>>(),
            vec![0]
        );
        assert_eq!(
            program.function_globals[&1]
                .iter()
                .map(|binding| binding.global)
                .collect::<Vec<_>>(),
            vec![0]
        );
        for fid in [0, 1] {
            let param = program.functions[&fid].signature.params.last().unwrap();
            assert_eq!(param.ty, program.globals[&0].threaded_param_type());
        }
        let BlockTail::Value(Expr::Call { args, .. }) = &program.functions[&0].body.tail else {
            panic!("expected direct call");
        };
        assert!(matches!(args.as_slice(), [Expr::Var(_)]));
        let BlockTail::Value(Expr::Call { args, .. }) = &program.functions[&1].body.tail else {
            panic!("expected recursive call");
        };
        assert!(matches!(args.as_slice(), [Expr::Var(_)]));
        check_globals_lowered(&program).unwrap();

        // Global propagation is call-graph complete, including recursion, but
        // stage 3 v1 intentionally requires mutating calls to be A-normalized
        // into statement position so returned state has a binding site.
        assert_eq!(
            crate::stage_03_mut_to_let::run(&mut program),
            Err(crate::stage_03_mut_to_let::Stage3Error::CallInExpressionPosition { function: 0 })
        );
    }

    #[test]
    fn mutable_global_root_rewrites_to_hidden_reference() {
        let mut program = program_with_globals();
        program.functions.insert(
            0,
            function(
                "write",
                Expr::WriteBack {
                    node: BorrowNode::GlobalRoot(0),
                    edge: BorrowEdge::Direct,
                    child: "child".into(),
                    world: None,
                },
            ),
        );
        // The structural test does not run the base scope validator; child is
        // intentionally irrelevant to global-root lowering.
        thread_globals(&mut program).unwrap();
        let BlockTail::Value(Expr::WriteBack { node, .. }) = &program.functions[&0].body.tail
        else {
            panic!("expected writeback");
        };
        assert!(matches!(node, BorrowNode::Reference(_)));
    }

    #[test]
    fn mutable_global_flows_through_stage3_return_augmentation() {
        let mut program = program_with_globals();
        let mut f = function("store", Expr::Unit);
        f.body.stmts = vec![
            Stmt::Let {
                pattern: vec![Some("child".into())],
                value: Expr::BorrowGlobal(0),
            },
            Stmt::Eval(Expr::WriteRef {
                reference: Box::new(Expr::Var("child".into())),
                value: Box::new(Expr::Const(crate::ir::Const::UInt {
                    bits: 32,
                    value: 7u8.into(),
                })),
            }),
            Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::GlobalRoot(0),
                edge: BorrowEdge::Direct,
                child: "child".into(),
                world: None,
            }),
        ];
        program.functions.insert(0, f);

        thread_globals(&mut program).unwrap();
        crate::stage_03_mut_to_let::run(&mut program).unwrap();

        let hidden = program.functions[&0].signature.params.last().unwrap();
        assert!(matches!(hidden.ty, Type::MutableRef { .. }));
        assert_eq!(
            program.functions[&0].signature.return_type,
            Type::Tuple(vec![hidden.ty.clone()])
        );
        let BlockTail::Value(Expr::Tuple(values)) = &program.functions[&0].body.tail else {
            panic!("stage 3 should return the updated hidden global");
        };
        assert_eq!(values, &vec![Expr::Var(hidden.var.clone())]);
    }

    #[test]
    fn immutable_global_is_reference_and_rejects_writeback() {
        let mut read_program = program_with_globals();
        read_program
            .functions
            .insert(0, function("read", Expr::BorrowGlobal(1)));
        thread_globals(&mut read_program).unwrap();
        assert_eq!(
            read_program.functions[&0]
                .signature
                .params
                .last()
                .unwrap()
                .ty,
            Type::Reference(Box::new(Type::UInt(32)))
        );

        let mut write_program = program_with_globals();
        write_program.functions.insert(
            0,
            function(
                "bad_write",
                Expr::WriteBack {
                    node: BorrowNode::GlobalRoot(1),
                    edge: BorrowEdge::Direct,
                    child: "child".into(),
                    world: None,
                },
            ),
        );
        assert_eq!(
            thread_globals(&mut write_program),
            Err(ThreadGlobalsError::ImmutableGlobalWrite {
                function: 0,
                global: 1,
            })
        );
        assert!(write_program.function_globals.is_empty());
    }

    #[test]
    fn generated_names_avoid_existing_locals() {
        let mut program = program_with_globals();
        let mut f = function("collision", Expr::BorrowGlobal(0));
        f.signature.params.push(Param {
            name: "__c2lean_global_0".into(),
            var: "__c2lean_global_0".into(),
            ty: Type::UInt(8),
        });
        program.functions.insert(0, f);
        thread_globals(&mut program).unwrap();
        assert_eq!(
            program.functions[&0].signature.params.last().unwrap().name,
            "__c2lean_global_0_1"
        );
    }

    #[test]
    fn binding_index_survives_suffix_params_and_ssa_renaming() {
        let mut program = program_with_globals();
        let mut f = function("stable_binding", Expr::Unit);
        f.body.stmts.push(Stmt::Eval(Expr::BorrowGlobal(0)));
        program.functions.insert(0, f);

        thread_globals(&mut program).unwrap();
        crate::stage_03_mut_to_let::run(&mut program).unwrap();
        let binding = program.function_globals[&0][0].clone();
        assert_eq!(binding.parameter_index, 0);

        // Model a later World/ghost suffix before SSA alpha-renames every
        // parameter binder while preserving signature order.
        program
            .functions
            .get_mut(&0)
            .unwrap()
            .signature
            .params
            .push(Param {
                name: "later_world_or_ghost".into(),
                var: "later_world_or_ghost".into(),
                ty: Type::Unit,
            });
        crate::ir::validate::validate_program(&program).unwrap();
        let old_var = program.functions[&0].signature.params[binding.parameter_index]
            .var
            .clone();

        crate::stage_05_ssa::run(&mut program).unwrap();

        let binding_after = &program.function_globals[&0][0];
        assert_eq!(binding_after, &binding);
        let bound_param = &program.functions[&0].signature.params[binding_after.parameter_index];
        assert_ne!(
            bound_param.var, old_var,
            "SSA should exercise binder renaming"
        );
        assert_eq!(bound_param.ty, program.globals[&0].threaded_param_type());
        crate::ir::validate::validate_program(&program).unwrap();
    }
}
