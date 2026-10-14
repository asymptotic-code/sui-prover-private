//! Move auto-dereference normalization at the three semantic pipeline boundaries.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::analysis::free_vars::free_vars_of_expr;
use crate::ir::analysis::scope::{walk_typed_block_mut, TypedScope, TypedScopeMutVisitor};
use crate::ir::analysis::type_of::{substitute_type_params, type_of, TypeOfError};
use crate::ir::visit::{walk_stmt_default, Visitor};
use crate::ir::{Expr, FunId, Program, Stmt, Type, VarId};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum NormalizeMode {
    /// Pre-SSA: skip multi-definition values whose scope type is provisional.
    Early,
    /// Post-SSA: repair only aborting arithmetic needed by abort extraction.
    Aborting,
    /// Post-dejump: normalize values nested in newly synthesized Pack nodes.
    PackedValues,
    /// Post-cleanup: establish the exact render form for every remaining use.
    Full,
}

pub(super) fn run(
    program: &mut Program,
    mode: NormalizeMode,
) -> Result<(), Vec<(FunId, TypeOfError)>> {
    struct Normalizer<'a> {
        program: &'a Program,
        skip_vars: &'a BTreeSet<VarId>,
        mode: NormalizeMode,
    }

    impl Normalizer<'_> {
        fn touches_skip(&self, expr: &Expr) -> bool {
            !self.skip_vars.is_empty()
                && free_vars_of_expr(expr)
                    .iter()
                    .any(|var| self.skip_vars.contains(var))
        }

        fn wrap_if_ref(&self, expr: &mut Expr, scope: &TypedScope) {
            if self.touches_skip(expr) {
                return;
            }
            if let Ok(ty) = type_of(expr, scope, self.program) {
                if matches!(ty, Type::Reference(_) | Type::MutableRef { .. }) {
                    let inner = std::mem::replace(expr, Expr::Unit);
                    *expr = Expr::ReadRef(Box::new(inner));
                }
            }
        }

        fn normalize_to_expected(&self, expr: &mut Expr, expected: &Type, scope: &TypedScope) {
            if self.touches_skip(expr) {
                return;
            }

            let Ok(actual) = type_of(expr, scope, self.program) else {
                return;
            };
            match (&actual, expected) {
                (Type::Reference(inner) | Type::MutableRef { inner, .. }, expected)
                    if inner.as_ref() == expected =>
                {
                    let inner = std::mem::replace(expr, Expr::Unit);
                    *expr = Expr::ReadRef(Box::new(inner));
                }
                (Type::Tuple(actual_items), Type::Tuple(expected_items))
                    if actual_items.len() == expected_items.len() =>
                {
                    if let Expr::Tuple(items) = expr {
                        for (item, expected_item) in items.iter_mut().zip(expected_items) {
                            self.normalize_to_expected(item, expected_item, scope);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    impl TypedScopeMutVisitor for Normalizer<'_> {
        type Error = TypeOfError;

        fn visit_expr_mut(
            &mut self,
            expr: &mut Expr,
            scope: &TypedScope,
        ) -> Result<(), TypeOfError> {
            // Continuation extraction can turn a mixed pre-SSA local into a
            // value-typed parameter while retaining the bytecode ReadRef that
            // was attached to its reference-valued definition. Once the
            // operand is known to be a value, that ReadRef is precisely Move's
            // implicit dereference artifact and must disappear.
            if self.mode != NormalizeMode::Early {
                if let Expr::ReadRef(inner) = expr {
                    if type_of(inner, scope, self.program)
                        .is_ok_and(|ty| !matches!(ty, Type::Reference(_) | Type::MutableRef { .. }))
                    {
                        *expr = *std::mem::replace(inner, Box::new(Expr::Unit));
                        return Ok(());
                    }
                }
            }
            match expr {
                Expr::BinOp { op, lhs, rhs }
                    if matches!(self.mode, NormalizeMode::Early | NormalizeMode::Full)
                        || (self.mode == NormalizeMode::Aborting && op.can_abort_on_uint()) =>
                {
                    self.wrap_if_ref(lhs, scope);
                    self.wrap_if_ref(rhs, scope);
                }
                Expr::If { cond, .. } | Expr::While { cond, .. }
                    if matches!(self.mode, NormalizeMode::Early | NormalizeMode::Full) =>
                {
                    self.wrap_if_ref(cond, scope)
                }
                Expr::Pack {
                    struct_id,
                    type_args,
                    variant,
                    fields,
                } if self.mode != NormalizeMode::Aborting => {
                    let declared_fields =
                        self.program.structs.get(struct_id).and_then(|decl| {
                            match (variant, decl.variants.as_ref()) {
                                (Some(tag), Some(_)) => {
                                    decl.variant_by_tag(*tag).map(|variant| &variant.fields)
                                }
                                _ => Some(&decl.fields),
                            }
                        });
                    if let Some(declared_fields) = declared_fields {
                        if declared_fields.len() == fields.len() {
                            for (actual_expr, field) in
                                fields.iter_mut().zip(declared_fields.iter())
                            {
                                let expected = substitute_type_params(&field.field_type, type_args);
                                self.normalize_to_expected(actual_expr, &expected, scope);
                            }
                        }
                    }
                }
                _ => {}
            }
            Ok(())
        }
    }

    let mut failures = Vec::new();
    for fid in program.body_ids() {
        let skip_vars = match mode {
            NormalizeMode::Early => early_skip_vars(&program.functions[&fid].body),
            NormalizeMode::Aborting | NormalizeMode::PackedValues | NormalizeMode::Full => {
                BTreeSet::new()
            }
        };
        let scope = program.functions[&fid]
            .signature
            .params
            .iter()
            .map(|param| (param.var.clone(), param.ty.clone()))
            .collect();
        let mut candidate = program.functions[&fid].body.clone();
        let result = {
            let mut normalizer = Normalizer {
                program,
                skip_vars: &skip_vars,
                mode,
            };
            walk_typed_block_mut(&mut normalizer, &mut candidate, scope, program)
        };
        match result {
            Ok(()) => program.functions.get_mut(&fid).unwrap().body = candidate,
            Err(_) if mode == NormalizeMode::Early => {}
            Err(error) => failures.push((fid, error)),
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures)
    }
}

pub(super) fn early_skip_vars(body: &crate::ir::Block) -> BTreeSet<VarId> {
    #[derive(Default)]
    struct Collect {
        counts: BTreeMap<VarId, u32>,
        edges: Vec<(Vec<VarId>, BTreeSet<VarId>)>,
    }

    impl Visitor for Collect {
        fn visit_stmt(&mut self, stmt: &Stmt) {
            if let Stmt::Let { pattern, value } = stmt {
                let binders: Vec<VarId> = pattern.iter().flatten().cloned().collect();
                for var in &binders {
                    *self.counts.entry(var.clone()).or_insert(0) += 1;
                }
                if !binders.is_empty() {
                    self.edges.push((binders, free_vars_of_expr(value)));
                }
            }
            walk_stmt_default(self, stmt);
        }
    }

    let mut collected = Collect::default();
    collected.visit_block(body);

    let mut skip: BTreeSet<VarId> = collected
        .counts
        .into_iter()
        .filter(|(_, count)| *count > 1)
        .map(|(var, _)| var)
        .collect();

    loop {
        let mut changed = false;
        for (binders, free_vars) in &collected.edges {
            if free_vars.iter().any(|var| skip.contains(var)) {
                for binder in binders {
                    changed |= skip.insert(binder.clone());
                }
            }
        }
        if !changed {
            return skip;
        }
    }
}

#[cfg(test)]
pub(super) mod test_support {
    use crate::ir::{
        BinOp, Block, BlockTail, Effects, Expr, Function, FunctionKind, Module, Param, Program,
        Signature, Stmt, Type, VarId,
    };

    fn u256_ref() -> Type {
        Type::Reference(Box::new(Type::UInt(256)))
    }

    fn u256(n: u64) -> Expr {
        Expr::Const(crate::ir::Const::UInt {
            bits: 256,
            value: ethnum::U256::from(n),
        })
    }

    fn insert_ref_native(program: &mut Program, fid: crate::ir::FunId) {
        program.natives.decls.insert(
            fid,
            crate::ir::NativeDecl {
                module: 0,
                name: "g".to_string(),
                signature: Signature {
                    type_params: vec![],
                    params: vec![],
                    return_type: u256_ref(),
                },
                effects: Effects::PURE,
                explicit_pure: true,
                is_framework: false,
                spec_target: None,
                user_native: None,
            },
        );
    }

    pub(in crate::stage_02_ir_cfg) fn let1(name: &str, value: Expr) -> Stmt {
        Stmt::Let {
            pattern: vec![Some(VarId::from(name))],
            value,
        }
    }

    pub(in crate::stage_02_ir_cfg) fn multi_def_cascade_program() -> Program {
        let mut program = Program::default();
        program.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: vec![],
                is_native: false,
            },
        );
        insert_ref_native(&mut program, 1);

        let g_call = || Expr::Call {
            fun: 1,
            type_args: vec![],
            args: vec![],
        };
        let body = Block {
            stmts: vec![
                let1("x", g_call()),
                Stmt::Eval(Expr::If {
                    cond: Box::new(Expr::Var(VarId::from("cond"))),
                    then_branch: Box::new(Block {
                        stmts: vec![let1("x", u256(7))],
                        tail: BlockTail::Value(Expr::Unit),
                    }),
                    else_branch: Box::new(Block {
                        stmts: vec![],
                        tail: BlockTail::Value(Expr::Unit),
                    }),
                }),
                let1(
                    "cmp",
                    Expr::BinOp {
                        op: BinOp::Lt,
                        lhs: Box::new(Expr::Var(VarId::from("x"))),
                        rhs: Box::new(Expr::Var(VarId::from("yref"))),
                    },
                ),
                let1(
                    "sub",
                    Expr::BinOp {
                        op: BinOp::Sub,
                        lhs: Box::new(Expr::Var(VarId::from("x"))),
                        rhs: Box::new(Expr::Var(VarId::from("k"))),
                    },
                ),
                let1(
                    "prod",
                    Expr::BinOp {
                        op: BinOp::Mul,
                        lhs: Box::new(Expr::Var(VarId::from("sub"))),
                        rhs: Box::new(Expr::Var(VarId::from("m"))),
                    },
                ),
            ],
            tail: BlockTail::Value(Expr::Var(VarId::from("prod"))),
        };
        let param = |name: &str, ty: Type| Param {
            name: name.to_string(),
            var: VarId::from(name),
            ty,
        };
        program.functions.insert(
            0,
            Function {
                module: 0,
                name: "f".to_string(),
                signature: Signature {
                    type_params: vec![],
                    params: vec![
                        param("cond", Type::Bool),
                        param("yref", u256_ref()),
                        param("k", Type::UInt(256)),
                        param("m", Type::UInt(256)),
                    ],
                    return_type: Type::UInt(256),
                },
                body,
                kind: FunctionKind::Source,
                effects: Effects::PURE,
                explicit_pure: false,
            },
        );
        program
    }
}

#[cfg(test)]
mod tests {
    use super::test_support::{let1, multi_def_cascade_program};
    use super::*;
    use crate::ir::invariants::{Invariant, Stage};
    use crate::ir::{
        BinOp, Block, BlockTail, Effects, Expr, Field, Function, FunctionKind, Module, Param,
        Program, Signature, Stmt, Struct, Type, VarId, Variant,
    };

    #[test]
    fn aborting_repairs_arithmetic_and_defers_compatible_comparisons() {
        let mut program = Program::default();
        program.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: vec![],
                is_native: false,
            },
        );
        for (fid, op, return_type) in [(0, BinOp::Eq, Type::Bool), (1, BinOp::Sub, Type::UInt(64))]
        {
            program.functions.insert(
                fid,
                Function {
                    module: 0,
                    name: format!("f{fid}"),
                    signature: Signature {
                        type_params: vec![],
                        params: vec![
                            Param {
                                name: "lhs".to_string(),
                                var: VarId::from("lhs"),
                                ty: Type::Reference(Box::new(Type::UInt(64))),
                            },
                            Param {
                                name: "rhs".to_string(),
                                var: VarId::from("rhs"),
                                ty: Type::UInt(64),
                            },
                        ],
                        return_type,
                    },
                    body: Block {
                        stmts: vec![Stmt::Let {
                            pattern: vec![Some(VarId::from("cmp"))],
                            value: Expr::BinOp {
                                op,
                                lhs: Box::new(Expr::Var(VarId::from("lhs"))),
                                rhs: Box::new(Expr::Var(VarId::from("rhs"))),
                            },
                        }],
                        tail: BlockTail::Value(Expr::Var(VarId::from("cmp"))),
                    },
                    kind: FunctionKind::Source,
                    effects: Effects::PURE,
                    explicit_pure: false,
                },
            );
        }

        run(&mut program, NormalizeMode::Aborting).unwrap();

        fn lhs(program: &Program, fid: crate::ir::FunId) -> &Expr {
            let Stmt::Let {
                value: Expr::BinOp { lhs, .. },
                ..
            } = &program.functions[&fid].body.stmts[0]
            else {
                panic!("expected binop let")
            };
            lhs.as_ref()
        }
        assert!(matches!(lhs(&program, 0), Expr::Var(_)));
        assert!(matches!(lhs(&program, 1), Expr::ReadRef(_)));

        crate::ir::invariants::verify_precondition(Stage::S10BoundedNat, &program).unwrap();
        crate::stage_10_bounded_nat::run(&mut program).unwrap();

        let violations = crate::ir::invariants::baseline::BinOpOperandTypesAgree
            .check(&program)
            .expect_err("exact agreement is established only by final normalization");
        assert!(violations
            .iter()
            .any(|violation| violation.invariant == "binop-operand-types-agree"));

        run(&mut program, NormalizeMode::Full).unwrap();
        crate::stage_10_bounded_nat::run(&mut program).unwrap();
        crate::ir::invariants::baseline::BinOpOperandTypesAgree
            .check(&program)
            .unwrap();
    }

    #[test]
    fn early_wraps_single_definition_reference_operand() {
        let ownership_ty = Type::Struct {
            struct_id: 36,
            type_args: vec![],
        };
        let mut program = Program::default();
        program.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: vec![],
                is_native: false,
            },
        );
        program.functions.insert(
            0,
            Function {
                module: 0,
                name: "f".to_string(),
                signature: Signature {
                    type_params: vec![],
                    params: vec![
                        Param {
                            name: "ownership_ref".to_string(),
                            var: VarId::from("ownership_ref"),
                            ty: Type::Reference(Box::new(ownership_ty.clone())),
                        },
                        Param {
                            name: "ownership".to_string(),
                            var: VarId::from("ownership"),
                            ty: ownership_ty,
                        },
                    ],
                    return_type: Type::Bool,
                },
                body: Block {
                    stmts: vec![Stmt::Let {
                        pattern: vec![Some(VarId::from("cmp"))],
                        value: Expr::BinOp {
                            op: BinOp::Eq,
                            lhs: Box::new(Expr::Var(VarId::from("ownership_ref"))),
                            rhs: Box::new(Expr::Var(VarId::from("ownership"))),
                        },
                    }],
                    tail: BlockTail::Value(Expr::Var(VarId::from("cmp"))),
                },
                kind: FunctionKind::Source,
                effects: Effects::PURE,
                explicit_pure: false,
            },
        );

        run(&mut program, NormalizeMode::Early).unwrap();

        let Stmt::Let { value, .. } = &program.functions[&0].body.stmts[0] else {
            panic!("expected let");
        };
        let Expr::BinOp { lhs, rhs, .. } = value else {
            panic!("expected binop");
        };
        assert!(
            matches!(lhs.as_ref(), Expr::ReadRef(inner) if matches!(inner.as_ref(), Expr::Var(v) if v.as_ref() == "ownership_ref"))
        );
        assert!(matches!(rhs.as_ref(), Expr::Var(v) if v.as_ref() == "ownership"));
    }

    #[test]
    fn resolves_pack_fields_by_non_dense_variant_tag() {
        let mut program = Program::default();
        program.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: vec![],
                is_native: false,
            },
        );
        program.structs.insert(
            0,
            Struct {
                module_id: 0,
                name: "E".to_string(),
                qualified_name: "p::m::E".to_string(),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: Some(vec![Variant {
                    name: "Value".to_string(),
                    tag: 9,
                    fields: vec![Field {
                        name: "value".to_string(),
                        field_type: Type::UInt(64),
                    }],
                }]),
                is_native: false,
            },
        );
        program.functions.insert(
            0,
            Function {
                module: 0,
                name: "f".to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: vec![Param {
                        name: "value".to_string(),
                        var: "value".into(),
                        ty: Type::Reference(Box::new(Type::UInt(64))),
                    }],
                    return_type: Type::Struct {
                        struct_id: 0,
                        type_args: Vec::new(),
                    },
                },
                body: Block::just(Expr::Pack {
                    struct_id: 0,
                    type_args: Vec::new(),
                    variant: Some(9),
                    fields: vec![Expr::Var("value".into())],
                }),
                kind: FunctionKind::Source,
                effects: Effects::PURE,
                explicit_pure: false,
            },
        );

        run(&mut program, NormalizeMode::Full).unwrap();

        let BlockTail::Value(Expr::Pack { fields, .. }) = &program.functions[&0].body.tail else {
            panic!("expected enum Pack tail")
        };
        assert!(matches!(fields.as_slice(), [Expr::ReadRef(_)]));
    }

    #[test]
    fn full_normalizes_references_nested_in_packed_tuple_fields() {
        let tuple_ty = Type::Tuple(vec![Type::UInt(64), Type::UInt(64)]);
        let mut program = Program::default();
        program.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: vec![],
                is_native: false,
            },
        );
        program.structs.insert(
            0,
            Struct {
                module_id: 0,
                name: "LoopState".to_string(),
                qualified_name: "p::m::LoopState".to_string(),
                type_params: vec![],
                fields: vec![Field {
                    name: "state".to_string(),
                    field_type: tuple_ty,
                }],
                variants: None,
                is_native: false,
            },
        );
        program.functions.insert(
            0,
            Function {
                module: 0,
                name: "f".to_string(),
                signature: Signature {
                    type_params: vec![],
                    params: vec![
                        Param {
                            name: "plain".to_string(),
                            var: "plain".into(),
                            ty: Type::UInt(64),
                        },
                        Param {
                            name: "borrowed".to_string(),
                            var: "borrowed".into(),
                            ty: Type::Reference(Box::new(Type::UInt(64))),
                        },
                    ],
                    return_type: Type::Struct {
                        struct_id: 0,
                        type_args: vec![],
                    },
                },
                body: Block::just(Expr::Pack {
                    struct_id: 0,
                    type_args: vec![],
                    variant: None,
                    fields: vec![Expr::Tuple(vec![
                        Expr::Var("plain".into()),
                        Expr::Var("borrowed".into()),
                    ])],
                }),
                kind: FunctionKind::Source,
                effects: Effects::PURE,
                explicit_pure: false,
            },
        );

        run(&mut program, NormalizeMode::Full).unwrap();

        let BlockTail::Value(Expr::Pack { fields, .. }) = &program.functions[&0].body.tail else {
            panic!("expected packed loop state")
        };
        let [Expr::Tuple(items)] = fields.as_slice() else {
            panic!("expected tuple field")
        };
        assert!(matches!(items[0], Expr::Var(_)));
        assert!(matches!(items[1], Expr::ReadRef(_)));
    }

    #[test]
    fn early_skip_seeds_multi_definitions_and_taints_derived_values() {
        let program = multi_def_cascade_program();
        let set = early_skip_vars(&program.functions[&0].body);

        for var in ["x", "cmp", "sub", "prod"] {
            assert!(set.contains(&VarId::from(var)), "missing tainted `{var}`");
        }
    }

    #[test]
    fn early_skip_reaches_into_while_body() {
        let inner_if = Expr::If {
            cond: Box::new(Expr::Var(VarId::from("c"))),
            then_branch: Box::new(Block {
                stmts: vec![let1(
                    "t9",
                    Expr::Const(crate::ir::Const::UInt {
                        bits: 256,
                        value: ethnum::U256::ZERO,
                    }),
                )],
                tail: BlockTail::Value(Expr::Unit),
            }),
            else_branch: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Value(Expr::Unit),
            }),
        };
        let body = Block {
            stmts: vec![Stmt::Eval(Expr::While {
                header: Box::new(Block::just(Expr::Unit)),
                cond: Box::new(Expr::Var(VarId::from("g"))),
                body: Box::new(Block {
                    stmts: vec![
                        let1(
                            "t9",
                            Expr::Const(crate::ir::Const::UInt {
                                bits: 256,
                                value: ethnum::U256::ZERO,
                            }),
                        ),
                        Stmt::Eval(inner_if),
                    ],
                    tail: BlockTail::Value(Expr::Unit),
                }),
                iter_locals: vec![],
                header_exit_locals: vec![],
                live_out: vec![],
            })],
            tail: BlockTail::Value(Expr::Unit),
        };

        assert!(early_skip_vars(&body).contains(&VarId::from("t9")));
    }

    #[test]
    fn full_wraps_reference_while_condition() {
        let mut program = Program::default();
        program.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: vec![],
                is_native: false,
            },
        );
        program.functions.insert(
            0,
            Function {
                module: 0,
                name: "f".to_string(),
                signature: Signature {
                    type_params: vec![],
                    params: vec![Param {
                        name: "cond".to_string(),
                        var: VarId::from("cond"),
                        ty: Type::Reference(Box::new(Type::Bool)),
                    }],
                    return_type: Type::Unit,
                },
                body: Block {
                    stmts: vec![Stmt::Eval(Expr::While {
                        header: Box::new(Block::just(Expr::Unit)),
                        cond: Box::new(Expr::Var(VarId::from("cond"))),
                        body: Box::new(Block::just(Expr::Unit)),
                        iter_locals: vec![],
                        header_exit_locals: vec![],
                        live_out: vec![],
                    })],
                    tail: BlockTail::Value(Expr::Unit),
                },
                kind: FunctionKind::Source,
                effects: Effects::PURE,
                explicit_pure: false,
            },
        );

        run(&mut program, NormalizeMode::Full).unwrap();

        let Stmt::Eval(Expr::While { cond, .. }) = &program.functions[&0].body.stmts[0] else {
            panic!("expected while")
        };
        assert!(matches!(cond.as_ref(), Expr::ReadRef(_)));
    }

    #[test]
    fn early_skips_multi_def_operand_but_wraps_single_def_reference() {
        let mut program = multi_def_cascade_program();
        run(&mut program, NormalizeMode::Early).unwrap();

        let Stmt::Let { value, .. } = &program.functions[&0].body.stmts[2] else {
            panic!("expected `let cmp` at index 2");
        };
        let Expr::BinOp { lhs, rhs, .. } = value else {
            panic!("expected binop");
        };
        assert!(matches!(lhs.as_ref(), Expr::Var(v) if v.as_ref() == "x"));
        assert!(
            matches!(rhs.as_ref(), Expr::ReadRef(inner) if matches!(inner.as_ref(), Expr::Var(v) if v.as_ref() == "yref"))
        );

        let Stmt::Let { value, .. } = &program.functions[&0].body.stmts[4] else {
            panic!("expected `let prod` at index 4");
        };
        let Expr::BinOp { lhs, .. } = value else {
            panic!("expected binop");
        };
        assert!(matches!(lhs.as_ref(), Expr::Var(v) if v.as_ref() == "sub"));
    }

    #[test]
    fn full_wraps_multi_def_operand() {
        let mut program = multi_def_cascade_program();
        run(&mut program, NormalizeMode::Full).unwrap();

        let Stmt::Let { value, .. } = &program.functions[&0].body.stmts[2] else {
            panic!("expected `let cmp` at index 2");
        };
        let Expr::BinOp { lhs, .. } = value else {
            panic!("expected binop");
        };
        assert!(
            matches!(lhs.as_ref(), Expr::ReadRef(inner) if matches!(inner.as_ref(), Expr::Var(v) if v.as_ref() == "x"))
        );
    }

    #[test]
    fn scope_failure_preserves_the_exact_body() {
        let mut program = Program::default();
        program.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: vec![],
                is_native: false,
            },
        );
        program.functions.insert(
            0,
            Function {
                module: 0,
                name: "normalization_failure".to_string(),
                signature: Signature {
                    type_params: vec![],
                    params: vec![
                        Param {
                            name: "r".to_string(),
                            var: VarId::from("r"),
                            ty: Type::Reference(Box::new(Type::UInt(64))),
                        },
                        Param {
                            name: "v".to_string(),
                            var: VarId::from("v"),
                            ty: Type::UInt(64),
                        },
                    ],
                    return_type: Type::Unit,
                },
                body: Block {
                    stmts: vec![
                        let1(
                            "cmp",
                            Expr::BinOp {
                                op: BinOp::Eq,
                                lhs: Box::new(Expr::Var(VarId::from("r"))),
                                rhs: Box::new(Expr::Var(VarId::from("v"))),
                            },
                        ),
                        Stmt::Let {
                            pattern: vec![Some(VarId::from("a")), Some(VarId::from("b"))],
                            value: Expr::Const(crate::ir::Const::UInt {
                                bits: 64,
                                value: ethnum::U256::ZERO,
                            }),
                        },
                    ],
                    tail: BlockTail::Value(Expr::Unit),
                },
                kind: FunctionKind::Source,
                effects: Effects::PURE,
                explicit_pure: false,
            },
        );
        let original = program.functions[&0].body.clone();

        let mut early = program.clone();
        run(&mut early, NormalizeMode::Early).unwrap();
        assert_eq!(early.functions[&0].body, original);

        let failures = run(&mut program, NormalizeMode::Full).unwrap_err();
        assert_eq!(failures.len(), 1);
        assert_eq!(failures[0].0, 0);
        assert!(matches!(
            &failures[0].1,
            TypeOfError::MalformedAccess { .. }
        ));
        assert_eq!(program.functions[&0].body, original);
    }
}
