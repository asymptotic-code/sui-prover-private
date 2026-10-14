//! Render-output regressions for the 2026-05-tests-lake-cleanup
//! sweep. Each test pins one shape that needed a render-layer fix.

use crate::ir::{
    BinOp, Block, BlockTail, Expr, Field, FunId, Function, FunctionKind, MatchArm, Param,
    Signature, Stmt, Struct, Type, VarId,
};
use crate::render::render_program;

use super::fixtures::*;

fn render_program_in_loop_mode(
    program: &crate::ir::Program,
    mode: crate::render::loop_termination::LoopMode,
    registry: crate::render::loop_termination::LoopTerminationRegistry,
) -> String {
    let context = crate::render::context::RenderContext::new(
        program,
        crate::render::loop_termination::LoopRenderContext::new(mode, registry),
    );
    let mut writer = crate::render::writer::LeanWriter::new(String::new());
    crate::render::render_program_into_filtered(&context, None, &mut writer)
        .expect("render program in explicit loop mode");
    writer.into_inner()
}

#[test]
fn mismatched_loop_helper_multi_slot_let_fails_closed() {
    for helper_kind in [
        FunctionKind::LoopBody {
            parent: 99,
            slot: 0,
        },
        FunctionKind::LoopAfter {
            parent: 99,
            slot: 0,
        },
    ] {
        let mut prog = empty_program();
        let mut helper = func(
            "helper",
            sig(vec![], Type::Bool),
            body(vec![], Expr::Const(crate::ir::Const::Bool(true))),
            0,
        );
        helper.kind = helper_kind;
        add_function(&mut prog, 0, helper);

        add_function(
            &mut prog,
            1,
            func(
                "caller",
                sig(vec![], Type::Unit),
                body(
                    vec![Stmt::Let {
                        pattern: vec![Some("value".into()), Some("world".into())],
                        value: Expr::Call {
                            fun: 0,
                            type_args: vec![],
                            args: vec![],
                        },
                    }],
                    Expr::Unit,
                ),
                0,
            ),
        );

        let out = render_program(&prog).expect("program renders a loud per-function fallback");
        assert!(
            out.contains("render fallback")
                && out.contains(
                    "multi-slot let RHS type mismatch (post-stage-7 invariant violation)"
                )
                && !out.contains("let value : Unit := ()")
                && !out.contains("let world : Unit := ()"),
            "mismatched loop-helper handoff must fail closed:\n{out}"
        );
    }
}

#[test]
fn incompatible_if_arm_cannot_supply_a_multi_slot_let() {
    let mut prog = empty_program();
    add_function(
        &mut prog,
        0,
        func(
            "caller",
            sig(vec![param("cond", Type::Bool)], Type::Unit),
            body(
                vec![Stmt::Let {
                    pattern: vec![Some("value".into()), Some("flag".into())],
                    value: Expr::If {
                        cond: Box::new(var("cond")),
                        then_branch: Box::new(body(
                            vec![],
                            Expr::Tuple(vec![
                                lit_u64(1),
                                Expr::Const(crate::ir::Const::Bool(true)),
                            ]),
                        )),
                        else_branch: Box::new(body(vec![], lit_u64(2))),
                    },
                }],
                Expr::Unit,
            ),
            0,
        ),
    );

    let out = render_program(&prog).expect("program renders a loud per-function fallback");
    assert!(
        out.contains("render fallback")
            && out.contains("multi-slot let RHS type mismatch (post-stage-7 invariant violation)")
            && !out.contains("let value : Unit := ()")
            && !out.contains("let flag : Unit := ()"),
        "incompatible branches must not inherit the first arm's tuple type:\n{out}"
    );
}

#[test]
fn function_tail_target_does_not_hide_an_unrelated_tuple_type() {
    let mut prog = empty_program();
    add_function(
        &mut prog,
        0,
        func(
            "caller",
            sig(vec![param("cond", Type::Bool)], Type::Bool),
            body(
                vec![],
                Expr::If {
                    cond: Box::new(var("cond")),
                    then_branch: Box::new(body(vec![], Expr::Tuple(vec![lit_u64(1), lit_u64(2)]))),
                    else_branch: Box::new(body(vec![], Expr::Tuple(vec![lit_u64(3), lit_u64(4)]))),
                },
            ),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(out.contains("(1 : BoundedNat (2^64))"), "{out}");
    assert!(out.contains("(4 : BoundedNat (2^64))"), "{out}");
    assert!(
        !out.contains("sorry"),
        "unrelated target must fail in Lean: {out}"
    );
}

#[test]
fn abort_match_inliner_reconstructs_aborted_payload_once() {
    let mut prog = empty_program();
    let ids = crate::stage_07_dejumps::option_aborts::ensure_aborts_types(&mut prog);
    let selector_var = VarId::from("__abort");
    let code_var = VarId::from("code");
    let selector_value = Expr::If {
        cond: Box::new(var("cond")),
        then_branch: Box::new(Block::just(ids.make_some(lit_u64(7)))),
        else_branch: Box::new(Block::just(ids.make_none())),
    };
    let mut block = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(selector_var.clone())],
            value: selector_value,
        }],
        tail: BlockTail::Value(Expr::Match {
            struct_id: ids.option,
            selector: Box::new(Expr::Var(selector_var.clone())),
            cases: vec![
                MatchArm {
                    variant: crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG,
                    bindings: vec![],
                    body: Box::new(Block::just(ids.make_none())),
                },
                MatchArm {
                    variant: crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG,
                    bindings: vec![code_var.clone()],
                    body: Box::new(Block::just(Expr::Var(selector_var))),
                },
            ],
        }),
    };

    crate::render::function::inline_aborts_match_scrutinees(&mut block, &prog);

    assert!(block.stmts.is_empty(), "selector let should be inlined");
    let BlockTail::Value(Expr::Match {
        selector, cases, ..
    }) = &block.tail
    else {
        panic!("expected match tail, got {:?}", block.tail);
    };
    assert!(
        matches!(selector.as_ref(), Expr::If { .. }),
        "selector should be the original abort check"
    );
    let aborted = cases
        .iter()
        .find(|arm| arm.variant == crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG)
        .expect("aborted arm");
    assert!(aborted.body.stmts.is_empty());
    assert!(matches!(
        &aborted.body.tail,
        BlockTail::Value(Expr::Pack {
            struct_id,
            variant: Some(crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG),
            fields,
            ..
        }) if *struct_id == ids.option
            && matches!(fields.as_slice(), [Expr::Var(v)] if v == &code_var)
    ));
}

#[test]
fn abort_match_normalizer_reconstructs_aborted_payload_for_call_selector() {
    let mut prog = empty_program();
    let ids = crate::stage_07_dejumps::option_aborts::ensure_aborts_types(&mut prog);
    let callee_id = 0;
    let cont_id = 1;
    add_function(
        &mut prog,
        callee_id,
        func(
            "expensive.aborts",
            sig(
                vec![param("x", Type::UInt(64))],
                ids.option_abort_code_type(),
            ),
            Block::just(ids.make_none()),
            0,
        ),
    );
    add_function(
        &mut prog,
        cont_id,
        func(
            "expensive.aborts.cont_0",
            sig(vec![], ids.option_abort_code_type()),
            Block::just(ids.make_none()),
            0,
        ),
    );

    let code_var = VarId::from("code");
    let selector = Expr::Call {
        fun: callee_id,
        type_args: vec![],
        args: vec![var("x")],
    };
    let mut block = Block::just(Expr::Match {
        struct_id: ids.option,
        selector: Box::new(selector.clone()),
        cases: vec![
            MatchArm {
                variant: crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG,
                bindings: vec![],
                body: Box::new(Block::just(Expr::Call {
                    fun: cont_id,
                    type_args: vec![],
                    args: vec![],
                })),
            },
            MatchArm {
                variant: crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG,
                bindings: vec![code_var.clone()],
                body: Box::new(Block::just(selector)),
            },
        ],
    });

    crate::render::function::normalize_aborts_result_matches(&mut block, &prog);

    let BlockTail::Value(Expr::Match { cases, .. }) = &block.tail else {
        panic!("expected match tail, got {:?}", block.tail);
    };
    let aborted = cases
        .iter()
        .find(|arm| arm.variant == crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG)
        .expect("aborted arm");
    assert!(aborted.body.stmts.is_empty());
    assert!(matches!(
        &aborted.body.tail,
        BlockTail::Value(Expr::Pack {
            struct_id,
            type_args,
            variant: Some(crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG),
            fields,
        }) if *struct_id == ids.option
            && type_args == &vec![ids.abort_code_type()]
            && matches!(fields.as_slice(), [Expr::Var(v)] if v == &code_var)
    ));
}

#[test]
fn abort_match_normalizer_reconstructs_aborted_payload_inside_wrapper() {
    let mut prog = empty_program();
    let ids = crate::stage_07_dejumps::option_aborts::ensure_aborts_types(&mut prog);
    let callee_id = 0;
    let wrapper_id = 42;
    add_function(
        &mut prog,
        callee_id,
        func(
            "expensive.aborts",
            sig(
                vec![param("x", Type::UInt(64))],
                ids.option_abort_code_type(),
            ),
            Block::just(ids.make_none()),
            0,
        ),
    );
    add_struct(
        &mut prog,
        wrapper_id,
        simple_struct(0, "Step", vec![("result", ids.option_abort_code_type())]),
    );

    let code_var = VarId::from("code");
    let selector = Expr::Call {
        fun: callee_id,
        type_args: vec![],
        args: vec![var("x")],
    };
    let wrapped_selector = Expr::Pack {
        struct_id: wrapper_id,
        type_args: vec![],
        variant: None,
        fields: vec![selector.clone()],
    };
    let wrapped_no_abort = Expr::Pack {
        struct_id: wrapper_id,
        type_args: vec![],
        variant: None,
        fields: vec![ids.make_none()],
    };
    let mut block = Block::just(Expr::Match {
        struct_id: ids.option,
        selector: Box::new(selector),
        cases: vec![
            MatchArm {
                variant: crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG,
                bindings: vec![],
                body: Box::new(Block::just(wrapped_no_abort)),
            },
            MatchArm {
                variant: crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG,
                bindings: vec![code_var.clone()],
                body: Box::new(Block::just(wrapped_selector)),
            },
        ],
    });

    crate::render::function::normalize_aborts_result_matches(&mut block, &prog);

    let BlockTail::Value(Expr::Match { cases, .. }) = &block.tail else {
        panic!("expected match tail, got {:?}", block.tail);
    };
    let aborted = cases
        .iter()
        .find(|arm| arm.variant == crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG)
        .expect("aborted arm");
    assert!(aborted.body.stmts.is_empty());
    assert!(matches!(
        &aborted.body.tail,
        BlockTail::Value(Expr::Pack {
            struct_id,
            fields,
            ..
        }) if *struct_id == wrapper_id
            && matches!(
                fields.as_slice(),
                [Expr::Pack {
                    struct_id: abort_struct_id,
                    type_args,
                    variant: Some(crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG),
                    fields: abort_fields,
                }] if *abort_struct_id == ids.option
                    && type_args == &vec![ids.abort_code_type()]
                    && matches!(abort_fields.as_slice(), [Expr::Var(v)] if v == &code_var)
            )
    ));
}

// ---- commit 0b4bbb48: single-line if-then-else when both arms ----
// ---- are tail-only ----

#[test]
fn if_with_both_arms_tail_only_renders_single_line_inside_pack() {
    // When `Expr::If` appears as a struct-pack field value (or any
    // other context that goes through `render_expr` rather than the
    // function-body tail-coerced path), the renderer must emit it
    // on a single line iff both arms are `Block { stmts: [], tail:
    // Value(_) }`. The multi-line layout's `else` keyword sits at
    // the writer's outer indent column -- well to the LEFT of `if`
    // inside long expression chains -- and Lean's indent-sensitive
    // parser would mis-attach it.
    //
    // The function-body top-level `If` goes through a separate
    // multi-line coerced path (`render_tail_value_coerced`) and is
    // intentionally NOT affected by this single-line optimisation;
    // see `if_function_body_tail_keeps_multi_line_layout` below.
    let mut prog = empty_program();
    let pair = Struct {
        module_id: 0,
        name: "Pair".to_string(),
        qualified_name: "p::m::Pair".to_string(),
        type_params: vec![],
        fields: vec![
            Field {
                name: "a".to_string(),
                field_type: Type::UInt(64),
            },
            Field {
                name: "b".to_string(),
                field_type: Type::UInt(64),
            },
        ],
        variants: None,
        is_native: false,
    };
    add_struct(&mut prog, 0, pair);

    let pack = Expr::Pack {
        struct_id: 0,
        type_args: vec![],
        variant: None,
        fields: vec![
            Expr::If {
                cond: Box::new(var("c")),
                then_branch: Box::new(Block::just(lit_u64(1))),
                else_branch: Box::new(Block::just(lit_u64(2))),
            },
            lit_u64(3),
        ],
    };
    let f = Function {
        module: 0,
        name: "pick_pack".to_string(),
        signature: Signature {
            type_params: vec![],
            params: vec![Param {
                name: "c".to_string(),
                var: VarId::from("c"),
                ty: Type::Bool,
            }],
            return_type: Type::Struct {
                struct_id: 0,
                type_args: vec![],
            },
        },
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(pack),
        },
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
    };
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    // `if`, `then`, and `else` all on the same physical line
    // for the inner If.
    let body_line = out
        .lines()
        .find(|l| l.contains("if c then "))
        .unwrap_or_else(|| panic!("no single-line if-then in output:\n{}", out));
    assert!(
        body_line.contains(" else "),
        "expected single-line if-then-else inside pack, got:\n{}",
        out
    );
}

#[test]
fn if_function_body_tail_keeps_multi_line_layout() {
    // Regression guard: the function-body tail position goes
    // through `render_tail_value_coerced`, which preserves the
    // multi-line layout. The single-line optimisation only fires
    // for `Expr::If` reached via `render_expr` (nested contexts).
    let mut prog = empty_program();
    let f = Function {
        module: 0,
        name: "pick".to_string(),
        signature: Signature {
            type_params: vec![],
            params: vec![
                Param {
                    name: "c".to_string(),
                    var: VarId::from("c"),
                    ty: Type::Bool,
                },
                Param {
                    name: "a".to_string(),
                    var: VarId::from("a"),
                    ty: Type::UInt(64),
                },
                Param {
                    name: "b".to_string(),
                    var: VarId::from("b"),
                    ty: Type::UInt(64),
                },
            ],
            return_type: Type::UInt(64),
        },
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::If {
                cond: Box::new(var("c")),
                then_branch: Box::new(Block::just(var("a"))),
                else_branch: Box::new(Block::just(var("b"))),
            }),
        },
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
    };
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    // Top-level function-body `if` -- `else` must land on its own
    // line per the legacy multi-line layout.
    let has_single_line_outer = out
        .lines()
        .any(|l| l.contains("if c then ") && l.contains(" else "));
    assert!(
        !has_single_line_outer,
        "function-body tail If should keep multi-line layout, got:\n{}",
        out
    );
}

#[test]
fn if_with_non_empty_arm_keeps_multi_line_layout() {
    // If either arm has a non-empty `stmts` list, the single-line
    // emission is gated off and the multi-line layout still applies
    // -- a regression guard that the gate is on `stmts.is_empty()`,
    // not just the `BlockTail::Value` discriminant.
    let mut prog = empty_program();
    let then_b = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(VarId::from("a1"))],
            value: var("a"),
        }],
        tail: BlockTail::Value(var("a1")),
    };
    let else_b = Block::just(var("b"));
    let f = Function {
        module: 0,
        name: "pick_long".to_string(),
        signature: Signature {
            type_params: vec![],
            params: vec![
                Param {
                    name: "c".to_string(),
                    var: VarId::from("c"),
                    ty: Type::Bool,
                },
                Param {
                    name: "a".to_string(),
                    var: VarId::from("a"),
                    ty: Type::UInt(64),
                },
                Param {
                    name: "b".to_string(),
                    var: VarId::from("b"),
                    ty: Type::UInt(64),
                },
            ],
            return_type: Type::UInt(64),
        },
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::If {
                cond: Box::new(var("c")),
                then_branch: Box::new(then_b),
                else_branch: Box::new(else_b),
            }),
        },
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
    };
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    // The single-line path would have `then ... else` on one
    // physical line. With a non-empty stmts in the then arm the
    // multi-line path triggers, putting `else` on its own line.
    let has_single_line = out
        .lines()
        .any(|l| l.contains("if ") && l.contains(" then ") && l.contains(" else "));
    assert!(
        !has_single_line,
        "non-empty arm should NOT trigger single-line layout, got:\n{}",
        out
    );
}

// ---- commit fb2d00a2: parenthesise struct-pack field values ----

#[test]
fn pack_field_with_if_value_is_parenthesised() {
    // A `Pack` whose field value is multi-token (`Expr::If`) must
    // wrap the value in parens so the trailing `, <next field>` of
    // the struct literal isn't consumed by the if's else-arm.
    let mut prog = empty_program();
    let pair = Struct {
        module_id: 0,
        name: "Pair".to_string(),
        qualified_name: "p::m::Pair".to_string(),
        type_params: vec![],
        fields: vec![
            Field {
                name: "a".to_string(),
                field_type: Type::UInt(64),
            },
            Field {
                name: "b".to_string(),
                field_type: Type::UInt(64),
            },
        ],
        variants: None,
        is_native: false,
    };
    add_struct(&mut prog, 0, pair);

    let pack = Expr::Pack {
        struct_id: 0,
        type_args: vec![],
        variant: None,
        fields: vec![
            Expr::If {
                cond: Box::new(var("c")),
                then_branch: Box::new(Block::just(lit_u64(1))),
                else_branch: Box::new(Block::just(lit_u64(2))),
            },
            lit_u64(3),
        ],
    };
    let f = Function {
        module: 0,
        name: "make_pair".to_string(),
        signature: Signature {
            type_params: vec![],
            params: vec![Param {
                name: "c".to_string(),
                var: VarId::from("c"),
                ty: Type::Bool,
            }],
            return_type: Type::Struct {
                struct_id: 0,
                type_args: vec![],
            },
        },
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(pack),
        },
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
    };
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    // The field value is wrapped: `a := (if ... then ... else ...)`.
    // Without the parens, the renderer would emit a bare
    // `a := if c then 1 else 2, b := 3` which Lean reads as the
    // else-arm consuming the trailing `, b := 3`.
    assert!(
        out.contains("a := ("),
        "expected `a := (` (paren-wrapped value), got:\n{}",
        out
    );
}

#[test]
fn pack_field_with_binop_value_is_parenthesised() {
    // BinOp values are also multi-token. Same parenthesisation
    // requirement as if/match Call.
    let mut prog = empty_program();
    let pair = Struct {
        module_id: 0,
        name: "Pair".to_string(),
        qualified_name: "p::m::Pair".to_string(),
        type_params: vec![],
        fields: vec![
            Field {
                name: "a".to_string(),
                field_type: Type::UInt(64),
            },
            Field {
                name: "b".to_string(),
                field_type: Type::UInt(64),
            },
        ],
        variants: None,
        is_native: false,
    };
    add_struct(&mut prog, 0, pair);

    let pack = Expr::Pack {
        struct_id: 0,
        type_args: vec![],
        variant: None,
        fields: vec![
            Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(var("x")),
                rhs: Box::new(lit_u64(1)),
            },
            lit_u64(3),
        ],
    };
    let f = Function {
        module: 0,
        name: "make_pair_add".to_string(),
        signature: Signature {
            type_params: vec![],
            params: vec![Param {
                name: "x".to_string(),
                var: VarId::from("x"),
                ty: Type::UInt(64),
            }],
            return_type: Type::Struct {
                struct_id: 0,
                type_args: vec![],
            },
        },
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(pack),
        },
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
    };
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    // `a := (x + (1 : ...))` -- the outer parens around the BinOp
    // are added by `render_with_parens_if_needed`.
    assert!(
        out.contains("a := ("),
        "expected `a := (` (paren-wrapped BinOp), got:\n{}",
        out
    );
}

// ---- commit e0e09e8a: partial def for source-level self-recursive ----
// ---- functions ----

#[test]
fn self_recursive_source_function_emits_partial_fixpoint() {
    // `fn rec(n: u64): u64 { rec(n) }` -- the simplest tree-recursive
    // shape. Lean's structural termination check can't see through
    // BoundedNat / List indices, so the renderer emits a
    // `def … partial_fixpoint` (same gate as self-recursive loop
    // helpers) when the body contains a direct self-call. Unlike an
    // opaque `partial def`, `partial_fixpoint` exposes `.eq_def`, so
    // obligations reaching the recursion (e.g. `max_heapify_recursive`
    // via `derive_reference_gas_price`) become provable.
    let mut prog = empty_program();

    // Build the function first, then patch its body to call itself.
    let f = Function {
        module: 0,
        name: "rec".to_string(),
        signature: Signature {
            type_params: vec![],
            params: vec![Param {
                name: "n".to_string(),
                var: VarId::from("n"),
                ty: Type::UInt(64),
            }],
            return_type: Type::UInt(64),
        },
        body: Block {
            stmts: vec![],
            // Initial placeholder body -- we'll patch in the Call(0)
            // after registering the function, since the renderer
            // resolves Call(fid) against the registered functions.
            tail: BlockTail::Value(Expr::Call {
                fun: 0,
                type_args: vec![],
                args: vec![var("n")],
            }),
        },
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    };
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("def rec") && out.contains("partial_fixpoint"),
        "expected `def rec … partial_fixpoint` for self-recursive fn, got:\n{}",
        out
    );
    assert!(
        !out.contains("partial def rec"),
        "self-recursive source must be `partial_fixpoint`, not opaque `partial def`, got:\n{}",
        out
    );
}

#[test]
fn execution_mode_makes_self_recursion_opaque_without_changing_proof_or_test() {
    use crate::render::loop_termination::{LoopMode, LoopTerminationRegistry};

    let mut prog = empty_program();
    add_function(
        &mut prog,
        0,
        Function {
            module: 0,
            name: "rec".to_string(),
            signature: sig(vec![param("n", Type::UInt(64))], Type::UInt(64)),
            body: body(
                vec![],
                Expr::Call {
                    fun: 0,
                    type_args: vec![],
                    args: vec![var("n")],
                },
            ),
            kind: FunctionKind::Source,
            effects: crate::ir::Effects::CONSERVATIVE,
            explicit_pure: false,
        },
    );
    add_function(
        &mut prog,
        1,
        func(
            "identity",
            sig(vec![param("n", Type::UInt(64))], Type::UInt(64)),
            body(vec![], var("n")),
            0,
        ),
    );
    let registry = LoopTerminationRegistry::parse(
        "@loop p.m.rec\n@measure\nn.val\n@decreasing\nomega\n@end\n",
    );

    let proof = render_program_in_loop_mode(&prog, LoopMode::Proof, registry.clone());
    assert!(proof.contains("def rec"), "{proof}");
    assert!(proof.contains("termination_by n.val"), "{proof}");
    assert!(!proof.contains("partial_fixpoint"), "{proof}");
    assert!(!proof.contains("partial def rec"), "{proof}");

    let test = render_program_in_loop_mode(&prog, LoopMode::Test, registry.clone());
    assert!(test.contains("def rec"), "{test}");
    assert!(test.contains("partial_fixpoint"), "{test}");
    assert!(!test.contains("termination_by"), "{test}");
    assert!(!test.contains("partial def rec"), "{test}");

    let execution = render_program_in_loop_mode(&prog, LoopMode::Execution, registry);
    assert!(execution.contains("partial def rec"), "{execution}");
    assert!(!execution.contains("partial_fixpoint"), "{execution}");
    assert!(!execution.contains("termination_by"), "{execution}");
    for rendered in [&proof, &test, &execution] {
        assert!(rendered.contains("def identity"), "{rendered}");
        assert!(!rendered.contains("partial def identity"), "{rendered}");
    }
}

fn read_only_world_loop_member(
    name: &str,
    kind: FunctionKind,
    current_world: &str,
    callee: FunId,
    world_type: &Type,
) -> Function {
    Function {
        module: 0,
        name: name.to_string(),
        signature: sig(
            vec![
                param("world_0", world_type.clone()),
                param(current_world, world_type.clone()),
            ],
            Type::Tuple(vec![Type::UInt(64), world_type.clone()]),
        ),
        body: body(
            vec![],
            Expr::Call {
                fun: callee,
                type_args: vec![],
                args: vec![var("world_0"), var(current_world)],
            },
        ),
        kind,
        effects: crate::ir::Effects::WORLD,
        explicit_pure: false,
    }
}

#[test]
fn read_only_world_mutual_fixpoint_uses_entry_world_bottom() {
    let mut prog = empty_program();
    let world_id = crate::stage_04_effects::ensure_world_struct(&mut prog);
    let world_type = crate::stage_04_effects::world_type(world_id);
    add_function(
        &mut prog,
        0,
        read_only_world_loop_member(
            "loop_a",
            FunctionKind::LoopBody {
                parent: 99,
                slot: 0,
            },
            "world_1",
            1,
            &world_type,
        ),
    );
    add_function(
        &mut prog,
        1,
        read_only_world_loop_member(
            "loop_b",
            FunctionKind::LoopAfter {
                parent: 99,
                slot: 0,
            },
            "world_1",
            0,
            &world_type,
        ),
    );

    let out = render_program(&prog).expect("render read-only mutual fixpoint");
    let indexed = "_root_.Prover.World.ReadOnlyWorldResult World (BoundedNat (2^64)) world_0";
    assert_eq!(
        out.matches(indexed).count(),
        2,
        "every mutual member must share the entry-World-indexed result:\n{out}"
    );
    assert!(
        !out.contains("ReadOnlyWorldResult World (BoundedNat (2^64)) world_1")
            && !out.contains("ReadOnlyWorldResult World (BoundedNat (2^64)) world_2"),
        "the changing threaded World must not define the bottom:\n{out}"
    );
    assert_eq!(out.matches("partial_fixpoint").count(), 2);

    prog.functions.get_mut(&0).unwrap().effects.world_writes = true;
    let writing = render_program(&prog).expect("render writing mutual fixpoint");
    assert!(
        !writing.contains("ReadOnlyWorldResult"),
        "a writing SCC must retain the conservative fallback:\n{writing}"
    );
}

#[test]
fn execution_mode_makes_eligible_mutual_scc_opaque_without_changing_other_modes() {
    use crate::render::loop_termination::{LoopMode, LoopTerminationRegistry};

    let mut prog = empty_program();
    add_function(
        &mut prog,
        0,
        Function {
            module: 0,
            name: "loop_a".to_string(),
            signature: sig(vec![param("n", Type::UInt(64))], Type::UInt(64)),
            body: body(
                vec![],
                Expr::Call {
                    fun: 1,
                    type_args: vec![],
                    args: vec![var("n")],
                },
            ),
            kind: FunctionKind::LoopBody {
                parent: 99,
                slot: 0,
            },
            effects: crate::ir::Effects::CONSERVATIVE,
            explicit_pure: false,
        },
    );
    add_function(
        &mut prog,
        1,
        Function {
            module: 0,
            name: "loop_b".to_string(),
            signature: sig(vec![param("n", Type::UInt(64))], Type::UInt(64)),
            body: body(
                vec![],
                Expr::Call {
                    fun: 0,
                    type_args: vec![],
                    args: vec![var("n")],
                },
            ),
            kind: FunctionKind::LoopAfter {
                parent: 99,
                slot: 0,
            },
            effects: crate::ir::Effects::CONSERVATIVE,
            explicit_pure: false,
        },
    );

    for mode in [LoopMode::Proof, LoopMode::Test] {
        let rendered = render_program_in_loop_mode(&prog, mode, LoopTerminationRegistry::default());
        assert!(rendered.contains("mutual"), "{rendered}");
        assert_eq!(
            rendered.matches("partial_fixpoint").count(),
            2,
            "{rendered}"
        );
        assert!(!rendered.contains("partial def"), "{rendered}");
    }

    let execution = render_program_in_loop_mode(
        &prog,
        LoopMode::Execution,
        LoopTerminationRegistry::default(),
    );
    assert!(execution.contains("mutual"), "{execution}");
    assert_eq!(execution.matches("partial def").count(), 2, "{execution}");
    assert!(!execution.contains("partial_fixpoint"), "{execution}");
    assert!(!execution.contains("termination_by"), "{execution}");
}

#[test]
fn execution_mode_makes_source_mutual_scc_opaque() {
    use crate::render::loop_termination::{LoopMode, LoopTerminationRegistry};

    let mut prog = empty_program();
    for (id, name, callee) in [(0, "source_a", 1), (1, "source_b", 0)] {
        add_function(
            &mut prog,
            id,
            Function {
                module: 0,
                name: name.to_string(),
                signature: sig(vec![param("n", Type::UInt(64))], Type::UInt(64)),
                body: body(
                    vec![],
                    Expr::Call {
                        fun: callee,
                        type_args: vec![],
                        args: vec![var("n")],
                    },
                ),
                kind: FunctionKind::Source,
                effects: crate::ir::Effects::CONSERVATIVE,
                explicit_pure: false,
            },
        );
    }

    let execution = render_program_in_loop_mode(
        &prog,
        LoopMode::Execution,
        LoopTerminationRegistry::default(),
    );
    assert!(execution.contains("mutual"), "{execution}");
    assert_eq!(execution.matches("partial def").count(), 2, "{execution}");
    assert!(!execution.contains("partial_fixpoint"), "{execution}");
    assert!(!execution.contains("termination_by"), "{execution}");
}

#[test]
fn read_only_world_singleton_fixpoint_uses_entry_world_bottom() {
    let mut prog = empty_program();
    let world_id = crate::stage_04_effects::ensure_world_struct(&mut prog);
    let world_type = crate::stage_04_effects::world_type(world_id);
    add_function(
        &mut prog,
        0,
        read_only_world_loop_member(
            "loop_single",
            FunctionKind::LoopBody {
                parent: 99,
                slot: 0,
            },
            "world_1",
            0,
            &world_type,
        ),
    );

    let out = render_program(&prog).expect("render read-only singleton fixpoint");
    let indexed = "_root_.Prover.World.ReadOnlyWorldResult World (BoundedNat (2^64)) world_0";
    assert_eq!(out.matches(indexed).count(), 1, "{out}");
    assert!(!out.contains("ReadOnlyWorldResult World (BoundedNat (2^64)) world_1"));
    assert_eq!(out.matches("partial_fixpoint").count(), 1);

    prog.functions.get_mut(&0).unwrap().effects.world_writes = true;
    let writing = render_program(&prog).expect("render writing singleton fixpoint");
    assert!(!writing.contains("ReadOnlyWorldResult"), "{writing}");
}

#[test]
fn non_self_recursive_source_function_emits_plain_def() {
    // Regression guard: a non-recursive function still gets
    // `def`, not `partial def`. (The self-call gate must be a
    // tight match on `(module, name)`, not "any function with
    // body matching its own shape".)
    let mut prog = empty_program();
    let f = func(
        "id",
        sig(vec![param("n", Type::UInt(64))], Type::UInt(64)),
        body(vec![], var("n")),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(out.contains("def id"), "expected `def id`, got:\n{}", out);
    assert!(
        !out.contains("partial def id"),
        "non-recursive fn should NOT be `partial def`, got:\n{}",
        out
    );
}

// Shared builders for the two `max_heapify_recursive`-shaped abort-SCC
// fixtures below: a self-recursive source `#0 rec`, its `.aborts` companion
// `#1` (tail-calling the cont `#2`), and the recursive cont `#2` whose body
// is a `match rec.aborts(n) { NoAbort => <no_abort_arm>, Aborted e => Aborted e }`.
// The two tests differ only in `<no_abort_arm>` -- whether the post-recursion
// continuation is trivially NoAbort (collapses -> `partial_fixpoint`) or has
// real content (stays opaque `partial def`).
fn self_recursive_source(id: FunId) -> Function {
    Function {
        module: 0,
        name: "rec".to_string(),
        signature: sig(vec![param("n", Type::UInt(64))], Type::UInt(64)),
        body: body(
            vec![],
            Expr::Call {
                fun: id,
                type_args: vec![],
                args: vec![var("n")],
            },
        ),
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    }
}

fn aborts_companion(abort_ty: Type, cont_id: FunId) -> Function {
    Function {
        module: 0,
        name: "rec.aborts".to_string(),
        signature: sig(vec![param("n", Type::UInt(64))], abort_ty),
        body: body(
            vec![],
            Expr::Call {
                fun: cont_id,
                type_args: vec![],
                args: vec![var("n")],
            },
        ),
        kind: FunctionKind::Spec {
            kind: crate::ir::SpecKind::Aborts,
            target: 0,
        },
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    }
}

fn recursive_cont(
    ids: &crate::stage_07_dejumps::option_aborts::AbortsTypeIds,
    abort_ty: Type,
    aborts_id: FunId,
    no_abort_arm: Block,
) -> Function {
    let code_var = VarId::from("e");
    Function {
        module: 0,
        name: "rec.aborts.cont_0".to_string(),
        signature: sig(vec![param("n", Type::UInt(64))], abort_ty),
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Match {
                struct_id: ids.option,
                selector: Box::new(Expr::Call {
                    fun: aborts_id,
                    type_args: vec![],
                    args: vec![var("n")],
                }),
                cases: vec![
                    MatchArm {
                        variant: crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG,
                        bindings: vec![],
                        body: Box::new(no_abort_arm),
                    },
                    MatchArm {
                        variant: crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG,
                        bindings: vec![code_var.clone()],
                        // `Aborted e => Aborted e` (canonical repack -- the
                        // Some variant holds the AbortCode value directly).
                        body: Box::new(Block::just(Expr::Pack {
                            struct_id: ids.option,
                            type_args: vec![ids.abort_code_type()],
                            variant: Some(crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG),
                            fields: vec![Expr::Var(code_var.clone())],
                        })),
                    },
                ],
            }),
        },
        kind: FunctionKind::Synthetic,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    }
}

#[test]
fn tail_recursive_source_abort_collapses_to_partial_fixpoint() {
    // `sui::priority_queue::max_heapify_recursive` shape: a self-recursive
    // SOURCE function whose `.aborts` companion recurses through a `.cont_*`
    // helper. The recursive `.aborts` call sits in a `match` SCRUTINEE, but
    // its NoAbort arm is trivially abort-free (a tail call to a `.cont_*`
    // leaf `#3` that returns NoAbort). `collapse_tail_recursive_aborts_match`
    // rewrites that identity propagation into the bare recursive call
    // (tail-position, monotone), so `scc_is_fixpoint_eligible` blesses the
    // abort SCC {#1, #2} and it renders as `partial_fixpoint` (real
    // `.eq_def`), NOT opaque `partial def`.
    let mut prog = empty_program();
    let ids = crate::stage_07_dejumps::option_aborts::ensure_aborts_types(&mut prog);
    let abort_ty = ids.option_abort_code_type();

    add_function(&mut prog, 0, self_recursive_source(0));
    add_function(&mut prog, 1, aborts_companion(abort_ty.clone(), 2));
    // NoAbort arm tail-calls the NoAbort leaf `#3` -> reduces to NoAbort.
    let no_abort_arm = Block::just(Expr::Call {
        fun: 3,
        type_args: vec![],
        args: vec![var("n")],
    });
    add_function(
        &mut prog,
        2,
        recursive_cont(&ids, abort_ty.clone(), 1, no_abort_arm),
    );
    // #3: `rec.aborts.cont_0.cont_0` NoAbort leaf (Synthetic, not in the SCC).
    add_function(
        &mut prog,
        3,
        Function {
            module: 0,
            name: "rec.aborts.cont_0.cont_0".to_string(),
            signature: sig(vec![param("n", Type::UInt(64))], abort_ty.clone()),
            body: body(vec![], ids.make_none()),
            kind: FunctionKind::Synthetic,
            effects: crate::ir::Effects::CONSERVATIVE,
            explicit_pure: false,
        },
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("mutual"),
        "expected a mutual block, got:\n{}",
        out
    );
    // In a fixpoint-eligible mutual block every member is `def … partial_fixpoint`,
    // never `partial def`. (The source value face #0 is a separate
    // `def rec … partial_fixpoint` singleton; the leaf #3 is a plain `def`.)
    assert!(
        !out.contains("partial def"),
        "collapsed tail-recursive abort SCC must be `partial_fixpoint`, not opaque \
         `partial def`, got:\n{}",
        out
    );
    assert!(
        out.contains("def rec.aborts") && out.contains("partial_fixpoint"),
        "abort face should render as a fixpoint def, got:\n{}",
        out
    );
}

#[test]
fn non_tail_source_abort_stays_partial_def() {
    // Guard the narrow gate: when the `.aborts` recursion's post-call
    // continuation is NOT trivially NoAbort (real abort behaviour remains
    // after the recursive call -- non-tail recursion), the
    // identity-propagation match does NOT collapse, the recursive `.aborts`
    // call stays in the `match` SCRUTINEE (non-monotone), and the abort SCC
    // {#1, #2} keeps its opaque `partial def`.
    let mut prog = empty_program();
    let ids = crate::stage_07_dejumps::option_aborts::ensure_aborts_types(&mut prog);
    let abort_ty = ids.option_abort_code_type();

    add_function(&mut prog, 0, self_recursive_source(0));
    add_function(&mut prog, 1, aborts_companion(abort_ty.clone(), 2));
    // NoAbort arm returns `Aborted 0` -- it does NOT reduce to NoAbort, so
    // this is NOT the collapsible tail-identity shape.
    let no_abort_arm = Block::just(ids.make_some(lit_u64(0)));
    add_function(
        &mut prog,
        2,
        recursive_cont(&ids, abort_ty.clone(), 1, no_abort_arm),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("mutual"),
        "expected a mutual block, got:\n{}",
        out
    );
    assert!(
        out.contains("partial def rec.aborts"),
        "non-tail source abort SCC must stay opaque `partial def`, got:\n{}",
        out
    );
    assert!(
        out.contains("partial def rec.aborts.cont_0"),
        "the whole non-collapsible abort SCC must be `partial def`, got:\n{}",
        out
    );
}

#[test]
fn target_typed_inner_blocks_erase_only_discarded_results() {
    let mut prog = empty_program();
    let mutable_u64 = Type::MutableRef {
        inner: Box::new(Type::UInt(64)),
        root: Box::new(Type::UInt(64)),
    };
    let discarded = vec![
        Stmt::Eval(lit_u64(91)),
        Stmt::Let {
            pattern: vec![None],
            value: lit_u64(92),
        },
    ];
    add_function(
        &mut prog,
        0,
        func(
            "discarded",
            sig(
                vec![
                    param("cond", Type::Bool),
                    param("mutation", mutable_u64.clone()),
                    param("value", Type::UInt(64)),
                ],
                Type::UInt(64),
            ),
            body(
                vec![let_(
                    "result",
                    Expr::If {
                        cond: Box::new(var("cond")),
                        then_branch: Box::new(Block {
                            stmts: discarded,
                            tail: BlockTail::Value(var("mutation")),
                        }),
                        else_branch: Box::new(Block::just(var("value"))),
                    },
                )],
                Expr::ReadRef(Box::new(var("result"))),
            ),
            0,
        ),
    );
    add_function(
        &mut prog,
        1,
        func(
            "named",
            sig(
                vec![
                    param("cond", Type::Bool),
                    param("mutation", mutable_u64.clone()),
                ],
                Type::UInt(64),
            ),
            body(
                vec![let_(
                    "result",
                    Expr::If {
                        cond: Box::new(var("cond")),
                        then_branch: Box::new(Block::just(var("mutation"))),
                        else_branch: Box::new(Block {
                            stmts: vec![let_("kept", lit_u64(93))],
                            tail: BlockTail::Value(var("kept")),
                        }),
                    },
                )],
                Expr::ReadRef(Box::new(var("result"))),
            ),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        !out.contains("91") && !out.contains("92") && !out.contains("let _"),
        "discard-only inner statements must be erased on the target-typed path:\n{out}"
    );
    assert!(
        out.contains("let kept := (93 : BoundedNat (2^64))"),
        "named inner bindings must be retained:\n{out}"
    );
}

#[test]
fn target_typed_inner_blocks_erase_discarded_partial_arithmetic() {
    let mut prog = empty_program();
    let mutable_u64 = Type::MutableRef {
        inner: Box::new(Type::UInt(64)),
        root: Box::new(Type::UInt(64)),
    };
    add_function(
        &mut prog,
        0,
        func(
            "partial_discard",
            sig(
                vec![
                    param("cond", Type::Bool),
                    param("mutation", mutable_u64),
                    param("value", Type::UInt(64)),
                ],
                Type::UInt(64),
            ),
            body(
                vec![let_(
                    "result",
                    Expr::If {
                        cond: Box::new(var("cond")),
                        then_branch: Box::new(Block {
                            stmts: vec![Stmt::Eval(add(lit_u64(9101), lit_u64(9102)))],
                            tail: BlockTail::Value(var("mutation")),
                        }),
                        else_branch: Box::new(Block::just(var("value"))),
                    },
                )],
                Expr::ReadRef(Box::new(var("result"))),
            ),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(out.contains("opaque large_uint_u64_9101"));
    assert!(out.contains("opaque large_uint_u64_9102"));
    let rendered_body = out
        .split_once("def partial_discard")
        .expect("partial_discard definition")
        .1
        .split_once("\n\n")
        .expect("end of partial_discard definition")
        .0;
    assert!(
        !rendered_body.contains("large_uint_u64_9101")
            && !rendered_body.contains("large_uint_u64_9102")
            && !rendered_body.contains("let _"),
        "discarded partial arithmetic must be absent from the rendered value body:\n{out}"
    );
}

#[test]
fn function_tail_inner_blocks_erase_only_discarded_results() {
    let mut prog = empty_program();
    add_function(
        &mut prog,
        0,
        func(
            "tail_discard",
            sig(vec![param("cond", Type::Bool)], Type::UInt(64)),
            Block::just(Expr::If {
                cond: Box::new(var("cond")),
                then_branch: Box::new(Block {
                    stmts: vec![
                        Stmt::Eval(lit_u64(101)),
                        Stmt::Let {
                            pattern: vec![None],
                            value: lit_u64(102),
                        },
                    ],
                    tail: BlockTail::Value(lit_u64(1)),
                }),
                else_branch: Box::new(Block {
                    stmts: vec![let_("kept", lit_u64(103))],
                    tail: BlockTail::Value(var("kept")),
                }),
            }),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        !out.contains("101") && !out.contains("102") && !out.contains("let _"),
        "discard-only statements must be erased from function-tail arms:\n{out}"
    );
    assert!(
        out.contains("let kept := (103 : BoundedNat (2^64))"),
        "named function-tail bindings must be retained:\n{out}"
    );
}

// ---- commit edcf2064: BorrowLoc respects var_overrides for the ----
// ---- wrapped variable ----

#[test]
fn borrow_loc_uses_param_display_name_not_ssa_var() {
    // `fn use_ref(split_coin: u64): MutableRef<u64> { &split_coin }`
    // where the param's SSA var is `$t0_0` but the signature emits
    // the parameter as `split_coin`. The BorrowLoc must honour the
    // var_overrides map and write `split_coin` (not `t_t0_0`) as
    // the wrapped var inside `Mutation.ofLocal`.
    //
    // Without the override lookup the body emitted `t_t0_0` -- an
    // undefined identifier -- and Lean rejected it. Surfaced on
    // navi-lending:utils and momentum-clmm:Pool.
    let mut prog = empty_program();
    let f = Function {
        module: 0,
        name: "use_ref".to_string(),
        signature: Signature {
            type_params: vec![],
            params: vec![Param {
                name: "split_coin".to_string(),
                var: VarId::from("$t0_0"),
                ty: Type::UInt(64),
            }],
            return_type: Type::MutableRef {
                inner: Box::new(Type::UInt(64)),
                root: Box::new(Type::UInt(64)),
            },
        },
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::BorrowLoc(VarId::from("$t0_0"))),
        },
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    };
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    // `split_coin` appears in the signature; the load-bearing check
    // is that the BorrowLoc wraps it in the body too, NOT the
    // escaped SSA var `t_t0_0`.
    assert!(
        !out.contains("t_t0_0"),
        "body must NOT reference escaped SSA var `t_t0_0`, got:\n{}",
        out
    );
    // Find the line containing the body's `Mutation.ofLocal` wrap
    // and confirm the wrapped var is the display name.
    let body_line = out
        .lines()
        .find(|l| l.contains("Mutation.ofLocal"))
        .unwrap_or_else(|| panic!("no Mutation.ofLocal in output:\n{}", out));
    assert!(
        body_line.contains("split_coin"),
        "BorrowLoc wrap should use display name `split_coin`, got line:\n{}\nfull:\n{}",
        body_line,
        out
    );
}

// ---- writeback-lowering S1: in-value map set (`Update{MapKey}`) ----

fn sui_map_program(module_name: &str, struct_name: &str) -> (crate::ir::Program, Type) {
    let mut prog = empty_program();
    prog.modules.insert(
        1,
        crate::ir::Module {
            name: module_name.to_string(),
            package_name: "Sui".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    let map_struct = Struct {
        module_id: 1,
        name: struct_name.to_string(),
        qualified_name: format!("sui::{}::{}", module_name, struct_name),
        type_params: vec!["K".to_string(), "V".to_string()],
        fields: vec![],
        variants: None,
        is_native: true,
    };
    add_struct(&mut prog, 0, map_struct);
    let map_ty = Type::Struct {
        struct_id: 0,
        type_args: vec![Type::UInt(64), Type::UInt(8)],
    };
    (prog, map_ty)
}

fn mapkey_update(df_value: Option<VarId>) -> Expr {
    Expr::Update {
        step: crate::ir::path::PathStep::MapKey {
            key: Box::new(var("k")),
            key_type: Type::UInt(64),
            value_type: Type::UInt(8),
            df_value,
        },
        base: Box::new(var("t")),
        value: Box::new(var("v")),
    }
}

fn mapkey_update_fn(map_ty: Type, update: Expr) -> Function {
    func(
        "set_in_map",
        sig(
            vec![
                param("t", map_ty.clone()),
                param("k", Type::UInt(64)),
                param("v", Type::UInt(8)),
            ],
            map_ty,
        ),
        body(vec![], update),
        0,
    )
}

#[test]
fn update_mapkey_on_table_renders_native_set() {
    let (mut prog, map_ty) = sui_map_program("table", "Table");
    add_function(&mut prog, 0, mapkey_update_fn(map_ty, mapkey_update(None)));
    let out = render_program(&prog).expect("renders");
    assert!(
        out.contains("(_root_.Table.set"),
        "missing native set:\n{out}"
    );
    assert!(out.contains("t k v)"), "operand order wrong:\n{out}");
}

#[test]
fn update_mapkey_on_vecmap_renders_native_set() {
    let (mut prog, map_ty) = sui_map_program("vec_map", "VecMap");
    add_function(&mut prog, 0, mapkey_update_fn(map_ty, mapkey_update(None)));
    let out = render_program(&prog).expect("renders");
    assert!(
        out.contains("(_root_.Vec_map.set"),
        "missing native set:\n{out}"
    );
}

#[test]
fn update_mapkey_on_non_map_base_is_a_loud_render_error() {
    let mut prog = empty_program();
    let plain = simple_struct(0, "NotAMap", vec![("x", Type::UInt(64))]);
    add_struct(&mut prog, 0, plain);
    let base_ty = Type::Struct {
        struct_id: 0,
        type_args: vec![],
    };
    add_function(&mut prog, 0, mapkey_update_fn(base_ty, mapkey_update(None)));
    // Per-function render errors land as a `sorry -- render fallback`
    // (loud at the lake / tests-run level), not a program-level Err.
    let out = render_program(&prog).expect("program still renders");
    assert!(
        out.contains("render fallback") && out.contains("non-native-map"),
        "expected loud sorry fallback:\n{out}"
    );
}

#[test]
fn update_mapkey_with_df_value_is_a_loud_render_error() {
    let (mut prog, map_ty) = sui_map_program("table", "Table");
    add_function(
        &mut prog,
        0,
        mapkey_update_fn(map_ty, mapkey_update(Some(VarId::from("dfv")))),
    );
    let out = render_program(&prog).expect("program still renders");
    assert!(
        out.contains("render fallback") && out.contains("df_value"),
        "expected loud sorry fallback:\n{out}"
    );
}

#[test]
fn residual_inner_return_is_a_loud_render_error() {
    let mut prog = empty_program();
    let inner = Expr::If {
        cond: Box::new(var("cond")),
        then_branch: Box::new(Block {
            stmts: Vec::new(),
            tail: BlockTail::Return(Box::new(Expr::Unit)),
        }),
        else_branch: Box::new(Block::just(Expr::Unit)),
    };
    add_function(
        &mut prog,
        0,
        func(
            "invalid_post_stage7",
            sig(vec![param("cond", Type::Bool)], Type::Unit),
            Block {
                stmts: vec![Stmt::Eval(inner)],
                tail: BlockTail::Value(Expr::Unit),
            },
            0,
        ),
    );

    let out = render_program(&prog).expect("program still renders");
    assert!(
        out.contains("render fallback")
            && out.contains("inner BlockTail::Return in eval context")
            && !out.contains("if cond then\n    ()"),
        "expected loud residual-Return fallback:\n{out}"
    );
}
