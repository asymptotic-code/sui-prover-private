//! Tests for `stage_07_dejumps::aborts_live_loop::run()` (phase 3b.5).
//!
//! The fixtures reproduce sui-system
//! `sui_system_state_inner::store_execution_time_estimates_v2`: an `.aborts`
//! loop chain whose `LoopBody` / `LoopAfter` sit under a DIRECT `Spec(Aborts)`
//! parent, whose result is consumed by a nested
//! `Call(cont, [Var.., Call(while_N, ..)])`, and whose `.after` merely returns
//! the accumulator -- no post-loop abort `Return` at all. That chain reached
//! the renderer returning `&mut SuiSystemStateInnerV2` under an `.aborts.`
//! name, so every abort face inside the loop was dropped.

use crate::ir::{
    Block, BlockTail, Const, Effects, Expr, Function, FunctionKind, Module, Param, Program,
    Signature, SpecKind, Stmt, Struct, Type, VarId,
};
use ethnum::U256;

use crate::stage_07_dejumps::aborts_live_loop;
use crate::stage_07_dejumps::option_aborts::ensure_aborts_types;

const ACC_STRUCT: usize = 100;

const SOURCE: usize = 0;
const ABORTS: usize = 1;
const HOLDER: usize = 2;
const CONT: usize = 3;
const WHILE: usize = 4;
const AFTER: usize = 5;

fn vid(s: &str) -> VarId {
    VarId::from(s)
}

fn lit_u64(n: u64) -> Expr {
    Expr::Const(Const::UInt {
        bits: 64,
        value: U256::from(n),
    })
}

fn param(name: &str, ty: Type) -> Param {
    Param {
        name: name.to_string(),
        var: vid(name),
        ty,
    }
}

fn func(
    name: &str,
    params: Vec<Param>,
    return_type: Type,
    body: Block,
    kind: FunctionKind,
) -> Function {
    Function {
        module: 0,
        name: name.to_string(),
        signature: Signature {
            type_params: Vec::new(),
            params,
            return_type,
        },
        body,
        kind,
        effects: Effects::CONSERVATIVE,
        explicit_pure: false,
    }
}

fn value(tail: Expr) -> Block {
    Block {
        stmts: vec![],
        tail: BlockTail::Value(tail),
    }
}

fn call(fun: usize, args: Vec<Expr>) -> Expr {
    Expr::Call {
        fun,
        type_args: Vec::new(),
        args,
    }
}

/// Empty program carrying the `Acc` accumulator struct plus the registered
/// `AbortResult` types. Returns the `&mut Acc` accumulator type, the canonical
/// `AbortResult` type, and a `NoAbort` value.
fn base_program() -> (Program, Type, Type, Expr) {
    let mut p = Program::default();
    p.modules.insert(
        0,
        Module {
            name: "m".to_string(),
            package_name: "p".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        },
    );
    p.structs.insert(
        ACC_STRUCT,
        Struct {
            module_id: 0,
            name: "Acc".to_string(),
            qualified_name: "p::m::Acc".to_string(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: None,
            is_native: false,
        },
    );
    let types = ensure_aborts_types(&mut p);
    let acc_struct = Type::Struct {
        struct_id: ACC_STRUCT,
        type_args: Vec::new(),
    };
    let acc_ty = Type::MutableRef {
        inner: Box::new(acc_struct.clone()),
        root: Box::new(acc_struct),
    };
    let abort_result = types.option_abort_code_type();
    let no_abort = types.make_none();
    (p, acc_ty, abort_result, no_abort)
}

/// The cluster-B chain. `extras` selects between the two slots the real
/// function carries: `true` gives slot 0's `cont(xs, while_0(..))` (one extra
/// arg threaded through the loop), `false` gives slot 1's `cont(while_1(..))`
/// (no extras). `after_body` is the `.after` body under test.
fn cluster_b_program(extras: bool, after_body: Block) -> (Program, Type) {
    let (mut p, acc_ty, abort_result, no_abort) = base_program();

    p.functions.insert(
        SOURCE,
        func(
            "f",
            vec![param("acc", acc_ty.clone()), param("xs", Type::UInt(64))],
            acc_ty.clone(),
            value(Expr::Var(vid("acc"))),
            FunctionKind::Source,
        ),
    );
    p.functions.insert(
        ABORTS,
        func(
            "f.aborts",
            vec![param("acc", acc_ty.clone()), param("xs", Type::UInt(64))],
            abort_result.clone(),
            value(call(
                HOLDER,
                vec![Expr::Var(vid("xs")), Expr::Var(vid("acc"))],
            )),
            FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target: SOURCE,
            },
        ),
    );

    // Holder: binds the loop's entry values, then tail-calls the continuation
    // with the loop result as its LAST argument.
    let loop_call = call(
        WHILE,
        vec![
            Expr::Var(vid("acc")),
            Expr::Var(vid("i0")),
            Expr::Var(vid("stop")),
        ],
    );
    let holder_tail = if extras {
        call(CONT, vec![Expr::Var(vid("xs")), loop_call])
    } else {
        call(CONT, vec![loop_call])
    };
    p.functions.insert(
        HOLDER,
        func(
            "f.aborts.cont_0",
            vec![param("xs", Type::UInt(64)), param("acc", acc_ty.clone())],
            abort_result.clone(),
            Block {
                stmts: vec![
                    Stmt::Let {
                        pattern: vec![Some(vid("i0"))],
                        value: lit_u64(0),
                    },
                    Stmt::Let {
                        pattern: vec![Some(vid("stop"))],
                        value: lit_u64(3),
                    },
                ],
                tail: BlockTail::Value(holder_tail),
            },
            FunctionKind::Synthetic,
        ),
    );

    let cont_params = if extras {
        vec![param("xs", Type::UInt(64)), param("acc", acc_ty.clone())]
    } else {
        vec![param("acc", acc_ty.clone())]
    };
    p.functions.insert(
        CONT,
        func(
            "f.aborts.cont_0.cont_0",
            cont_params,
            abort_result.clone(),
            value(no_abort),
            FunctionKind::Synthetic,
        ),
    );

    p.functions.insert(
        WHILE,
        func(
            "f.aborts.while_0",
            vec![
                param("acc", acc_ty.clone()),
                param("i", Type::UInt(64)),
                param("stop", Type::UInt(64)),
            ],
            acc_ty.clone(),
            value(Expr::If {
                cond: Box::new(Expr::Const(Const::Bool(true))),
                then_branch: Box::new(value(call(
                    WHILE,
                    vec![
                        Expr::Var(vid("acc")),
                        Expr::Var(vid("i")),
                        Expr::Var(vid("stop")),
                    ],
                ))),
                else_branch: Box::new(value(call(
                    AFTER,
                    vec![Expr::Var(vid("acc")), Expr::Var(vid("i"))],
                ))),
            }),
            FunctionKind::LoopBody {
                parent: ABORTS,
                slot: 0,
            },
        ),
    );
    p.functions.insert(
        AFTER,
        func(
            "f.aborts.while_0.after",
            vec![param("acc", acc_ty.clone()), param("i", Type::UInt(64))],
            acc_ty,
            after_body,
            FunctionKind::LoopAfter {
                parent: ABORTS,
                slot: 0,
            },
        ),
    );

    (p, abort_result)
}

/// `.after` as the misfiled chain leaves it: the accumulator, nothing else.
fn passthrough_after() -> Block {
    value(Expr::Var(vid("acc")))
}

fn no_abort() -> Expr {
    let (_, _, _, expr) = base_program();
    expr
}

fn args_of(e: &Expr, fun: usize) -> Vec<Expr> {
    match e {
        Expr::Call { fun: f, args, .. } if *f == fun => args.clone(),
        other => panic!("expected call to #{fun}, got {other:?}"),
    }
}

fn tail_expr(b: &Block) -> &Expr {
    match &b.tail {
        BlockTail::Value(e) => e,
        other => panic!("expected Value tail, got {other:?}"),
    }
}

fn param_names(p: &Program, fid: usize) -> Vec<String> {
    p.functions[&fid]
        .signature
        .params
        .iter()
        .map(|q| q.name.clone())
        .collect()
}

#[test]
fn passthrough_after_folds_and_retypes_the_chain() {
    // The cluster-B defeat: `.after` carries no post-loop abort `Return`, so
    // the nested fold's old gate skipped it and the world-threaded fold found
    // no tuple destructure to match. Both loop helpers then reached the
    // renderer accumulator-typed under an `.aborts.` name.
    let (mut p, abort_result) = cluster_b_program(true, passthrough_after());

    aborts_live_loop::run(&mut p).expect("run");

    assert_eq!(
        p.functions[&WHILE].signature.return_type, abort_result,
        "while_0 must be retyped to AbortResult"
    );
    assert_eq!(
        p.functions[&AFTER].signature.return_type, abort_result,
        ".after must be retyped to AbortResult"
    );

    // The cont's one extra arg is threaded through both helpers.
    assert_eq!(
        param_names(&p, WHILE),
        vec!["acc", "i", "stop", "__la_w0"],
        "while_0 gains the cont's extra as a trailing param"
    );
    assert_eq!(
        param_names(&p, AFTER),
        vec!["acc", "i", "__la_a0"],
        ".after gains the cont's extra as a trailing param"
    );

    // Both internal calls carry the new trailing arg.
    let Expr::If {
        then_branch,
        else_branch,
        ..
    } = tail_expr(&p.functions[&WHILE].body)
    else {
        panic!("expected an If tail in while_0");
    };
    assert_eq!(
        args_of(tail_expr(then_branch), WHILE).last(),
        Some(&Expr::Var(vid("__la_w0"))),
        "the loop self-call is threaded"
    );
    assert_eq!(
        args_of(tail_expr(else_branch), AFTER).last(),
        Some(&Expr::Var(vid("__la_w0"))),
        "the `.after` call is threaded"
    );

    // `.after`'s accumulator leaf becomes the continuation call.
    assert_eq!(
        args_of(tail_expr(&p.functions[&AFTER].body), CONT),
        vec![Expr::Var(vid("__la_a0")), Expr::Var(vid("acc"))],
        ".after's accumulator leaf must call the continuation"
    );

    // The holder's `cont(extra.., while_0(..))` collapses onto the loop.
    assert_eq!(
        args_of(tail_expr(&p.functions[&HOLDER].body), WHILE),
        vec![
            Expr::Var(vid("acc")),
            Expr::Var(vid("i0")),
            Expr::Var(vid("stop")),
            Expr::Var(vid("xs")),
        ],
        "the holder tail-calls the loop with the extras appended"
    );
}

#[test]
fn passthrough_after_folds_with_no_extra_args() {
    // Slot 1 of the same function: the continuation consumes the accumulator
    // alone, so the fold threads nothing and only retypes.
    let (mut p, abort_result) = cluster_b_program(false, passthrough_after());

    aborts_live_loop::run(&mut p).expect("run");

    assert_eq!(p.functions[&WHILE].signature.return_type, abort_result);
    assert_eq!(p.functions[&AFTER].signature.return_type, abort_result);
    assert_eq!(param_names(&p, WHILE), vec!["acc", "i", "stop"]);
    assert_eq!(param_names(&p, AFTER), vec!["acc", "i"]);
    assert_eq!(
        args_of(tail_expr(&p.functions[&AFTER].body), CONT),
        vec![Expr::Var(vid("acc"))]
    );
    assert_eq!(
        args_of(tail_expr(&p.functions[&HOLDER].body), WHILE),
        vec![
            Expr::Var(vid("acc")),
            Expr::Var(vid("i0")),
            Expr::Var(vid("stop")),
        ]
    );
}

#[test]
fn after_with_post_loop_abort_return_still_folds() {
    // The shape the nested fold was written for (cetus-dlmm
    // `bin::add_bin_if_absent`): `.after` holds a post-loop abort exit. It
    // keeps first refusal, so widening the fallback must not disturb it.
    let after = Block {
        stmts: vec![],
        tail: BlockTail::Value(Expr::If {
            cond: Box::new(Expr::Const(Const::Bool(true))),
            then_branch: Box::new(Block {
                stmts: vec![],
                tail: BlockTail::Return(Box::new(no_abort())),
            }),
            else_branch: Box::new(value(Expr::Var(vid("acc")))),
        }),
    };
    let (mut p, abort_result) = cluster_b_program(true, after);

    aborts_live_loop::run(&mut p).expect("run");

    assert_eq!(p.functions[&WHILE].signature.return_type, abort_result);
    assert_eq!(p.functions[&AFTER].signature.return_type, abort_result);
    // Only the accumulator leaf is wrapped; the abort `Return` is untouched.
    let Expr::If {
        then_branch,
        else_branch,
        ..
    } = tail_expr(&p.functions[&AFTER].body)
    else {
        panic!("expected an If tail in `.after`");
    };
    assert!(
        matches!(then_branch.tail, BlockTail::Return(_)),
        "the abort exit must stay a Return"
    );
    assert_eq!(
        args_of(tail_expr(else_branch), CONT),
        vec![Expr::Var(vid("__la_a0")), Expr::Var(vid("acc"))]
    );
}

#[test]
fn two_consumption_sites_decline() {
    // The uniqueness guard is what makes the rewrite well-defined; widening
    // the fallback must not weaken it.
    let (mut p, _abort_result) = cluster_b_program(true, passthrough_after());
    let acc_ty = p.functions[&SOURCE].signature.params[0].ty.clone();
    let second_holder = p.functions[&HOLDER].clone();
    p.functions.insert(
        6,
        func(
            "f.aborts.cont_1",
            vec![param("xs", Type::UInt(64)), param("acc", acc_ty)],
            second_holder.signature.return_type.clone(),
            second_holder.body.clone(),
            FunctionKind::Synthetic,
        ),
    );
    let before = p.functions[&WHILE].signature.return_type.clone();

    aborts_live_loop::run(&mut p).expect("run");

    assert_eq!(
        p.functions[&WHILE].signature.return_type, before,
        "a loop consumed twice must be left alone"
    );
    assert_eq!(param_names(&p, WHILE), vec!["acc", "i", "stop"]);
}

#[test]
fn already_abort_result_after_is_untouched() {
    let (mut p, abort_result) = cluster_b_program(true, passthrough_after());
    p.functions.get_mut(&AFTER).unwrap().signature.return_type = abort_result;
    let before = p.functions[&HOLDER].body.clone();

    aborts_live_loop::run(&mut p).expect("run");

    assert_eq!(param_names(&p, WHILE), vec!["acc", "i", "stop"]);
    assert_eq!(
        p.functions[&HOLDER].body, before,
        "an already-folded slot must not be rewritten twice"
    );
}

#[test]
fn collapsed_abort_value_leaf_is_not_routed_into_the_continuation() {
    // blast `allocation::add_protocol`: two `fold!`s joined by `&&` inside one
    // `assert!`. The second loop's `.after` ends in `vector::destroy_empty`,
    // whose callee-abort check `return_collapse` leaves as a VALUE leaf
    // (`Aborted(c) => Aborted c`) beside the accumulator arm. Wrapping it too
    // passed an `AbortResult` as the continuation's accumulator argument.
    let (mut probe, _, _, _) = base_program();
    let aborted = ensure_aborts_types(&mut probe).make_some(lit_u64(0));
    let after = value(Expr::If {
        cond: Box::new(Expr::Const(Const::Bool(true))),
        then_branch: Box::new(value(Expr::Var(vid("acc")))),
        else_branch: Box::new(value(aborted.clone())),
    });
    let (mut p, abort_result) = cluster_b_program(true, after);

    aborts_live_loop::run(&mut p).expect("run");

    assert_eq!(p.functions[&AFTER].signature.return_type, abort_result);
    let Expr::If {
        then_branch,
        else_branch,
        ..
    } = tail_expr(&p.functions[&AFTER].body)
    else {
        panic!("expected an If tail in `.after`");
    };
    assert_eq!(
        args_of(tail_expr(then_branch), CONT),
        vec![Expr::Var(vid("__la_a0")), Expr::Var(vid("acc"))],
        "the accumulator leaf must call the continuation"
    );
    assert_eq!(
        tail_expr(else_branch),
        &aborted,
        "an abort verdict is already the retyped `.after`'s result"
    );
}
