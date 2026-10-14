//! Phase 1 (`aborts_variant`) tests.
//!
//! Slice 1: verify per-tail rewrites (Value, Return, Abort) and
//! sibling `.aborts` function emission. No splice patterns yet.

use crate::ir::builder::ProverFnIds;
use crate::ir::path::PathStep;
use crate::ir::{
    AbortPayloadMode, AbortProvenance, Block, BlockTail, Expr, Function, FunctionKind, Module,
    NativeDecl, Param, Program, Signature, SpecKind, Stmt, Struct, Type, VarId,
};
use ethnum::U256;
use std::collections::BTreeMap;

use crate::stage_07_dejumps::aborts_variant;
use crate::stage_07_dejumps::option_aborts::{ABORT_CODE_QUALIFIED_NAME, OPTION_QUALIFIED_NAME};

fn module() -> Module {
    Module {
        name: "m".to_string(),
        package_name: "p".to_string(),
        address: String::new(),
        required_imports: Vec::new(),
        is_native: false,
    }
}

fn param(name: &str, ty: Type) -> Param {
    Param {
        name: name.to_string(),
        var: VarId::from(name),
        ty,
    }
}

fn sig(params: Vec<Param>, return_type: Type) -> Signature {
    Signature {
        type_params: Vec::new(),
        params,
        return_type,
    }
}

fn func(name: &str, sig: Signature, body: Block, kind: FunctionKind) -> Function {
    Function {
        module: 0,
        name: name.to_string(),
        signature: sig,
        body,
        kind,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    }
}

fn program_with(funcs: Vec<(usize, Function)>) -> Program {
    let mut p = Program::default();
    p.modules.insert(0, module());
    for (id, f) in funcs {
        p.functions.insert(id, f);
    }
    p
}

fn lit_u64(n: u64) -> Expr {
    Expr::Const(crate::ir::Const::UInt {
        bits: 64,
        value: U256::from(n),
    })
}

fn body_value(tail: Expr) -> Block {
    Block {
        stmts: vec![],
        tail: BlockTail::Value(tail),
    }
}

fn body_return(value: Expr) -> Block {
    Block {
        stmts: vec![],
        tail: BlockTail::Return(Box::new(value)),
    }
}

fn body_abort(code: Expr) -> Block {
    Block {
        stmts: vec![],
        tail: BlockTail::Abort {
            code: Box::new(code),
        },
    }
}

fn one_fn_program(body: Block) -> Program {
    let f = func(
        "f",
        sig(vec![param("x", Type::UInt(64))], Type::UInt(64)),
        body,
        FunctionKind::Source,
    );
    program_with(vec![(0, f)])
}

/// Find the materialized `f.aborts` companion fid via its
/// `FunctionKind::Spec { kind: Aborts, target: source_fid }`.
fn find_aborts(p: &Program, source_fid: usize) -> Option<usize> {
    p.functions
        .iter()
        .find(|(_, f)| {
            matches!(
                f.kind,
                FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    target,
                } if target == source_fid
            )
        })
        .map(|(id, _)| *id)
}

/// Build the pre-strip body map `materialise` now takes (in production
/// it is the source bodies snapshotted before `collect_predicates` strips
/// the `prover::*` calls; in these unit tests nothing strips, so it is
/// just the current source/test bodies).
fn pre_strip_bodies(p: &Program) -> BTreeMap<usize, Block> {
    p.functions
        .iter()
        .filter(|(_, f)| matches!(f.kind, FunctionKind::Source | FunctionKind::Test { .. }))
        .map(|(id, f)| (*id, f.body.clone()))
        .collect()
}

#[test]
fn function_tail_value_becomes_value_none() {
    let mut p = one_fn_program(body_value(lit_u64(42)));
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    let aborts_fid = find_aborts(&p, 0).expect(".aborts companion emitted");
    let aborts = &p.functions[&aborts_fid];

    // Body's tail is Value(Pack(Option<MoveAbortCode>, None)).
    match &aborts.body.tail {
        BlockTail::Value(Expr::Pack {
            variant: Some(tag),
            fields,
            ..
        }) => {
            assert_eq!(
                *tag,
                crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG,
                "function-tail Value rewrites to Option's None variant"
            );
            assert!(fields.is_empty(), "None variant has no fields");
        }
        other => panic!("expected Value(Pack(None, [])), got {other:?}"),
    }
}

#[test]
fn return_becomes_return_none() {
    // f.body = { stmts: [Eval(If{..., then: Return(99), else: Value(unit)})], tail: Value(42) }
    let inner_if = Expr::If {
        cond: Box::new(Expr::Var(VarId::from("x"))),
        then_branch: Box::new(body_return(lit_u64(99))),
        else_branch: Box::new(body_value(Expr::Unit)),
    };
    let body = Block {
        stmts: vec![Stmt::Eval(inner_if)],
        tail: BlockTail::Value(lit_u64(42)),
    };
    let mut p = one_fn_program(body);
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    let aborts_fid = find_aborts(&p, 0).expect(".aborts companion emitted");
    let aborts = &p.functions[&aborts_fid];

    // Find the inner Return tail — phase 1's per-tail rewrite
    // converts it to Return(None). (Normalize pass is currently
    // disabled — see comment in materialise() about task #26.)
    let stmt = &aborts.body.stmts[0];
    let inner_if = match stmt {
        Stmt::Eval(Expr::If { then_branch, .. }) => then_branch,
        other => panic!("expected Eval(If), got {other:?}"),
    };
    match &inner_if.tail {
        BlockTail::Return(payload) => match payload.as_ref() {
            Expr::Pack {
                variant: Some(tag),
                fields,
                ..
            } => {
                assert_eq!(
                    *tag,
                    crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG,
                    "inner Return rewrites to Return(None)"
                );
                assert!(fields.is_empty(), "None has no fields");
            }
            other => panic!("expected Pack(None), got {other:?}"),
        },
        other => panic!("expected Return tail, got {other:?}"),
    }
}

#[test]
fn abort_becomes_return_some_code() {
    // f.body = { tail: Abort{ code: 42 } }
    let mut p = one_fn_program(body_abort(lit_u64(42)));
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    let aborts_fid = find_aborts(&p, 0).expect(".aborts companion emitted");
    let aborts = &p.functions[&aborts_fid];

    // Tail should be Return(Some(MoveAbortCode { code: 42 })).
    match &aborts.body.tail {
        BlockTail::Return(payload) => match payload.as_ref() {
            Expr::Pack {
                variant: Some(some_tag),
                fields: outer_fields,
                ..
            } => {
                assert_eq!(
                    *some_tag,
                    crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG,
                    "Abort rewrites to Return wrapping Some(...)"
                );
                assert_eq!(outer_fields.len(), 1, "Some has one field");
                // Inner: Pack(MoveAbortCode, None, [42]).
                match &outer_fields[0] {
                    Expr::Pack {
                        variant: None,
                        fields: inner_fields,
                        ..
                    } => {
                        assert_eq!(inner_fields.len(), 1, "MoveAbortCode struct has one field");
                        assert_eq!(inner_fields[0], lit_u64(42));
                    }
                    other => panic!("expected Pack(MoveAbortCode, [code]), got {other:?}"),
                }
            }
            other => panic!("expected Pack(Some(MoveAbortCode)), got {other:?}"),
        },
        other => panic!("expected Return tail, got {other:?}"),
    }
}

#[test]
fn aborts_companion_signature_matches() {
    let mut p = one_fn_program(body_value(lit_u64(42)));
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    let aborts_fid = find_aborts(&p, 0).expect(".aborts companion emitted");
    let aborts = &p.functions[&aborts_fid];
    let source = &p.functions[&0];

    // Same params as source.
    assert_eq!(aborts.signature.params, source.signature.params);
    // Same type params.
    assert_eq!(aborts.signature.type_params, source.signature.type_params);
    // Name suffix.
    assert_eq!(aborts.name, "f.aborts");
    // Kind = Spec(Aborts, target=0).
    assert!(matches!(
        aborts.kind,
        FunctionKind::Spec {
            kind: SpecKind::Aborts,
            target: 0
        }
    ));
    // Effects = PURE.
    assert_eq!(aborts.effects, crate::ir::Effects::PURE);
}

#[test]
fn synthetic_structs_registered() {
    let mut p = one_fn_program(body_value(lit_u64(42)));
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    // Both Option and MoveAbortCode should now exist in program.structs.
    let has_option = p
        .structs
        .values()
        .any(|s| s.qualified_name == OPTION_QUALIFIED_NAME);
    let has_abort_code = p
        .structs
        .values()
        .any(|s| s.qualified_name == ABORT_CODE_QUALIFIED_NAME);
    assert!(has_option, "Option<T> registered");
    assert!(has_abort_code, "MoveAbortCode registered");
}

#[test]
fn idempotent_on_already_processed() {
    let mut p = one_fn_program(body_value(lit_u64(42)));
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("first run");
    let before = p.functions.len();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("second run");
    let after = p.functions.len();
    assert_eq!(
        before, after,
        "second run on already-processed program is a no-op"
    );
}

#[test]
fn break_continue_value_unchanged() {
    // f.body has an inner While whose body has an inner If with one
    // arm Break and one arm Continue. Both tails should survive
    // phase 1 unchanged (phase 2's loop extraction will lower them).
    let inner_if = Expr::If {
        cond: Box::new(Expr::Var(VarId::from("x"))),
        then_branch: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Break {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        }),
        else_branch: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Continue {
                level: 0,
                value: Box::new(Expr::Unit),
            },
        }),
    };
    let while_expr = Expr::While {
        header: Box::new(Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Unit),
        }),
        cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
        body: Box::new(Block {
            stmts: vec![Stmt::Eval(inner_if)],
            tail: BlockTail::Value(Expr::Unit),
        }),
        iter_locals: Vec::new(),
        header_exit_locals: Vec::new(),
        live_out: vec![],
    };
    let body = Block {
        stmts: vec![Stmt::Eval(while_expr)],
        tail: BlockTail::Value(lit_u64(42)),
    };

    let mut p = one_fn_program(body);
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    let aborts_fid = find_aborts(&p, 0).expect(".aborts companion emitted");
    let aborts = &p.functions[&aborts_fid];

    // Drill down to the inner If's arm tails.
    let while_expr = match &aborts.body.stmts[0] {
        Stmt::Eval(w) => w,
        _ => panic!("expected Eval(While)"),
    };
    let inner_block = match while_expr {
        Expr::While { body, .. } => body.as_ref(),
        _ => panic!("expected While"),
    };
    let inner_if = match &inner_block.stmts[0] {
        Stmt::Eval(if_e) => if_e,
        _ => panic!("expected Eval(If)"),
    };
    let (then_branch, else_branch) = match inner_if {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => (then_branch.as_ref(), else_branch.as_ref()),
        _ => panic!("expected If"),
    };

    assert!(
        matches!(&then_branch.tail, BlockTail::Break { level: 0, .. }),
        "Break tail unchanged in .aborts variant"
    );
    assert!(
        matches!(&else_branch.tail, BlockTail::Continue { level: 0, .. }),
        "Continue tail unchanged in .aborts variant"
    );
}

// ---------------------------------------------------------------------------
// Slice 2 -- sub-expression splices
// ---------------------------------------------------------------------------

/// Build a two-function program where `g` has an `.aborts` companion
/// pre-registered and `f` calls `g`. Returns the program.
fn two_fn_program_with_callee_aborts(call_in_f_body: Block) -> Program {
    let g = func(
        "g",
        sig(vec![param("y", Type::UInt(64))], Type::UInt(64)),
        body_value(lit_u64(0)),
        FunctionKind::Source,
    );
    let f = func(
        "f",
        sig(vec![param("x", Type::UInt(64))], Type::UInt(64)),
        call_in_f_body,
        FunctionKind::Source,
    );
    program_with(vec![(0, g), (1, f)])
}

/// Look up `.aborts` companion fid given a source target fid.
fn aborts_of(p: &Program, target: usize) -> Option<usize> {
    p.functions.iter().find_map(|(id, fn_)| {
        if let FunctionKind::Spec {
            kind: SpecKind::Aborts,
            target: t,
        } = fn_.kind
        {
            if t == target {
                return Some(*id);
            }
        }
        None
    })
}

#[test]
fn callee_aborts_splice_at_eval_position() {
    // f.body = { stmts: [Eval(Call(g, [x]))], tail: Value(42) }
    let f_body = Block {
        stmts: vec![Stmt::Eval(Expr::Call {
            fun: 0,
            type_args: vec![],
            args: vec![Expr::Var(VarId::from("x"))],
        })],
        tail: BlockTail::Value(lit_u64(42)),
    };
    let mut p = two_fn_program_with_callee_aborts(f_body);
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    let g_aborts_fid = aborts_of(&p, 0).expect("g.aborts");
    let f_aborts_fid = aborts_of(&p, 1).expect("f.aborts");
    let f_aborts = &p.functions[&f_aborts_fid];

    // f.aborts.body should be: stmts: [Let { pat: [__c_0], value:
    // Call(g.aborts, [x]) }], tail: Value(Match { selector: Var(__c_0),
    // cases: [None -> Value(None), Some(_) -> Return(Var(__c_0))] }).
    assert_eq!(
        f_aborts.body.stmts.len(),
        1,
        "Eval splice replaces Eval with a single Let __c"
    );
    match &f_aborts.body.stmts[0] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern.len(), 1);
            assert!(pattern[0].is_some(), "pattern binds __c");
            match value {
                Expr::Call { fun, args, .. } => {
                    assert_eq!(*fun, g_aborts_fid, "Call routed to g.aborts");
                    assert_eq!(args.len(), 1);
                    assert_eq!(args[0], Expr::Var(VarId::from("x")));
                }
                other => panic!("expected Call(g.aborts), got {other:?}"),
            }
        }
        other => panic!("expected Let __c, got {other:?}"),
    }

    // Verify the splice tail: Match on __c.
    match &f_aborts.body.tail {
        BlockTail::Value(Expr::Match { cases, .. }) => {
            assert_eq!(cases.len(), 2);
            let none_arm = cases
                .iter()
                .find(|a| a.variant == crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG)
                .expect("None arm");
            let some_arm = cases
                .iter()
                .find(|a| a.variant == crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG)
                .expect("Some arm");
            // None arm body: Block { stmts: [], tail: Value(None) }
            // (the continuation — original tail rewritten by per-tail
            // pass to Value(None)).
            assert!(none_arm.body.stmts.is_empty(), "None arm continuation");
            assert!(
                matches!(&none_arm.body.tail, BlockTail::Value(_)),
                "None arm tail is Value"
            );
            // Some arm body: Block { stmts: [], tail: Return(Var(__c)) }
            // Return is an early-exit terminator -- it contributes no
            // value type to the Match. The surrounding code sees the
            // NoAbort arm's source-T type. The Return's payload is
            // propagated to the function tail by task #26 (inner-Return
            // lift); until that lands, the renderer sorry's it.
            assert!(some_arm.body.stmts.is_empty(), "Some arm body");
            assert!(
                matches!(&some_arm.body.tail, BlockTail::Return(_)),
                "Some arm propagates abort as Return (early-exit)"
            );
        }
        other => panic!("expected Value(Match), got {other:?}"),
    }
}

#[test]
fn callee_aborts_splice_inside_discarded_if_arm() {
    let call_g = Expr::Call {
        fun: 0,
        type_args: vec![],
        args: vec![Expr::Var(VarId::from("x"))],
    };
    let f_body = body_value(Expr::If {
        cond: Box::new(Expr::Var(VarId::from("cond"))),
        then_branch: Box::new(Block {
            stmts: vec![Stmt::Eval(call_g)],
            tail: BlockTail::Value(lit_u64(7)),
        }),
        else_branch: Box::new(body_value(lit_u64(8))),
    });
    let g = func(
        "g",
        sig(vec![param("y", Type::UInt(64))], Type::UInt(64)),
        body_value(lit_u64(0)),
        FunctionKind::Source,
    );
    let f = func(
        "f",
        sig(
            vec![param("x", Type::UInt(64)), param("cond", Type::Bool)],
            Type::UInt(64),
        ),
        f_body,
        FunctionKind::Source,
    );
    let mut p = program_with(vec![(0, g), (1, f)]);
    let preds = pre_strip_bodies(&p);
    aborts_variant::materialise(&mut p, &preds, &ProverFnIds::default()).expect("materialise");

    let g_aborts_fid = aborts_of(&p, 0).expect("g.aborts");
    let f_aborts_fid = aborts_of(&p, 1).expect("f.aborts");
    let BlockTail::Value(Expr::If { then_branch, .. }) = &p.functions[&f_aborts_fid].body.tail
    else {
        panic!("expected f.aborts to preserve the source if")
    };
    assert_eq!(then_branch.stmts.len(), 1);
    assert!(matches!(
        &then_branch.stmts[0],
        Stmt::Let {
            value: Expr::Call { fun, .. },
            ..
        } if *fun == g_aborts_fid
    ));
    let BlockTail::Value(Expr::Match { cases, .. }) = &then_branch.tail else {
        panic!("expected the discarded call to become an abort guard")
    };
    let no_abort = cases
        .iter()
        .find(|arm| arm.variant == crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG)
        .expect("NoAbort arm");
    let aborted = cases
        .iter()
        .find(|arm| arm.variant == crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG)
        .expect("Aborted arm");
    assert!(matches!(
        &no_abort.body.tail,
        BlockTail::Value(Expr::Pack {
            variant: Some(tag),
            ..
        }) if *tag == crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG
    ));
    assert!(matches!(&aborted.body.tail, BlockTail::Return(_)));

    let rendered = crate::render::render_program(&p).expect("render");
    let source_body = rendered
        .split_once("def f ")
        .expect("f definition")
        .1
        .split_once("\n\n")
        .expect("end of f definition")
        .0;
    let aborts_body = rendered
        .split_once("def f.aborts ")
        .expect("f.aborts definition")
        .1
        .split_once("\n\n")
        .expect("end of f.aborts definition")
        .0;
    assert!(
        !source_body.contains("g x"),
        "the discarded value call must be absent from f:\n{source_body}"
    );
    assert!(
        aborts_body.contains("g.aborts x"),
        "f.aborts must retain the discarded callee's abort guard:\n{aborts_body}"
    );
}

#[test]
fn callee_aborts_splice_at_let_position() {
    // f.body = { stmts: [Let { pat: [v], value: Call(g, [x]) }],
    //            tail: Value(Var(v)) }
    let f_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(VarId::from("v"))],
            value: Expr::Call {
                fun: 0,
                type_args: vec![],
                args: vec![Expr::Var(VarId::from("x"))],
            },
        }],
        tail: BlockTail::Value(Expr::Var(VarId::from("v"))),
    };
    let mut p = two_fn_program_with_callee_aborts(f_body);
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    let g_aborts_fid = aborts_of(&p, 0).expect("g.aborts");
    let f_aborts_fid = aborts_of(&p, 1).expect("f.aborts");
    let f_aborts = &p.functions[&f_aborts_fid];

    // f.aborts.body.stmts should have one Let __c stmt; the
    // continuation in the Match's None arm should retain the
    // original Let { pat: [v], value: Call(g, ..) }.
    assert_eq!(
        f_aborts.body.stmts.len(),
        1,
        "outer block has just the abort-check Let"
    );
    match &f_aborts.body.stmts[0] {
        Stmt::Let {
            value: Expr::Call { fun, .. },
            ..
        } => {
            assert_eq!(*fun, g_aborts_fid);
        }
        other => panic!("expected Let __c = Call(g.aborts), got {other:?}"),
    }

    // None arm should contain the original Let { pat: [v], value: Call(g, ..) }.
    let none_arm_body = match &f_aborts.body.tail {
        BlockTail::Value(Expr::Match { cases, .. }) => cases
            .iter()
            .find(|a| a.variant == crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG)
            .map(|a| &a.body)
            .expect("None arm"),
        other => panic!("expected Value(Match), got {other:?}"),
    };
    assert_eq!(
        none_arm_body.stmts.len(),
        1,
        "None arm preserves the original Let"
    );
    match &none_arm_body.stmts[0] {
        Stmt::Let {
            pattern,
            value: Expr::Call { fun, .. },
        } => {
            assert_eq!(pattern.len(), 1);
            assert_eq!(pattern[0], Some(VarId::from("v")));
            assert_eq!(
                *fun, 0,
                "original Call to source g is preserved (NOT rewritten)"
            );
        }
        other => panic!("expected preserved Let v=Call(g), got {other:?}"),
    }
}

/// S6 tripwire: an abortable callee `g` in a VALUE / ARGUMENT position
/// (here a `BinOp` operand) is unguardable by the callee-aborts splice,
/// so `materialise` must fail loud with `ValuePositionAbort` instead of
/// silently dropping `g`'s abort verdict. This shape is exactly the
/// latent ANF gap: stage_06 let-inline never folds a non-total op into a
/// value position, so it cannot arise on well-formed input -- we build
/// it directly via IR to prove the tripwire fires.
#[test]
fn value_position_abortable_call_trips_guard() {
    // f.body = { stmts: [Let { pat: [v], value: Call(g,[x]) + 1 }],
    //            tail: Value(Var(v)) }
    // g (fid 0) is CONSERVATIVE (can abort) with an .aborts companion.
    let f_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(VarId::from("v"))],
            value: Expr::BinOp {
                op: crate::ir::BinOp::Add,
                lhs: Box::new(Expr::Call {
                    fun: 0,
                    type_args: vec![],
                    args: vec![Expr::Var(VarId::from("x"))],
                }),
                rhs: Box::new(lit_u64(1)),
            },
        }],
        tail: BlockTail::Value(Expr::Var(VarId::from("v"))),
    };
    let mut p = two_fn_program_with_callee_aborts(f_body);
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    let err = aborts_variant::materialise(&mut p, &preds, &ids)
        .expect_err("value-position abortable callee must trip the tripwire");
    assert_eq!(
        err,
        crate::stage_07_dejumps::Stage7Error::ValuePositionAbort { callee: 0 },
        "tripwire reports the offending source callee g (fid 0)"
    );
}

/// The tripwire is totality-gated: a TOTAL callee `g` (`Effects::PURE`)
/// can never abort, so `g.aborts` is always `None` and a value-position
/// `Call(g)` is sound (stage_06 legitimately folds total calls into
/// value positions). The same shape as above, but with a total `g`,
/// must NOT trip the tripwire.
#[test]
fn value_position_total_call_does_not_trip_guard() {
    let g = Function {
        module: 0,
        name: "g".to_string(),
        signature: sig(vec![param("y", Type::UInt(64))], Type::UInt(64)),
        body: body_value(lit_u64(0)),
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
    };
    let f_body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(VarId::from("v"))],
            value: Expr::BinOp {
                op: crate::ir::BinOp::Add,
                lhs: Box::new(Expr::Call {
                    fun: 0,
                    type_args: vec![],
                    args: vec![Expr::Var(VarId::from("x"))],
                }),
                rhs: Box::new(lit_u64(1)),
            },
        }],
        tail: BlockTail::Value(Expr::Var(VarId::from("v"))),
    };
    let f = func(
        "f",
        sig(vec![param("x", Type::UInt(64))], Type::UInt(64)),
        f_body,
        FunctionKind::Source,
    );
    let mut p = program_with(vec![(0, g), (1, f)]);
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids)
        .expect("total value-position callee must NOT trip the tripwire");
}

#[test]
fn callee_aborts_no_splice_when_callee_has_no_aborts_companion() {
    // Single-function program: f calls something (fid 99) that has
    // no .aborts companion. The splice should NOT fire.
    let f_body = Block {
        stmts: vec![Stmt::Eval(Expr::Call {
            fun: 99,
            type_args: vec![],
            args: vec![Expr::Var(VarId::from("x"))],
        })],
        tail: BlockTail::Value(lit_u64(42)),
    };
    let mut p = one_fn_program(f_body);
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    let f_aborts_fid = aborts_of(&p, 0).expect("f.aborts");
    let f_aborts = &p.functions[&f_aborts_fid];

    // No splice — original Eval(Call) stays in stmts; tail is the
    // per-tail-rewritten Value(None).
    assert_eq!(f_aborts.body.stmts.len(), 1);
    assert!(matches!(
        &f_aborts.body.stmts[0],
        Stmt::Eval(Expr::Call { fun: 99, .. })
    ));
    assert!(
        matches!(&f_aborts.body.tail, BlockTail::Value(Expr::Pack { variant: Some(t), .. }) if *t == crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG)
    );
}

#[test]
fn assert_calls_lower_in_place() {
    // f.body has `eval prover::asserts(p)` in statement position;
    // materialise lowers it IN PLACE to `if !p { return Some(abort) }
    // else { <rest> }` (branch-preserving), not collected to the tail.
    let asserts_fid: usize = 100;
    let pred_expr = Expr::Var(VarId::from("assertion_holds"));
    let body = Block {
        stmts: vec![Stmt::Eval(Expr::Call {
            fun: asserts_fid,
            type_args: vec![],
            args: vec![pred_expr.clone()],
        })],
        tail: BlockTail::Value(lit_u64(42)),
    };
    let mut p = one_fn_program(body);
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds {
        asserts: Some(asserts_fid),
        ..ProverFnIds::default()
    };
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    let f_aborts_fid = find_aborts(&p, 0).expect("f.aborts");
    let f_aborts = &p.functions[&f_aborts_fid];

    // Body should be: { stmts: [], tail: Value(If { cond: !p,
    // then: just(Return(Some(assert_code))), else: <wrapped original> }) }
    match &f_aborts.body.tail {
        BlockTail::Value(Expr::If {
            cond,
            then_branch,
            else_branch: _,
        }) => {
            // cond is UnOp(Not, pred_expr).
            match cond.as_ref() {
                Expr::UnOp {
                    op: crate::ir::ops::UnOp::Not,
                    operand,
                } => {
                    assert_eq!(**operand, pred_expr);
                }
                other => panic!("expected Not(p), got {other:?}"),
            }
            // then is a Return(Some(MoveAbortCode)).
            match &then_branch.tail {
                BlockTail::Return(payload) => match payload.as_ref() {
                    Expr::Pack {
                        variant: Some(tag), ..
                    } => {
                        assert_eq!(
                            *tag,
                            crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG,
                            "assert guard returns Some(...)"
                        );
                    }
                    other => panic!("expected Pack(Some), got {other:?}"),
                },
                other => panic!("expected Return tail in then-arm, got {other:?}"),
            }
        }
        other => panic!("expected Value(If) wrapping body, got {other:?}"),
    }
}

#[test]
fn multiple_callee_aborts_in_sequence() {
    // f.body = { stmts: [Eval(Call(g, ..)), Eval(Call(g, ..))], tail: Value(..) }
    // After splice, expect two nested Match shapes (one per Call).
    let g = func(
        "g",
        sig(vec![param("y", Type::UInt(64))], Type::UInt(64)),
        body_value(lit_u64(0)),
        FunctionKind::Source,
    );
    let call_g = Expr::Call {
        fun: 0,
        type_args: vec![],
        args: vec![Expr::Var(VarId::from("x"))],
    };
    let f_body = Block {
        stmts: vec![Stmt::Eval(call_g.clone()), Stmt::Eval(call_g.clone())],
        tail: BlockTail::Value(lit_u64(42)),
    };
    let f = func(
        "f",
        sig(vec![param("x", Type::UInt(64))], Type::UInt(64)),
        f_body,
        FunctionKind::Source,
    );
    let mut p = program_with(vec![(0, g), (1, f)]);
    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    let f_aborts_fid = aborts_of(&p, 1).expect("f.aborts");
    let f_aborts = &p.functions[&f_aborts_fid];

    // Outer block: stmts has one Let __c_0 = Call(g.aborts); tail
    // is Value(Match { ..., None -> <continuation with second
    // splice>, Some -> Return(__c_0) }).
    assert_eq!(f_aborts.body.stmts.len(), 1);
    let outer_match_cases = match &f_aborts.body.tail {
        BlockTail::Value(Expr::Match { cases, .. }) => cases,
        other => panic!("expected outer Value(Match), got {other:?}"),
    };
    let outer_none_arm_body = outer_match_cases
        .iter()
        .find(|a| a.variant == crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG)
        .map(|a| &a.body)
        .expect("outer None arm");
    // Inner block (the continuation): stmts has Let __c_1 = Call(g.aborts);
    // tail is Value(Match { ..., None -> Value(None), Some -> Return(__c_1) }).
    assert_eq!(
        outer_none_arm_body.stmts.len(),
        1,
        "inner block has the second Let __c"
    );
    assert!(
        matches!(
            &outer_none_arm_body.tail,
            BlockTail::Value(Expr::Match { .. })
        ),
        "inner block tail is the second Match"
    );
}

#[test]
fn callee_aborts_wraps_bool_native_to_option() {
    // Simulate a stage-10-emitted scenario: a native main fn (id=10)
    // exists with a Bool-returning .aborts native (id=11,
    // spec_target=10). When f calls the main native, the splice
    // should wrap the Bool result into Option<MoveAbortCode>.
    let f = func(
        "f",
        sig(vec![param("x", Type::UInt(64))], Type::UInt(64)),
        Block {
            stmts: vec![Stmt::Eval(Expr::Call {
                fun: 10,
                type_args: vec![],
                args: vec![Expr::Var(VarId::from("x"))],
            })],
            tail: BlockTail::Value(lit_u64(42)),
        },
        FunctionKind::Source,
    );
    let mut p = program_with(vec![(0, f)]);

    // Register the native main fn at id=10 and its Bool-returning
    // .aborts companion at id=11.
    use crate::ir::NativeDecl;
    p.natives.decls.insert(
        10,
        NativeDecl {
            module: 0,
            name: "BoundedU64_add".to_string(),
            signature: Signature {
                type_params: vec![],
                params: vec![Param {
                    name: "a".into(),
                    var: VarId::from("a"),
                    ty: Type::UInt(64),
                }],
                return_type: Type::UInt(64),
            },
            effects: crate::ir::Effects::PURE,
            explicit_pure: true,
            is_framework: true,
            spec_target: None,
            user_native: None,
        },
    );
    p.natives.decls.insert(
        11,
        NativeDecl {
            module: 0,
            name: "BoundedU64_add_aborts".to_string(),
            signature: Signature {
                type_params: vec![],
                params: vec![Param {
                    name: "a".into(),
                    var: VarId::from("a"),
                    ty: Type::UInt(64),
                }],
                return_type: Type::Bool, // legacy stage-10 shape
            },
            effects: crate::ir::Effects::PURE,
            explicit_pure: true,
            is_framework: true,
            spec_target: Some(10),
            user_native: None,
        },
    );

    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    // Find f.aborts via FunctionKind::Spec{Aborts, target=0}
    // (since f's id is 0 in this fixture).
    let f_aborts_fid = aborts_of(&p, 0).expect("f.aborts");
    let f_aborts = &p.functions[&f_aborts_fid];

    // Expect two Lets in f.aborts.body.stmts:
    //   Let { pat: [__c_bool_var], value: Call(11, [x]) }
    //   Let { pat: [__c_var], value: If { cond: __c_bool_var,
    //                                    then: Value(Some(MoveAbortCode{0})),
    //                                    else: Value(None) } }
    assert_eq!(
        f_aborts.body.stmts.len(),
        2,
        "Bool->Option wrap produces 2 lets"
    );
    match &f_aborts.body.stmts[0] {
        Stmt::Let {
            value: Expr::Call { fun, .. },
            ..
        } => {
            assert_eq!(*fun, 11, "first let calls Bool-returning native");
        }
        other => panic!("expected first Let to call native 11, got {other:?}"),
    }
    match &f_aborts.body.stmts[1] {
        Stmt::Let {
            value: Expr::If { .. },
            ..
        } => {
            // Good — the wrap let is an If with Some/None arms.
        }
        other => panic!("expected wrap Let with If value, got {other:?}"),
    }
}

fn table_bool_native_program(mode: AbortPayloadMode, native_name: &str) -> Program {
    bool_native_program(
        mode,
        "Sui",
        "table",
        "2",
        native_name,
        &[("Sui", "dynamic_field", "2")],
    )
}

fn bool_native_program(
    mode: AbortPayloadMode,
    package_name: &str,
    module_name: &str,
    address: &str,
    native_name: &str,
    additional_modules: &[(&str, &str, &str)],
) -> Program {
    let f = func(
        "f",
        sig(vec![param("x", Type::UInt(64))], Type::UInt(64)),
        Block {
            stmts: vec![Stmt::Eval(Expr::Call {
                fun: 10,
                type_args: vec![],
                args: vec![Expr::Var(VarId::from("x"))],
            })],
            tail: BlockTail::Value(lit_u64(42)),
        },
        FunctionKind::Source,
    );
    let mut p = program_with(vec![(0, f)]);
    p.modules.insert(
        0,
        Module {
            name: "storage".to_string(),
            package_name: "lending_core".to_string(),
            address: "0".to_string(),
            required_imports: Vec::new(),
            is_native: false,
        },
    );
    p.modules.insert(
        1,
        Module {
            name: module_name.to_string(),
            package_name: package_name.to_string(),
            address: address.to_string(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    for (index, (package_name, module_name, address)) in additional_modules.iter().enumerate() {
        p.modules.insert(
            index + 2,
            Module {
                name: (*module_name).to_string(),
                package_name: (*package_name).to_string(),
                address: (*address).to_string(),
                required_imports: Vec::new(),
                is_native: true,
            },
        );
    }
    p.natives.decls.insert(
        10,
        NativeDecl {
            module: 1,
            name: native_name.to_string(),
            signature: Signature {
                type_params: vec![],
                params: vec![param("x", Type::UInt(64))],
                return_type: Type::UInt(64),
            },
            effects: crate::ir::Effects::PURE,
            explicit_pure: true,
            is_framework: true,
            spec_target: None,
            user_native: None,
        },
    );
    p.natives.decls.insert(
        11,
        NativeDecl {
            module: 1,
            name: format!("{native_name}.aborts"),
            signature: Signature {
                type_params: vec![],
                params: vec![param("x", Type::UInt(64))],
                return_type: Type::Bool,
            },
            effects: crate::ir::Effects::PURE,
            explicit_pure: true,
            is_framework: true,
            spec_target: Some(10),
            user_native: None,
        },
    );
    AbortProvenance::configure(&mut p, mode).unwrap();
    let preds = pre_strip_bodies(&p);
    aborts_variant::materialise(&mut p, &preds, &ProverFnIds::default()).expect("materialise");
    p
}

fn wrapped_bool_abort_fields(p: &Program) -> &[Expr] {
    let f_aborts = &p.functions[&aborts_of(p, 0).expect("f.aborts")];
    let then_branch = match &f_aborts.body.stmts[1] {
        Stmt::Let {
            value: Expr::If { then_branch, .. },
            ..
        } => then_branch,
        other => panic!("expected Bool wrapper If, got {other:?}"),
    };
    let option_fields = match &then_branch.tail {
        BlockTail::Value(Expr::Pack {
            variant: Some(variant),
            fields,
            ..
        }) if *variant == crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG => fields,
        other => panic!("expected Aborted payload, got {other:?}"),
    };
    match option_fields.as_slice() {
        [Expr::Pack { fields, .. }] => fields,
        other => panic!("expected wrapped AbortCode, got {other:?}"),
    }
}

#[test]
fn proof_bool_native_wrapper_keeps_the_existing_single_field_payload() {
    let p = table_bool_native_program(AbortPayloadMode::Proof, "borrow");
    assert_eq!(wrapped_bool_abort_fields(&p), &[lit_u64(0)]);

    let rendered = crate::render::render_program(&p).expect("render");
    assert!(!rendered.contains("origin_tag"));
}

#[test]
fn observed_table_bool_native_wrappers_use_semantic_abort_descriptors() {
    for (native_name, code, origin_tag) in [
        ("borrow", 1, 2),
        ("borrow_mut", 1, 2),
        ("remove", 1, 2),
        ("add", 0, 2),
        ("destroy_empty", 0, 3),
    ] {
        let p = table_bool_native_program(AbortPayloadMode::ObservedTest, native_name);
        assert_eq!(
            wrapped_bool_abort_fields(&p),
            &[
                lit_u64(code),
                lit_u64(origin_tag),
                lit_u64(crate::ir::ObservedErrorKind::Abort.tag()),
            ],
            "descriptor for table::{native_name}"
        );
    }

    let rendered = crate::render::render_program(&table_bool_native_program(
        AbortPayloadMode::ObservedTest,
        "borrow",
    ))
    .expect("render");
    assert!(rendered.contains("origin_tag"));
}

#[test]
fn observed_framework_bool_native_wrappers_use_exact_vm_failures() {
    let abort = crate::ir::ObservedErrorKind::Abort.tag();
    let vector = crate::ir::ObservedErrorKind::VectorOperation.tag();
    for (package, module, address, native, code, origin_tag, error_kind) in [
        ("Sui", "dynamic_field", "2", "add", 0, 2, abort),
        ("Sui", "dynamic_field", "2", "store_bag_add", 0, 2, abort),
        ("Sui", "dynamic_field", "2", "borrow", 1, 2, abort),
        ("Sui", "dynamic_field", "2", "borrow_mut", 1, 2, abort),
        ("Sui", "dynamic_field", "2", "remove", 1, 2, abort),
        ("Sui", "vec_set", "2", "insert", 0, 2, abort),
        ("Sui", "vec_set", "2", "remove", 1, 2, abort),
        ("Sui", "bag", "2", "destroy_empty", 0, 2, abort),
        ("Sui", "object_bag", "2", "destroy_empty", 0, 2, abort),
        ("MoveStdlib", "vector", "1", "borrow", 1, 1, vector),
        ("MoveStdlib", "vector", "1", "swap", 1, 1, vector),
        ("MoveStdlib", "vector", "1", "pop_back", 2, 1, vector),
        ("MoveStdlib", "vector", "1", "destroy_empty", 3, 1, vector),
        ("MoveStdlib", "vector", "1", "remove", 0x20000, 2, abort),
        ("MoveStdlib", "vector", "1", "insert", 0x20000, 2, abort),
    ] {
        let p = bool_native_program(
            AbortPayloadMode::ObservedTest,
            package,
            module,
            address,
            native,
            &[],
        );
        assert_eq!(
            wrapped_bool_abort_fields(&p),
            &[lit_u64(code), lit_u64(origin_tag), lit_u64(error_kind),],
            "descriptor for {package}::{module}::{native}"
        );
    }
}

#[test]
fn ambiguous_bool_native_wrappers_stay_unknown() {
    for (package, module, address, native) in [
        ("MoveStdlib", "vector", "1", "swap_remove"),
        ("Sui", "bag", "2", "add"),
        ("Sui", "bag", "2", "borrow"),
        ("Sui", "bag", "2", "remove"),
        ("Sui", "object_bag", "2", "add"),
        ("Sui", "object_bag", "2", "borrow"),
        ("Sui", "object_bag", "2", "remove"),
        ("MoveStdlib", "vector", "2", "borrow"),
        ("Sui", "dynamic_field", "3", "borrow"),
        ("Sui", "table", "3", "destroy_empty"),
        ("Tests", "helpers", "2", "BoundedU64_add"),
    ] {
        let p = bool_native_program(
            AbortPayloadMode::ObservedTest,
            package,
            module,
            address,
            native,
            &[],
        );
        assert_eq!(
            wrapped_bool_abort_fields(&p),
            &[lit_u64(0), lit_u64(0), lit_u64(0)],
            "ambiguous descriptor for {package}::{module}::{native}"
        );
    }
}

fn bounded_nat_bool_native_program(
    op: crate::stage_10_bounded_nat::prelude_fids::Op,
    src_width: u32,
) -> Program {
    let mut p = Program::default();
    p.modules.insert(
        0,
        Module {
            name: "arithmetic_tests".into(),
            package_name: "Tests".into(),
            address: "0".into(),
            required_imports: Vec::new(),
            is_native: false,
        },
    );
    p.functions.insert(
        0,
        func(
            "f",
            sig(Vec::new(), Type::Unit),
            Block {
                stmts: Vec::new(),
                tail: BlockTail::Value(Expr::Unit),
            },
            FunctionKind::Source,
        ),
    );
    let main = crate::stage_10_bounded_nat::prelude_fids::ensure_main_fid(&mut p, op, src_width);
    crate::stage_10_bounded_nat::prelude_fids::ensure_aborts_fid(&mut p, op, src_width)
        .expect("aborting BoundedNat operation");
    let params = p.natives.decls[&main].signature.params.clone();
    p.functions.insert(
        0,
        func(
            "f",
            sig(params.clone(), Type::Unit),
            Block {
                stmts: vec![Stmt::Eval(Expr::Call {
                    fun: main,
                    type_args: Vec::new(),
                    args: params
                        .iter()
                        .map(|param| Expr::Var(param.var.clone()))
                        .collect(),
                })],
                tail: BlockTail::Value(Expr::Unit),
            },
            FunctionKind::Source,
        ),
    );
    AbortProvenance::configure(&mut p, AbortPayloadMode::ObservedTest).unwrap();
    let preds = pre_strip_bodies(&p);
    aborts_variant::materialise(&mut p, &preds, &ProverFnIds::default()).expect("materialise");
    p
}

#[test]
fn observed_bounded_nat_failures_are_arithmetic_errors_at_the_caller() {
    use crate::stage_10_bounded_nat::prelude_fids::Op;

    for op in [
        Op::Add,
        Op::Sub,
        Op::Mul,
        Op::Div,
        Op::Mod,
        Op::Shl { rhs_width: 8 },
        Op::Shr { rhs_width: 8 },
        Op::Cast { dst: 8 },
    ] {
        let p = bounded_nat_bool_native_program(op, 64);
        assert_eq!(
            wrapped_bool_abort_fields(&p),
            &[
                lit_u64(0),
                lit_u64(1),
                lit_u64(crate::ir::ObservedErrorKind::Arithmetic.tag()),
            ],
            "BoundedNat descriptor for {op:?}"
        );
    }
}

fn validator_full_abort_program(mode: AbortPayloadMode) -> Program {
    let f = func(
        "f",
        sig(vec![param("x", Type::UInt(64))], Type::Unit),
        Block {
            stmts: vec![Stmt::Eval(Expr::Call {
                fun: 10,
                type_args: Vec::new(),
                args: vec![Expr::Var(VarId::from("x"))],
            })],
            tail: BlockTail::Value(Expr::Unit),
        },
        FunctionKind::Source,
    );
    let mut p = program_with(vec![(0, f)]);
    p.modules.insert(
        0,
        Module {
            name: "validator_tests".into(),
            package_name: "Tests".into(),
            address: "0".into(),
            required_imports: Vec::new(),
            is_native: false,
        },
    );
    p.modules.insert(
        1,
        Module {
            name: "validator".into(),
            package_name: "SuiSystem".into(),
            address: "3".into(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    p.natives.decls.insert(
        10,
        NativeDecl {
            module: 1,
            name: "validate_metadata_bcs".into(),
            signature: sig(vec![param("x", Type::UInt(64))], Type::Unit),
            effects: crate::ir::Effects::CONSERVATIVE,
            explicit_pure: false,
            is_framework: true,
            spec_target: None,
            user_native: None,
        },
    );
    p.natives.decls.insert(
        11,
        NativeDecl {
            module: 1,
            name: "validate_metadata_bcs.aborts".into(),
            signature: sig(vec![param("x", Type::UInt(64))], Type::Bool),
            effects: crate::ir::Effects::PURE,
            explicit_pure: true,
            is_framework: true,
            spec_target: Some(10),
            user_native: None,
        },
    );
    AbortProvenance::configure(&mut p, mode).unwrap();
    let preds = pre_strip_bodies(&p);
    aborts_variant::materialise(&mut p, &preds, &ProverFnIds::default()).expect("materialise");
    p
}

#[test]
fn observed_full_native_abort_preserves_code_and_stamps_validator_origin() {
    let p = validator_full_abort_program(AbortPayloadMode::ObservedTest);
    let f_aborts = &p.functions[&aborts_of(&p, 0).expect("f.aborts")];
    assert_eq!(f_aborts.body.stmts.len(), 2);
    let normalized = match &f_aborts.body.stmts[1] {
        Stmt::Let {
            value: Expr::Match { cases, .. },
            ..
        } => cases,
        other => panic!("expected validator result normalization, got {other:?}"),
    };
    let fields = match &normalized[1].body.tail {
        BlockTail::Value(Expr::Pack { fields, .. }) => match fields.as_slice() {
            [Expr::Pack { fields, .. }] => fields,
            other => panic!("expected wrapped validator AbortCode, got {other:?}"),
        },
        other => panic!("expected stamped validator abort, got {other:?}"),
    };
    assert!(matches!(
        &fields[0],
        Expr::Field {
            struct_id,
            field_index: 0,
            ..
        } if *struct_id == p.struct_id_by_qualified_name(ABORT_CODE_QUALIFIED_NAME).unwrap()
    ));
    assert_eq!(fields[1], lit_u64(2));
    assert_eq!(
        fields[2],
        lit_u64(crate::ir::ObservedErrorKind::Abort.tag())
    );

    let proof = validator_full_abort_program(AbortPayloadMode::Proof);
    let proof_aborts = &proof.functions[&aborts_of(&proof, 0).expect("f.aborts")];
    assert_eq!(proof_aborts.body.stmts.len(), 1);
    assert!(matches!(
        &proof_aborts.body.stmts[0],
        Stmt::Let {
            value: Expr::Call { fun: 11, .. },
            ..
        }
    ));
    assert_eq!(
        proof.structs[&proof
            .struct_id_by_qualified_name(ABORT_CODE_QUALIFIED_NAME)
            .unwrap()]
            .fields
            .len(),
        1
    );
}

#[test]
fn observed_unmapped_bool_native_wrapper_uses_unknown_origin() {
    let p = table_bool_native_program(AbortPayloadMode::ObservedTest, "unmapped");
    assert_eq!(
        wrapped_bool_abort_fields(&p),
        &[
            lit_u64(0),
            lit_u64(0),
            lit_u64(crate::ir::ObservedErrorKind::Unknown.tag()),
        ]
    );
}

#[test]
fn borrow_map_key_on_bag_splices_typed_borrow_aborts() {
    let key_ty = Type::UInt(64);
    let value_ty = Type::Bool;
    let bag_sid = 100;
    let bag_ty = Type::Struct {
        struct_id: bag_sid,
        type_args: vec![],
    };
    let mut_bag_ty = Type::MutableRef {
        inner: Box::new(bag_ty.clone()),
        root: Box::new(bag_ty),
    };

    let f = func(
        "f",
        sig(
            vec![param("bag", mut_bag_ty), param("k", key_ty.clone())],
            value_ty.clone(),
        ),
        Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(VarId::from("v"))],
                value: Expr::Borrow {
                    step: PathStep::MapKey {
                        key: Box::new(Expr::Var(VarId::from("k"))),
                        key_type: key_ty.clone(),
                        value_type: value_ty.clone(),
                        df_value: None,
                    },
                    base: Box::new(Expr::Var(VarId::from("bag"))),
                },
            }],
            tail: BlockTail::Value(Expr::Var(VarId::from("v"))),
        },
        FunctionKind::Source,
    );
    let mut p = program_with(vec![(0, f)]);
    p.modules.insert(
        1,
        Module {
            name: "bag".to_string(),
            package_name: "Sui".to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    p.structs.insert(
        bag_sid,
        Struct {
            module_id: 1,
            name: "Bag".to_string(),
            qualified_name: "Sui::bag::Bag".to_string(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: None,
            is_native: true,
        },
    );
    p.natives.decls.insert(
        10,
        NativeDecl {
            module: 1,
            name: "borrow".to_string(),
            signature: Signature {
                type_params: vec!["K".to_string(), "V".to_string()],
                params: vec![
                    param(
                        "self",
                        Type::Struct {
                            struct_id: bag_sid,
                            type_args: vec![],
                        },
                    ),
                    param("k", Type::TypeParam(0)),
                ],
                return_type: Type::TypeParam(1),
            },
            effects: crate::ir::Effects::PURE,
            explicit_pure: true,
            is_framework: true,
            spec_target: None,
            user_native: None,
        },
    );
    p.natives.decls.insert(
        11,
        NativeDecl {
            module: 1,
            name: "borrow.aborts".to_string(),
            signature: Signature {
                type_params: vec!["K".to_string(), "V".to_string()],
                params: vec![
                    param(
                        "self",
                        Type::Struct {
                            struct_id: bag_sid,
                            type_args: vec![],
                        },
                    ),
                    param("k", Type::TypeParam(0)),
                ],
                return_type: Type::Bool,
            },
            effects: crate::ir::Effects::PURE,
            explicit_pure: true,
            is_framework: true,
            spec_target: Some(10),
            user_native: None,
        },
    );

    let preds = pre_strip_bodies(&p);
    let ids = ProverFnIds::default();
    aborts_variant::materialise(&mut p, &preds, &ids).expect("materialise");

    let f_aborts_fid = aborts_of(&p, 0).expect("f.aborts");
    let f_aborts = &p.functions[&f_aborts_fid];

    assert_eq!(
        f_aborts.body.stmts.len(),
        2,
        "Bool-returning bag borrow.aborts is called and wrapped"
    );
    match &f_aborts.body.stmts[0] {
        Stmt::Let {
            value:
                Expr::Call {
                    fun,
                    type_args,
                    args,
                },
            ..
        } => {
            assert_eq!(*fun, 11);
            assert_eq!(type_args, &vec![key_ty.clone(), value_ty.clone()]);
            assert_eq!(
                args,
                &vec![Expr::Var(VarId::from("bag")), Expr::Var(VarId::from("k"))]
            );
        }
        other => panic!("expected first Let to call bag borrow.aborts, got {other:?}"),
    }

    let none_arm_body = match &f_aborts.body.tail {
        BlockTail::Value(Expr::Match { cases, .. }) => cases
            .iter()
            .find(|a| a.variant == crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG)
            .map(|a| &a.body)
            .expect("None arm"),
        other => panic!("expected Value(Match), got {other:?}"),
    };
    assert!(
        matches!(
            &none_arm_body.stmts[0],
            Stmt::Let {
                value: Expr::Borrow { .. },
                ..
            }
        ),
        "None arm keeps the original map-key borrow"
    );
}

// ---------------------------------------------------------------------------
// Phase 3a.5b -- labeled-block loop chains (`retype_and_splice_labeled_block_loops`)
// ---------------------------------------------------------------------------

/// Build the `is_duplicate_with_pending_validator` shape: an abortable
/// callee `g` runs BEFORE the labeled block, so `materialise` has wrapped
/// the remainder in `match g.aborts(..) { NoAbort => { .. } }` and the dead
/// `let v = P(x)` sits ONE LEVEL DOWN inside that arm -- not as the last
/// top-level statement of the `Spec(Aborts)` body.
///
/// ```text
/// #0 g(y)          Source
/// #1 f(x)          Source
/// #2 g.aborts(y)   Spec(Aborts, target #0)
/// #3 f.aborts(x)   Spec(Aborts, target #1)
///      let __c_0 = g.aborts(x)
///      match __c_0 { NoAbort => { let v = P(x); NoAbort }
///                    Aborted(_) => __c_0 }
/// #4 f.aborts.labeled_0(x)                  Synthetic  -> L(x)
/// #5 f.aborts.labeled_0.while_0(x)          LoopBody{parent #4, slot 0}
/// #6 f.aborts.labeled_0.while_0.after(x)    LoopAfter{parent #4, slot 0}
/// ```
///
/// `Consumption` selects what the guard arm does with `v`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Consumption {
    /// `let v = P(x); NoAbort` -- `v` discarded outright.
    Dead,
    /// `let v = P(x); let n = !v; NoAbort` -- `v` IS read, but only by a
    /// binding that is itself dead. The `no_pending_or_active_duplicates_*`
    /// family's shape: the wrapper's result feeds a negation that feeds an
    /// `if` whose value nothing consumes.
    DerivedDead,
    /// `let v = P(x); v` -- the result reaches the tail. Threading, not
    /// deadening; this pass must decline.
    Live,
}

fn labeled_chain_program(consumption: Consumption) -> (Program, aborts_variant::AbortsMap) {
    let bool_body = || body_value(Expr::Const(crate::ir::Const::Bool(false)));
    let call = |fun: usize, arg: &str| Expr::Call {
        fun,
        type_args: vec![],
        args: vec![Expr::Var(VarId::from(arg))],
    };

    let mut p = program_with(vec![
        (
            0,
            func(
                "g",
                sig(vec![param("y", Type::UInt(64))], Type::UInt(64)),
                body_value(lit_u64(0)),
                FunctionKind::Source,
            ),
        ),
        (
            1,
            func(
                "f",
                sig(vec![param("x", Type::UInt(64))], Type::Bool),
                bool_body(),
                FunctionKind::Source,
            ),
        ),
        (
            2,
            func(
                "g.aborts",
                sig(vec![param("y", Type::UInt(64))], Type::UInt(64)),
                bool_body(),
                FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    target: 0,
                },
            ),
        ),
        (
            3,
            func(
                "f.aborts",
                sig(vec![param("x", Type::UInt(64))], Type::Bool),
                bool_body(),
                FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    target: 1,
                },
            ),
        ),
        (
            4,
            func(
                "f.aborts.labeled_0",
                sig(vec![param("x", Type::UInt(64))], Type::Bool),
                body_value(call(5, "x")),
                FunctionKind::Synthetic,
            ),
        ),
        (
            5,
            func(
                "f.aborts.labeled_0.while_0",
                sig(vec![param("x", Type::UInt(64))], Type::Bool),
                Block {
                    // The dropped callee-abort: `g` is an `aborts_map` key.
                    stmts: vec![Stmt::Let {
                        pattern: vec![Some(VarId::from("t"))],
                        value: call(0, "x"),
                    }],
                    tail: BlockTail::Value(call(6, "x")),
                },
                FunctionKind::LoopBody { parent: 4, slot: 0 },
            ),
        ),
        (
            6,
            func(
                "f.aborts.labeled_0.while_0.after",
                sig(vec![param("x", Type::UInt(64))], Type::Bool),
                bool_body(),
                FunctionKind::LoopAfter { parent: 4, slot: 0 },
            ),
        ),
    ]);

    let types = crate::stage_07_dejumps::option_aborts::ensure_aborts_types(&mut p);
    let abort_result_ty = types.option_abort_code_type();
    for fid in [2, 3] {
        p.functions.get_mut(&fid).unwrap().signature.return_type = abort_result_ty.clone();
    }
    let mut guard_stmts = vec![Stmt::Let {
        pattern: vec![Some(VarId::from("v"))],
        value: call(4, "x"),
    }];
    if consumption == Consumption::DerivedDead {
        guard_stmts.push(Stmt::Let {
            pattern: vec![Some(VarId::from("n"))],
            value: Expr::UnOp {
                op: crate::ir::ops::UnOp::Not,
                operand: Box::new(Expr::Var(VarId::from("v"))),
            },
        });
    }
    let guarded_arm = Block {
        stmts: guard_stmts,
        tail: BlockTail::Value(if consumption == Consumption::Live {
            Expr::Var(VarId::from("v"))
        } else {
            types.make_none()
        }),
    };
    p.functions.get_mut(&3).unwrap().body = Block {
        stmts: vec![Stmt::Let {
            pattern: vec![Some(VarId::from("__c_0"))],
            value: call(2, "x"),
        }],
        tail: BlockTail::Value(Expr::Match {
            struct_id: types.option,
            selector: Box::new(Expr::Var(VarId::from("__c_0"))),
            cases: vec![
                crate::ir::MatchArm {
                    variant: crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG,
                    bindings: vec![],
                    body: Box::new(guarded_arm),
                },
                crate::ir::MatchArm {
                    variant: crate::stage_07_dejumps::option_aborts::OPTION_SOME_TAG,
                    bindings: vec![VarId::from("__c_1")],
                    body: Box::new(body_value(Expr::Var(VarId::from("__c_0")))),
                },
            ],
        }),
    };

    let aborts_map: aborts_variant::AbortsMap = [(0usize, 2usize), (1, 3)].into_iter().collect();
    (p, aborts_map)
}

/// The chain's every consumption is dead, so the whole chain retypes --
/// even though the `let` is nested inside the guard arm rather than sitting
/// at the `Spec(Aborts)` body's top level. This is the shape that shipped a
/// `Bool`-returning `<f>.aborts.labeled_0.while_0` to the renderer.
#[test]
fn labeled_chain_retypes_when_the_dead_let_is_nested_in_a_guard_arm() {
    let (mut p, aborts_map) = labeled_chain_program(Consumption::Dead);
    let abort_result_ty = crate::stage_07_dejumps::option_aborts::ensure_aborts_types(&mut p)
        .option_abort_code_type();

    aborts_variant::retype_and_splice_labeled_block_loops(&mut p, &aborts_map);

    for fid in [4, 5, 6] {
        assert_eq!(
            p.functions[&fid].signature.return_type, abort_result_ty,
            "fid {fid} ({}) must be retyped to AbortResult",
            p.functions[&fid].name
        );
    }

    // The guard arm's dead `let v = P(x)` is gone, replaced by the generic
    // splice's `let __c_N = P(x)` + abort-propagating Match. `__c_N` must
    // NOT collide with the `__c_0` materialise already bound here.
    let none_arm = match &p.functions[&3].body.tail {
        BlockTail::Value(Expr::Match { cases, .. }) => cases
            .iter()
            .find(|a| a.variant == crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG)
            .map(|a| &a.body)
            .expect("None arm"),
        other => panic!("expected Value(Match), got {other:?}"),
    };
    let injected = match &none_arm.stmts[..] {
        [Stmt::Let { pattern, value }] => {
            assert!(
                matches!(value, Expr::Call { fun: 4, .. }),
                "expected the injected `let __c_N = P(x)`, got {value:?}"
            );
            pattern[0].clone().expect("single binding")
        }
        other => panic!("expected exactly one injected Let, got {other:?}"),
    };
    assert_ne!(
        injected,
        VarId::from("__c_0"),
        "the second splice pass must not shadow the first pass's `__c_0`"
    );
    assert!(
        matches!(
            &none_arm.tail,
            BlockTail::Value(Expr::Match { selector, .. })
                if **selector == Expr::Var(injected.clone())
        ),
        "guard arm must retail to a Match on the injected verdict, got {:?}",
        none_arm.tail
    );

    // The loop body's dropped callee-abort is now spliced in.
    let loop_body = &p.functions[&5].body;
    assert!(
        matches!(
            &loop_body.stmts[0],
            Stmt::Let {
                value: Expr::Call { fun: 2, .. },
                ..
            }
        ),
        "loop body must open with `let __c = g.aborts(x)`, got {:?}",
        loop_body.stmts[0]
    );
}

/// A LIVE consumption needs the accumulator threaded, not deadened, so the
/// pass must decline the whole chain rather than half-convert it. (That is
/// the `Ascii.try_string` / `Voting_power.insert` shape.)
#[test]
fn labeled_chain_declines_a_live_consumption() {
    let (mut p, aborts_map) = labeled_chain_program(Consumption::Live);
    let before: Vec<Type> = [4, 5, 6]
        .iter()
        .map(|fid| p.functions[fid].signature.return_type.clone())
        .collect();

    aborts_variant::retype_and_splice_labeled_block_loops(&mut p, &aborts_map);

    let after: Vec<Type> = [4, 5, 6]
        .iter()
        .map(|fid| p.functions[fid].signature.return_type.clone())
        .collect();
    assert_eq!(before, after, "a live consumption must not be retyped");
    assert!(
        matches!(&p.functions[&3].body.tail, BlockTail::Value(Expr::Match { cases, .. })
            if cases.iter().any(|a| a.body.stmts.len() == 1)),
        "the host body must be left untouched"
    );
}

/// A consumption read only by a binding that is itself dead is still dead:
/// the transitively-dead cone must be pruned before the acceptance
/// predicate looks. This is the `no_pending_or_active_duplicates_*` shape
/// -- nine of the thirteen broken sui-system clusters.
#[test]
fn labeled_chain_retypes_a_transitively_dead_consumption() {
    let (mut p, aborts_map) = labeled_chain_program(Consumption::DerivedDead);
    let abort_result_ty = crate::stage_07_dejumps::option_aborts::ensure_aborts_types(&mut p)
        .option_abort_code_type();

    aborts_variant::retype_and_splice_labeled_block_loops(&mut p, &aborts_map);

    for fid in [4, 5, 6] {
        assert_eq!(
            p.functions[&fid].signature.return_type, abort_result_ty,
            "fid {fid} ({}) must be retyped to AbortResult",
            p.functions[&fid].name
        );
    }
    let none_arm = match &p.functions[&3].body.tail {
        BlockTail::Value(Expr::Match { cases, .. }) => cases
            .iter()
            .find(|a| a.variant == crate::stage_07_dejumps::option_aborts::OPTION_NONE_TAG)
            .map(|a| &a.body)
            .expect("None arm"),
        other => panic!("expected Value(Match), got {other:?}"),
    };
    // The derived `let n = !v` is gone -- leaving it would dangle on `v`,
    // which the demotion to `Eval(P(x))` unbinds.
    assert_eq!(
        none_arm.stmts.len(),
        1,
        "the dead cone above the consumption must be pruned, got {:?}",
        none_arm.stmts
    );
    assert!(
        matches!(
            &none_arm.stmts[0],
            Stmt::Let {
                value: Expr::Call { fun: 4, .. },
                ..
            }
        ),
        "expected the injected `let __c_N = P(x)`, got {:?}",
        none_arm.stmts[0]
    );
}
