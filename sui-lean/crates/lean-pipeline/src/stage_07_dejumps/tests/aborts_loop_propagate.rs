//! Phase 3a.5 guard tests -- a WORLD-THREADED loop result is a consumer too.
//!
//! `aborts_loop_propagate` may retype a loop slot to `AbortResult` and give
//! `while_N.after` an unconditional `NoAbort` tail ONLY when nothing still
//! reads the loop's accumulator. Its liveness guard recognised the
//! single-binder consumption `let v := while_N(..)` and nothing else, so the
//! world-threaded destructure `let (acc, world) := while_N(..)` -- the normal
//! shape for every loop that threads the World -- walked straight past it.
//!
//! The measured casualty is scallop `ScallopProtocol::borrow::
//! assert_isolated_asset`. Both of its `#[loop_after]` continuations lost
//! their tail, so the post-loop abort condition
//! `unable_to_borrow_other_coin_with_isolated_asset` was discarded from the
//! `.aborts` face: the `.after` said "the loop exited, therefore NoAbort"
//! while the check that turns a `false` accumulator into an abort sat in a
//! continuation nobody called any more.
//!
//! The fixture below is that function's shape at the phase-3a.5 boundary: two
//! sibling loops in the two arms of an `if`, their `(accumulator, World)`
//! result destructured by one `let`, and a post-loop `if acc { NoAbort } else
//! { Aborted CODE }`.

use crate::ir::builder::ProverFnIds;
use crate::ir::{
    Block, BlockTail, Const, Expr, Function, FunctionKind, MatchArm, Module, Param, Program,
    Signature, SpecKind, Stmt, Struct, Type, VarId,
};
use ethnum::U256;

use crate::stage_07_dejumps::aborts_variant::AbortsMap;
use crate::stage_07_dejumps::option_aborts::{self, OPTION_NONE_TAG, OPTION_SOME_TAG};
use crate::stage_07_dejumps::{
    aborts_live_loop, aborts_loop_propagate, asymmetric_arms, cont_inline, return_collapse,
    return_lift,
};

const G: usize = 0;
const F: usize = 1;
const G_ABORTS: usize = 2;
const F_ABORTS: usize = 3;
const WHILE0: usize = 4;
const AFTER0: usize = 5;
const WHILE1: usize = 6;
const AFTER1: usize = 7;
const H: usize = 8;
const H_ABORTS: usize = 9;

const WORLD_SID: usize = 900;

/// The post-loop abort face the defect discarded.
const ABORT_CODE: u64 = 77;

/// How the `.aborts` parent consumes the loop result.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Consumption {
    /// `let (acc, world) := if c { while_0(..) } else { while_1(..) }` and the
    /// remainder turns `acc` into the post-loop abort. Scallop's shape.
    WorldThreadedLive,
    /// cetus `position::update_rewards_internal`: the loop sits in the `then`
    /// arm of a value-position `if` bound by the LAST top-level statement, and
    /// nothing reads the binding. This is the dead-accumulator case the pass
    /// exists for, so it must still convert -- and convert PROPERLY, rewriting
    /// the sibling arm to `NoAbort` and appending the `match` that propagates
    /// the verdict. Reporting success without those two is what turned
    /// `update_rewards_internal.aborts` into a bare `NoAbort`.
    CetusDeadArmNested,
    /// The cetus shape in the parent -- so `try_propagate` succeeds there --
    /// while a SECOND function destructures the same loop's
    /// `(accumulator, World)` and reads it. The retype is per-FUNCTION, so
    /// converting on the strength of the parent alone leaves that second
    /// consumer binding an `AbortResult` as the accumulator. This is
    /// `mmt_v3::tick::update`'s defect at the arity the world-threaded
    /// destructure actually uses.
    DeadHereLiveElsewhere,
}

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

fn func(name: &str, signature: Signature, body: Block, kind: FunctionKind) -> Function {
    Function {
        module: 0,
        name: name.to_string(),
        signature,
        body,
        kind,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    }
}

fn lit_u64(n: u64) -> Expr {
    Expr::Const(Const::UInt {
        bits: 64,
        value: U256::from(n),
    })
}

fn var(name: &str) -> Expr {
    Expr::Var(VarId::from(name))
}

fn call(fun: usize, args: Vec<Expr>) -> Expr {
    Expr::Call {
        fun,
        type_args: vec![],
        args,
    }
}

fn value(e: Expr) -> Block {
    Block {
        stmts: vec![],
        tail: BlockTail::Value(e),
    }
}

fn let1(name: &str, v: Expr) -> Stmt {
    Stmt::Let {
        pattern: vec![Some(VarId::from(name))],
        value: v,
    }
}

fn if_expr(cond: Expr, then_branch: Block, else_branch: Block) -> Expr {
    Expr::If {
        cond: Box::new(cond),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

fn world_type() -> Type {
    Type::Struct {
        struct_id: WORLD_SID,
        type_args: Vec::new(),
    }
}

/// `(Bool, World)` -- the accumulator the loop helpers carry.
fn carried_type() -> Type {
    Type::Tuple(vec![Type::Bool, world_type()])
}

/// One loop slot: a body whose callee-abort splice carries a `Return(Aborted)`
/// (phase 3a.5's guard A), and an `.after` in the trivial exit form (guard B).
fn add_slot(p: &mut Program, slot: u32, while_fid: usize, after_fid: usize, types_option: usize) {
    let params = || vec![param("acc", Type::Bool), param("w", world_type())];
    let body = Block {
        stmts: vec![
            let1("__c_0", call(G_ABORTS, vec![lit_u64(0)])),
            let1("t", Expr::Const(Const::Bool(true))),
        ],
        tail: BlockTail::Value(Expr::Match {
            struct_id: types_option,
            selector: Box::new(var("__c_0")),
            cases: vec![
                MatchArm {
                    variant: OPTION_NONE_TAG,
                    bindings: vec![],
                    body: Box::new(value(if_expr(
                        var("t"),
                        value(call(while_fid, vec![var("acc"), var("w")])),
                        value(call(after_fid, vec![var("acc"), var("w")])),
                    ))),
                },
                MatchArm {
                    variant: OPTION_SOME_TAG,
                    bindings: vec![VarId::from("__c_1")],
                    body: Box::new(Block {
                        stmts: vec![],
                        tail: BlockTail::Return(Box::new(var("__c_0"))),
                    }),
                },
            ],
        }),
    };
    p.functions.insert(
        while_fid,
        func(
            &format!("f.aborts.while_{slot}"),
            sig(params(), carried_type()),
            body,
            FunctionKind::LoopBody {
                parent: F_ABORTS,
                slot,
            },
        ),
    );
    p.functions.insert(
        after_fid,
        func(
            &format!("f.aborts.while_{slot}.after"),
            sig(params(), carried_type()),
            value(Expr::Tuple(vec![var("acc"), var("w")])),
            FunctionKind::LoopAfter {
                parent: F_ABORTS,
                slot,
            },
        ),
    );
}

fn fixture(consumption: Consumption) -> (Program, AbortsMap, Type) {
    let mut p = Program::default();
    p.modules.insert(0, module());
    p.structs.insert(
        WORLD_SID,
        Struct {
            module_id: 0,
            name: "World".into(),
            qualified_name: crate::stage_04_effects::WORLD_QUALIFIED_NAME.into(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: None,
            is_native: true,
        },
    );

    p.functions.insert(
        G,
        func(
            "g",
            sig(vec![param("x", Type::UInt(64))], Type::Bool),
            value(Expr::Const(Const::Bool(false))),
            FunctionKind::Source,
        ),
    );
    p.functions.insert(
        F,
        func(
            "f",
            sig(
                vec![param("c", Type::Bool), param("w", world_type())],
                world_type(),
            ),
            value(var("w")),
            FunctionKind::Source,
        ),
    );

    let types = option_aborts::ensure_aborts_types(&mut p);
    let abort_result_ty = types.option_abort_code_type();

    p.functions.insert(
        G_ABORTS,
        func(
            "g.aborts",
            sig(vec![param("x", Type::UInt(64))], abort_result_ty.clone()),
            value(types.make_some(lit_u64(1))),
            FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target: G,
            },
        ),
    );

    add_slot(&mut p, 0, WHILE0, AFTER0, types.option);
    add_slot(&mut p, 1, WHILE1, AFTER1, types.option);

    // One `if` arm: the callee-abort guard `materialise` splices around the
    // loop seed, whose Aborted arm is the inner `Return` that makes
    // `return_lift` lift this whole `let`'s remainder into a continuation.
    let seeded_arm = |tmp: &str, bound: &str, while_fid: usize| Block {
        stmts: vec![let1(tmp, call(G_ABORTS, vec![lit_u64(0)]))],
        tail: BlockTail::Value(Expr::Match {
            struct_id: types.option,
            selector: Box::new(var(tmp)),
            cases: vec![
                MatchArm {
                    variant: OPTION_NONE_TAG,
                    bindings: vec![],
                    body: Box::new(value(call(while_fid, vec![var("acc0"), var("w")]))),
                },
                MatchArm {
                    variant: OPTION_SOME_TAG,
                    bindings: vec![VarId::from(bound)],
                    body: Box::new(Block {
                        stmts: vec![],
                        tail: BlockTail::Return(Box::new(var(tmp))),
                    }),
                },
            ],
        }),
    };

    let (stmts, tail) = match consumption {
        Consumption::WorldThreadedLive => (
            vec![
                let1("acc0", Expr::Const(Const::Bool(true))),
                Stmt::Let {
                    pattern: vec![Some(VarId::from("acc")), Some(VarId::from("w2"))],
                    value: if_expr(
                        var("c"),
                        seeded_arm("__c_2", "__c_3", WHILE0),
                        seeded_arm("__c_4", "__c_5", WHILE1),
                    ),
                },
                // The post-loop abort face: `if acc { () } else { abort CODE }`.
                Stmt::Eval(if_expr(
                    var("acc"),
                    value(Expr::Unit),
                    Block {
                        stmts: vec![],
                        tail: BlockTail::Return(Box::new(types.make_some(lit_u64(ABORT_CODE)))),
                    },
                )),
            ],
            BlockTail::Return(Box::new(types.make_none())),
        ),
        Consumption::CetusDeadArmNested | Consumption::DeadHereLiveElsewhere => (
            vec![
                let1("acc0", Expr::Const(Const::Bool(true))),
                let1(
                    "dead",
                    if_expr(
                        var("c"),
                        value(call(WHILE0, vec![var("acc0"), var("w")])),
                        // cetus leaks `$t0_0` here -- the VALUE face's
                        // `&mut PositionInfo` -- when the arm is not rewritten.
                        value(var("w")),
                    ),
                ),
            ],
            BlockTail::Return(Box::new(types.make_none())),
        ),
    };

    p.functions.insert(
        F_ABORTS,
        func(
            "f.aborts",
            sig(
                vec![param("c", Type::Bool), param("w", world_type())],
                abort_result_ty.clone(),
            ),
            Block { stmts, tail },
            FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target: F,
            },
        ),
    );

    if consumption == Consumption::DeadHereLiveElsewhere {
        p.functions.insert(
            H_ABORTS,
            func(
                "h.aborts",
                sig(
                    vec![param("c", Type::Bool), param("w", world_type())],
                    abort_result_ty.clone(),
                ),
                Block {
                    stmts: vec![
                        let1("acc0", Expr::Const(Const::Bool(true))),
                        Stmt::Let {
                            pattern: vec![Some(VarId::from("hacc")), Some(VarId::from("hw"))],
                            value: call(WHILE0, vec![var("acc0"), var("w")]),
                        },
                    ],
                    tail: BlockTail::Value(if_expr(
                        var("hacc"),
                        value(types.make_none()),
                        value(types.make_some(lit_u64(ABORT_CODE))),
                    )),
                },
                FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    target: H,
                },
            ),
        );
    }

    let aborts_map: AbortsMap = [(G, G_ABORTS), (F, F_ABORTS)].into_iter().collect();
    (p, aborts_map, abort_result_ty)
}

/// Every `FunId` reachable from `root` by a `Call` edge.
fn reachable_from(p: &Program, root: usize) -> std::collections::BTreeSet<usize> {
    use crate::ir::visit::{walk_expr_default, Visitor};
    struct C(std::collections::BTreeSet<usize>);
    impl Visitor for C {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, .. } = e {
                self.0.insert(*fun);
            }
            walk_expr_default(self, e);
        }
    }
    let mut seen: std::collections::BTreeSet<usize> = [root].into_iter().collect();
    let mut queue = vec![root];
    while let Some(fid) = queue.pop() {
        let Some(f) = p.functions.get(&fid) else {
            continue;
        };
        let mut c = C(Default::default());
        c.visit_block(&f.body);
        for callee in c.0 {
            if seen.insert(callee) {
                queue.push(callee);
            }
        }
    }
    seen
}

/// Does any function reachable from `f.aborts` still mention `ABORT_CODE`?
fn abort_face_reachable(p: &Program) -> bool {
    use crate::ir::visit::{walk_expr_default, Visitor};
    struct A(bool);
    impl Visitor for A {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Const(Const::UInt { value, .. }) = e {
                if *value == U256::from(ABORT_CODE) {
                    self.0 = true;
                }
            }
            walk_expr_default(self, e);
        }
    }
    reachable_from(p, F_ABORTS).into_iter().any(|fid| {
        p.functions.get(&fid).is_some_and(|f| {
            let mut a = A(false);
            a.visit_block(&f.body);
            a.0
        })
    })
}

/// The mechanism. A `#[loop_after]` may only be deadened to an unconditional
/// `NoAbort` once nothing reads the accumulator it was returning; the
/// world-threaded destructure `let (acc, world) := while_N(..)` IS such a
/// reader, so both slots must be declined and left exactly as they were.
#[test]
fn world_threaded_live_accumulator_declines_the_slot() {
    let (mut p, aborts_map, abort_result_ty) = fixture(Consumption::WorldThreadedLive);
    let before: Vec<Block> = [AFTER0, AFTER1]
        .iter()
        .map(|fid| p.functions[fid].body.clone())
        .collect();

    aborts_loop_propagate::run(&mut p, &aborts_map).expect("phase 3a.5");

    for fid in [WHILE0, AFTER0, WHILE1, AFTER1] {
        assert_ne!(
            p.functions[&fid].signature.return_type, abort_result_ty,
            "{} must not be retyped while `acc` is still read",
            p.functions[&fid].name
        );
        assert_eq!(
            p.functions[&fid].signature.return_type,
            carried_type(),
            "{} must keep carrying (accumulator, World)",
            p.functions[&fid].name
        );
    }
    for (fid, was) in [AFTER0, AFTER1].iter().zip(before) {
        assert_eq!(
            p.functions[fid].body, was,
            "{} must keep its continuation tail, not be deadened to NoAbort",
            p.functions[fid].name
        );
    }
}

/// The consequence, end to end: the post-loop abort condition must still be
/// reachable from the `.aborts` companion after the stage-7 phases that
/// follow. When the slot is wrongly converted, the check that raises it is
/// lifted into a continuation with no caller and the `.aborts` face silently
/// loses an abort path -- a green audit over a weaker property.
#[test]
fn the_post_loop_abort_face_survives_stage_seven() {
    let (mut p, aborts_map, _) = fixture(Consumption::WorldThreadedLive);
    assert!(abort_face_reachable(&p), "fixture must start with the face");

    aborts_loop_propagate::run(&mut p, &aborts_map).expect("phase 3a.5");
    return_lift::run(&mut p).expect("phase 3b");
    aborts_live_loop::run(&mut p).expect("phase 3b.5");
    return_collapse::run(&mut p).expect("phase 3c collapse");
    asymmetric_arms::run(&mut p).expect("phase 3c arms");
    return_collapse::run(&mut p).expect("phase 3c collapse");
    cont_inline::run(&mut p).expect("phase 3d");

    assert!(
        abort_face_reachable(&p),
        "the post-loop abort condition was discarded from f.aborts"
    );
}

/// Guard C0 is per-PROGRAM because the retype is. A slot whose result is
/// dead in the `.aborts` parent but destructured and read somewhere else
/// must be declined -- otherwise that second consumer binds an
/// `AbortResult` as the accumulator. The guard recognised only the
/// single-binder read, so every world-threaded `let (acc, world) :=
/// while_N(..)` slipped past it.
#[test]
fn a_live_reader_elsewhere_declines_the_slot() {
    let (mut p, aborts_map, abort_result_ty) = fixture(Consumption::DeadHereLiveElsewhere);

    aborts_loop_propagate::run(&mut p, &aborts_map).expect("phase 3a.5");

    for fid in [WHILE0, AFTER0] {
        assert_ne!(
            p.functions[&fid].signature.return_type, abort_result_ty,
            "{} must not be retyped while another function reads its accumulator",
            p.functions[&fid].name
        );
    }
}

/// The cetus anchor. A dead arm-nested loop result STILL converts -- this is
/// the case the pass exists for -- but conversion means all three steps, not
/// just the retype. `update_rewards_internal.aborts` regressed because the
/// pass reported success having rewritten nothing, leaving the companion's
/// tail an unconditional `NoAbort` and the sibling arm holding the value
/// face's `&mut PositionInfo`, while the Move source has two `assert!`s
/// inside that loop.
#[test]
fn dead_arm_nested_consumption_converts_with_the_propagating_match() {
    let (mut p, aborts_map, abort_result_ty) = fixture(Consumption::CetusDeadArmNested);

    aborts_loop_propagate::run(&mut p, &aborts_map).expect("phase 3a.5");

    for fid in [WHILE0, AFTER0] {
        assert_eq!(
            p.functions[&fid].signature.return_type, abort_result_ty,
            "{} must still be retyped when the accumulator is dead",
            p.functions[&fid].name
        );
    }

    let body = &p.functions[&F_ABORTS].body;
    // (a) the tail now consults the loop's verdict instead of asserting
    // NoAbort. The rewrite preserves whether the tail was a Value or a
    // Return; pre-return_lift it is still a Return.
    let tail_expr = match &body.tail {
        BlockTail::Value(e) => e,
        BlockTail::Return(e) => e.as_ref(),
        other => panic!("unexpected .aborts tail {other:?}"),
    };
    let Expr::Match {
        selector, cases, ..
    } = tail_expr
    else {
        panic!("the .aborts tail must become a match on the loop verdict, got {tail_expr:?}");
    };
    assert_eq!(**selector, var("dead"));
    assert_eq!(cases.len(), 2);
    // (b) the sibling arm delivers NoAbort rather than leaking the value face.
    let Some(Stmt::Let {
        value: Expr::If { else_branch, .. },
        ..
    }) = body.stmts.last()
    else {
        panic!("the loop binding must survive as the last statement");
    };
    assert_ne!(
        else_branch.tail,
        BlockTail::Value(var("w")),
        "the non-loop arm must be rewritten to NoAbort, not left holding the value face"
    );

    let _ = ProverFnIds::default();
}
