//! Phase 3b.5b tests -- the manufactured continuation
//! (`aborts_live_loop::run_labeled_wrapper_loops`).
//!
//! Both fixtures reproduce a measured sui-system shape: a `while` nested in
//! an extracted labeled block, whose accumulator the `Spec(Aborts)` parent
//! consumes LIVE. Phase 3a.5b vetoes those (it deadens, and a live result
//! cannot be deadened) and phase 3b.5 never enumerates them (the loop's
//! parent is the Synthetic `.aborts.labeled_N` wrapper), so before this pass
//! the whole chain reached the renderer accumulator-typed with every
//! callee-abort inside it dropped.

use crate::ir::builder::ProverFnIds;
use crate::ir::{
    Block, BlockTail, Const, Expr, Function, FunctionKind, MatchArm, Module, Param, Program,
    Signature, SpecKind, Stmt, Type, VarId,
};
use ethnum::U256;

use crate::stage_07_dejumps::aborts_live_loop;
use crate::stage_07_dejumps::aborts_variant::{self, AbortsMap};
use crate::stage_07_dejumps::option_aborts::{self, AbortsTypeIds, OPTION_SOME_TAG};
use crate::stage_07_dejumps::postcondition::{check, PostconditionError};
use crate::stage_07_dejumps::{asymmetric_arms, cont_inline, return_collapse, return_lift};

// FunIds shared by every fixture below.
const G: usize = 0;
const F: usize = 1;
const G_ABORTS: usize = 2;
const F_ABORTS: usize = 3;
const WRAPPER: usize = 4;
const LOOP: usize = 5;
const AFTER: usize = 6;

/// Which measured cluster the fixture reproduces.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    /// `ascii::try_string`: a `Bool` accumulator, an early-exit CONSTANT
    /// leaf inside the loop, and an `.after` that delivers the natural exit
    /// through a function-tail `Return`.
    TryString,
    /// `voting_power::insert`: an accumulator leaf that is itself an
    /// ABORTABLE CALL (tail position, which the splice does not detect), and
    /// an `.after` whose already-spliced Aborted arm carries
    /// `labeled_block_extract`'s fabricated `Abort { code: 0 }` placeholder.
    Insert,
}

/// How the host consumes the wrapper's result.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Consumption {
    /// `let acc = P(..)` and the remainder reads `acc`.
    Live,
    /// `let acc = P(..)` and nothing reads it -- phase 3a.5b's business.
    Dead,
    /// Two live sites: the wrapper's arity would change under one of them.
    LiveTwice,
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

/// Build the whole cluster. `dropped_abort` controls whether the loop
/// actually calls an abortable callee -- the gate every labeled-loop pass
/// keys on.
fn chain_program(
    shape: Shape,
    consumption: Consumption,
    dropped_abort: bool,
) -> (Program, AbortsMap, AbortsTypeIds) {
    let mut p = Program::default();
    p.modules.insert(0, module());
    let mut add = |fid: usize, f: Function| {
        p.functions.insert(fid, f);
    };

    // `g(x) : Bool` is the abortable callee whose face the misfiled chain
    // drops. `f(v) : u64` is the function under test.
    add(
        G,
        func(
            "g",
            sig(vec![param("x", Type::UInt(64))], Type::Bool),
            value(Expr::Const(Const::Bool(false))),
            FunctionKind::Source,
        ),
    );
    add(
        F,
        func(
            "f",
            sig(vec![param("v", Type::UInt(64))], Type::UInt(64)),
            value(lit_u64(0)),
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
            value(types.make_none()),
            FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target: G,
            },
        ),
    );

    // ---- the labeled-block chain -------------------------------------
    // P: `f.aborts.labeled_0(v, i) -> Bool`, body just `L(i, v)`.
    p.functions.insert(
        WRAPPER,
        func(
            "f.aborts.labeled_0",
            sig(
                vec![param("v", Type::UInt(64)), param("i", Type::UInt(64))],
                Type::Bool,
            ),
            value(call(LOOP, vec![var("i"), var("v")])),
            FunctionKind::Synthetic,
        ),
    );

    // L: guard -> (early-exit accumulator leaf | self-call), else -> A.
    let early_exit = match shape {
        Shape::TryString => Block {
            stmts: vec![let1("e", Expr::Const(Const::Bool(false)))],
            tail: BlockTail::Value(var("e")),
        },
        // A tail-position abortable call: the accumulator needs its VALUE,
        // so it cannot simply be swapped for its `.aborts`.
        Shape::Insert => value(call(G, vec![var("v")])),
    };
    let loop_stmts = if dropped_abort {
        vec![let1("t", call(G, vec![var("v")]))]
    } else {
        vec![let1("t", Expr::Const(Const::Bool(true)))]
    };
    p.functions.insert(
        LOOP,
        func(
            "f.aborts.labeled_0.while_0",
            sig(
                vec![param("i", Type::UInt(64)), param("v", Type::UInt(64))],
                Type::Bool,
            ),
            Block {
                stmts: loop_stmts,
                tail: BlockTail::Value(if_expr(
                    var("t"),
                    value(if_expr(
                        var("t"),
                        early_exit,
                        value(call(LOOP, vec![var("i"), var("v")])),
                    )),
                    value(call(AFTER, vec![var("i")])),
                )),
            },
            FunctionKind::LoopBody {
                parent: WRAPPER,
                slot: 0,
            },
        ),
    );

    // A: the labeled block's natural exit.
    let after_body = match shape {
        Shape::TryString => Block {
            stmts: vec![let1("r", Expr::Const(Const::Bool(true)))],
            tail: BlockTail::Return(Box::new(var("r"))),
        },
        // `materialise` already guarded this callee, and
        // `labeled_block_extract` then rewrote the Aborted arm's
        // `Return(__c_0)` to `Abort { code: 0 }` because the accumulator
        // return type had no way to say "aborted".
        Shape::Insert => Block {
            stmts: vec![let1("__c_0", call(G_ABORTS, vec![var("i")]))],
            tail: BlockTail::Value(Expr::Match {
                struct_id: types.option,
                selector: Box::new(var("__c_0")),
                cases: vec![
                    MatchArm {
                        variant: option_aborts::OPTION_NONE_TAG,
                        bindings: vec![],
                        body: Box::new(value(call(G, vec![var("i")]))),
                    },
                    MatchArm {
                        variant: OPTION_SOME_TAG,
                        bindings: vec![VarId::from("__c_1")],
                        body: Box::new(Block {
                            stmts: vec![],
                            tail: BlockTail::Abort {
                                code: Box::new(lit_u64(0)),
                            },
                        }),
                    },
                ],
            }),
        },
    };
    p.functions.insert(
        AFTER,
        func(
            "f.aborts.labeled_0.while_0.after",
            sig(vec![param("i", Type::UInt(64))], Type::Bool),
            after_body,
            FunctionKind::LoopAfter {
                parent: WRAPPER,
                slot: 0,
            },
        ),
    );

    // ---- the host ----------------------------------------------------
    // `f.aborts(v)`: seed the loop, consume its verdict, then abort with a
    // code derived from `v` (so `v` is a genuine continuation capture).
    let remainder_tail = match consumption {
        Consumption::Dead => BlockTail::Value(types.make_none()),
        Consumption::Live | Consumption::LiveTwice => BlockTail::Value(if_expr(
            var("acc"),
            value(types.make_none()),
            value(types.make_some(var("v"))),
        )),
    };
    let mut host_stmts = vec![let1("i0", lit_u64(0))];
    if consumption == Consumption::LiveTwice {
        host_stmts.push(let1("acc0", call(WRAPPER, vec![var("v"), var("i0")])));
    }
    host_stmts.push(let1("acc", call(WRAPPER, vec![var("v"), var("i0")])));
    p.functions.insert(
        F_ABORTS,
        func(
            "f.aborts",
            sig(vec![param("v", Type::UInt(64))], abort_result_ty),
            Block {
                stmts: host_stmts,
                tail: remainder_tail,
            },
            FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target: F,
            },
        ),
    );

    let aborts_map: AbortsMap = [(G, G_ABORTS), (F, F_ABORTS)].into_iter().collect();
    (p, aborts_map, types)
}

fn return_types(p: &Program) -> Vec<Type> {
    [WRAPPER, LOOP, AFTER]
        .iter()
        .map(|fid| p.functions[fid].signature.return_type.clone())
        .collect()
}

fn manufactured_cont(p: &Program) -> usize {
    let want = crate::ir::names::cont_name("f.aborts", 0);
    *p.functions
        .iter()
        .find(|(_, f)| f.name == want)
        .map(|(fid, _)| fid)
        .unwrap_or_else(|| panic!("expected a manufactured {want}"))
}

/// Every `Call(fun, ..)` reachable from `b`, at any depth.
fn callees(b: &Block) -> std::collections::BTreeSet<usize> {
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
    let mut c = C(Default::default());
    c.visit_block(b);
    c.0
}

fn has_abort_tail(b: &Block) -> bool {
    use crate::ir::visit::{walk_tail_default, Visitor};
    struct A(bool);
    impl Visitor for A {
        fn visit_tail(&mut self, t: &BlockTail) {
            if matches!(t, BlockTail::Abort { .. }) {
                self.0 = true;
            }
            walk_tail_default(self, t);
        }
    }
    let mut a = A(false);
    a.visit_block(b);
    a.0
}

// ---------------------------------------------------------------------------
// The acceptance test: drive `MisfiledAbortsFamilyValueChain` to zero.
// ---------------------------------------------------------------------------

#[test]
fn postcondition_rejects_the_live_chain_and_the_fold_clears_it() {
    for shape in [Shape::TryString, Shape::Insert] {
        let (mut p, aborts_map, _) = chain_program(shape, Consumption::Live, true);
        let ids = ProverFnIds::default();

        let err = check(&p, &ids).expect_err("the misfiled value chain must be rejected");
        assert!(
            matches!(
                err,
                PostconditionError::MisfiledAbortsFamilyValueChain {
                    dropped_callee: G,
                    ..
                }
            ),
            "got {err:?}"
        );

        aborts_live_loop::run_labeled_wrapper_loops(&mut p, &aborts_map).expect("fold");
        // The downstream phases the driver runs before `postcondition::check`:
        // 3b.6's `return_lift` plus 3c's arm lift + tail collapse are what
        // resolve the `Return(Aborted)`s this pass's loop splice injects.
        return_lift::run(&mut p).expect("return_lift");
        asymmetric_arms::run(&mut p).expect("asymmetric_arms");
        return_collapse::run(&mut p).expect("return_collapse");

        check(&p, &ids).expect("the retyped chain must satisfy the postcondition");
    }
}

/// The fold makes the host TAIL-call the wrapper, which turns that
/// single-use Synthetic into a `cont_inline` candidate -- and inlining it
/// deletes the very function the loop chain names as its `parent`. Both
/// invariants must end at zero: a dangling `LoopBody.parent` is not an
/// acceptable price for clearing the misfiled chain.
#[test]
fn cont_inline_after_the_fold_keeps_loop_parents_resolvable() {
    use crate::ir::invariants::baseline::FunctionKindReferencesResolve;
    use crate::ir::invariants::Invariant;

    for shape in [Shape::TryString, Shape::Insert] {
        let (mut p, aborts_map, _) = chain_program(shape, Consumption::Live, true);
        let ids = ProverFnIds::default();

        aborts_live_loop::run_labeled_wrapper_loops(&mut p, &aborts_map).expect("fold");
        return_lift::run(&mut p).expect("return_lift");
        asymmetric_arms::run(&mut p).expect("asymmetric_arms");
        return_collapse::run(&mut p).expect("return_collapse");
        cont_inline::run(&mut p).expect("cont_inline");

        assert!(
            !p.functions.contains_key(&WRAPPER),
            "the fold's tail-call makes the wrapper inlinable"
        );
        FunctionKindReferencesResolve
            .check(&p)
            .expect("every loop parent must still resolve");
        for fid in [LOOP, AFTER] {
            assert_eq!(
                p.functions[&fid].kind.loop_parent(),
                Some(F_ABORTS),
                "{} must be re-parented onto the function that absorbed the wrapper",
                p.functions[&fid].name
            );
        }
        check(&p, &ids).expect("the retyped chain must still satisfy the postcondition");
    }
}

// ---------------------------------------------------------------------------
// The `ascii::try_string` shape.
// ---------------------------------------------------------------------------

#[test]
fn try_string_shape_retypes_the_whole_chain_through_the_wrapper() {
    let (mut p, aborts_map, types) = chain_program(Shape::TryString, Consumption::Live, true);
    let abort_result_ty = types.option_abort_code_type();

    aborts_live_loop::run_labeled_wrapper_loops(&mut p, &aborts_map).expect("fold");

    for fid in [WRAPPER, LOOP, AFTER] {
        assert_eq!(
            p.functions[&fid].signature.return_type, abort_result_ty,
            "{} must be retyped to AbortResult",
            p.functions[&fid].name
        );
    }

    // All three carry one fresh trailing capture (`v`), each under its own
    // name, and the wrapper forwards its copy into the loop.
    for (fid, want) in [(WRAPPER, "__la_p0"), (LOOP, "__la_w0"), (AFTER, "__la_a0")] {
        let params = &p.functions[&fid].signature.params;
        assert_eq!(
            params.last().map(|q| q.name.as_str()),
            Some(want),
            "{} params: {:?}",
            p.functions[&fid].name,
            params.iter().map(|q| &q.name).collect::<Vec<_>>()
        );
        assert_eq!(params.last().unwrap().ty, Type::UInt(64));
    }
    assert_eq!(
        p.functions[&WRAPPER].body,
        value(call(
            LOOP,
            vec![var("i"), var("v"), Expr::Var(VarId::from("__la_p0"))]
        )),
        "the wrapper must forward its capture into the loop"
    );

    // The host keeps its pre-consumption stmts and tail-calls the wrapper
    // with the capture appended; the remainder moved into the continuation.
    let cont = manufactured_cont(&p);
    let host = &p.functions[&F_ABORTS];
    assert_eq!(host.body.stmts, vec![let1("i0", lit_u64(0))]);
    assert_eq!(
        host.body.tail,
        BlockTail::Value(call(WRAPPER, vec![var("v"), var("i0"), var("v")]))
    );
    assert_eq!(
        p.functions[&cont]
            .signature
            .params
            .iter()
            .map(|q| (q.name.as_str(), q.ty.clone()))
            .collect::<Vec<_>>(),
        vec![("v", Type::UInt(64)), ("acc", Type::Bool)],
        "the accumulator is the continuation's LAST parameter"
    );
    assert_eq!(
        p.functions[&cont].signature.return_type,
        types.option_abort_code_type()
    );

    // `.after`'s function-tail `Return` of the accumulator now delivers the
    // continuation -- and stays a `Return`, so a nested early exit keeps
    // exiting the function.
    assert_eq!(
        p.functions[&AFTER].body.tail,
        BlockTail::Return(Box::new(call(
            cont,
            vec![Expr::Var(VarId::from("__la_a0")), var("r")]
        ))),
    );
}

#[test]
fn try_string_shape_splices_the_dropped_callee_abort_into_the_loop() {
    let (mut p, aborts_map, _) = chain_program(Shape::TryString, Consumption::Live, true);

    // Before: the loop calls `g` and never its abort companion.
    assert!(!callees(&p.functions[&LOOP].body).contains(&G_ABORTS));

    aborts_live_loop::run_labeled_wrapper_loops(&mut p, &aborts_map).expect("fold");

    let body = &p.functions[&LOOP].body;
    assert!(
        matches!(
            body.stmts.first(),
            Some(Stmt::Let {
                value: Expr::Call { fun: G_ABORTS, .. },
                ..
            })
        ),
        "the loop must open with the spliced `let __c = g.aborts(v)`, got {:?}",
        body.stmts
    );
    assert!(
        callees(body).contains(&G),
        "the guarded original call must be preserved"
    );
    // The early-exit accumulator leaf routes into the continuation.
    let cont = manufactured_cont(&p);
    assert!(callees(body).contains(&cont));
}

// ---------------------------------------------------------------------------
// The `voting_power::insert` shape.
// ---------------------------------------------------------------------------

#[test]
fn insert_shape_discharges_the_fabricated_abort_placeholder() {
    let (mut p, aborts_map, types) = chain_program(Shape::Insert, Consumption::Live, true);

    assert!(
        has_abort_tail(&p.functions[&AFTER].body),
        "fixture must start from the fabricated abort-code-0 placeholder"
    );

    aborts_live_loop::run_labeled_wrapper_loops(&mut p, &aborts_map).expect("fold");

    let cont = manufactured_cont(&p);
    for fid in [WRAPPER, LOOP, AFTER, cont] {
        assert!(
            !has_abort_tail(&p.functions[&fid].body),
            "{} still fabricates an abort placeholder: {:?}",
            p.functions[&fid].name,
            p.functions[&fid].body
        );
    }

    // The Aborted arm now propagates its own bound payload.
    let BlockTail::Value(Expr::Match { cases, .. }) = &p.functions[&AFTER].body.tail else {
        panic!(
            "expected the spliced Match, got {:?}",
            p.functions[&AFTER].body
        );
    };
    let aborted = cases
        .iter()
        .find(|a| a.variant == OPTION_SOME_TAG)
        .expect("Aborted arm");
    assert_eq!(
        aborted.body.tail,
        BlockTail::Value(Expr::Pack {
            struct_id: types.option,
            type_args: vec![types.abort_code_type()],
            variant: Some(OPTION_SOME_TAG),
            fields: vec![var("__c_1")],
        }),
    );
}

#[test]
fn insert_shape_anf_lifts_a_tail_position_abortable_leaf() {
    let (mut p, aborts_map, _) = chain_program(Shape::Insert, Consumption::Live, true);

    aborts_live_loop::run_labeled_wrapper_loops(&mut p, &aborts_map).expect("fold");

    // The early-exit leaf `g(v)` was a tail-position call, which the
    // callee-aborts splice detects only in STATEMENT position. Lifting it
    // into a `let` is what lets the splice guard it -- so `g.aborts` must
    // appear twice in the loop: once for the statement-position `let t =
    // g(v)`, once for the lifted leaf.
    let body = &p.functions[&LOOP].body;
    let targets: std::collections::BTreeSet<usize> = std::iter::once(G_ABORTS).collect();
    assert_eq!(
        aborts_variant::count_calls_to(body, &targets)
            .get(&G_ABORTS)
            .copied(),
        Some(2),
        "both the statement-position call and the ANF-lifted leaf must be guarded: {body:?}"
    );
}

// ---------------------------------------------------------------------------
// Declines -- each of these would be a wrong transformation.
// ---------------------------------------------------------------------------

#[test]
fn declines_a_dead_consumption() {
    // Phase 3a.5b owns this shape: it DEADENS the accumulator rather than
    // threading it, and doing both would double-convert the chain.
    let (mut p, aborts_map, _) = chain_program(Shape::TryString, Consumption::Dead, true);
    let before = return_types(&p);

    aborts_live_loop::run_labeled_wrapper_loops(&mut p, &aborts_map).expect("fold");

    assert_eq!(before, return_types(&p));
}

#[test]
fn declines_a_chain_with_no_dropped_callee_abort() {
    // Nothing to recover, so the chain must come out byte-identical --
    // over-application changes output that works today.
    let (mut p, aborts_map, _) = chain_program(Shape::TryString, Consumption::Live, false);
    let before: Vec<Function> = [WRAPPER, LOOP, AFTER, F_ABORTS]
        .iter()
        .map(|fid| p.functions[fid].clone())
        .collect();

    aborts_live_loop::run_labeled_wrapper_loops(&mut p, &aborts_map).expect("fold");

    let after: Vec<Function> = [WRAPPER, LOOP, AFTER, F_ABORTS]
        .iter()
        .map(|fid| p.functions[fid].clone())
        .collect();
    assert_eq!(before, after);
}

#[test]
fn declines_when_the_wrapper_has_more_than_one_call_site() {
    // The fold appends parameters to the wrapper; a second site would keep
    // calling it at the old arity.
    let (mut p, aborts_map, _) = chain_program(Shape::TryString, Consumption::LiveTwice, true);
    let before = return_types(&p);

    aborts_live_loop::run_labeled_wrapper_loops(&mut p, &aborts_map).expect("fold");

    assert_eq!(before, return_types(&p));
}

#[test]
fn declines_when_the_loop_is_reachable_from_outside_the_chain() {
    // `append_trailing_args` threads the fresh params only into the wrapper
    // and the loop itself, so any other caller would be left short an arg.
    let (mut p, aborts_map, _) = chain_program(Shape::TryString, Consumption::Live, true);
    p.functions.insert(
        99,
        func(
            "other.aborts",
            sig(vec![param("i", Type::UInt(64))], Type::Bool),
            value(call(LOOP, vec![var("i"), var("i")])),
            FunctionKind::Synthetic,
        ),
    );
    let before = return_types(&p);

    aborts_live_loop::run_labeled_wrapper_loops(&mut p, &aborts_map).expect("fold");

    assert_eq!(before, return_types(&p));
}
