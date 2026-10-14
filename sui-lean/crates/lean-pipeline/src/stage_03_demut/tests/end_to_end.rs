//! End-to-end tests for `stage_03_demut::run`.
//!
//! Constructs a small `Program` with a `&mut`-taking function plus a
//! caller, runs the full pipeline (`run`), and asserts both
//! signatures and bodies are demoted as expected.

use crate::ir::builder::{lit_u64, var};
use crate::ir::{Block, BlockTail, BorrowEdge, BorrowNode, Expr, Stmt, Type, VarId};
use crate::stage_03_demut::run;

use super::fixtures::{func, mut_ref, param, program_with, sig, FuncOpts};

const STRUCT_S: usize = 7;

fn t() -> Type {
    Type::UInt(64)
}

fn vid(name: &str) -> VarId {
    VarId::from(name)
}

#[test]
fn end_to_end_unit_returning_mut_function() {
    // g(x: &mut T): () { *x = 42 }
    // After demut:
    //   g(x: T): T {
    //       let x = path_to_update(x, [], 42) = 42
    //       x
    //   }
    let g_body = Block {
        stmts: vec![Stmt::Eval(Expr::WriteRef {
            reference: Box::new(var("r0")),
            value: Box::new(lit_u64(42)),
        })],
        tail: BlockTail::Value(Expr::Unit),
    };
    // Stage 2 emits BorrowLoc(x) before the WriteRef.
    let g_body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some(vid("r0"))],
                value: Expr::BorrowLoc(vid("x")),
            },
            Stmt::Eval(Expr::WriteRef {
                reference: Box::new(var("r0")),
                value: Box::new(lit_u64(42)),
            }),
        ],
        tail: g_body.tail,
    };
    let g = func(
        "g",
        sig(vec![param("x", mut_ref(t(), t()))], Type::Unit),
        g_body,
        FuncOpts::default(),
    );

    let mut prog = program_with(vec![(0, g)]);
    run(&mut prog).expect("stage 3 run should succeed");

    let g = &prog.functions[&0];
    // Signature: x: T (stripped), return: T (no augmentation since unit return + 1 mut).
    assert_eq!(g.signature.params[0].ty, t());
    assert_eq!(g.signature.return_type, t());

    // Body's WriteRef has been replaced with `let x = path_to_update(x, [], 42) = 42`.
    let stmts = &g.body.stmts;
    assert_eq!(stmts.len(), 2);
    match &stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(vid("x"))]);
            assert_eq!(value, &lit_u64(42));
        }
        other => panic!("expected Stmt::Let rebinding x, got {:?}", other),
    }

    // Body tail: was Value(Unit), now Value(Var(x)) (one mut, unit return).
    match &g.body.tail {
        BlockTail::Value(Expr::Var(name)) => assert_eq!(name, &vid("x")),
        other => panic!("expected Value(Var(x)), got {:?}", other),
    }
}

#[test]
fn end_to_end_caller_destructures_augmented_return() {
    // g(x: &mut T): R { *x = 42; 7 }   // R simple, augmented to (R, T).
    // caller(arg: &mut T): () { let r = g(&mut arg); }
    //
    // After demut:
    //   g(x: T): (R, T) { let x = 42; (7, x) }
    //   caller(arg: T): T {
    //       let r0 = BorrowLoc(arg);
    //       let (r, arg) = g(r0);    // augmented destructure
    //       arg                      // tail
    //   }
    let g_body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some(vid("r0"))],
                value: Expr::BorrowLoc(vid("x")),
            },
            Stmt::Eval(Expr::WriteRef {
                reference: Box::new(var("r0")),
                value: Box::new(lit_u64(42)),
            }),
        ],
        tail: BlockTail::Value(lit_u64(7)),
    };
    let g = func(
        "g",
        sig(vec![param("x", mut_ref(t(), t()))], t()),
        g_body,
        FuncOpts::default(),
    );

    let caller_body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some(vid("r0"))],
                value: Expr::BorrowLoc(vid("arg")),
            },
            Stmt::Let {
                pattern: vec![Some(vid("r"))],
                value: Expr::Call {
                    fun: 0,
                    type_args: Vec::new(),
                    args: vec![var("r0")],
                },
            },
        ],
        tail: BlockTail::Value(Expr::Unit),
    };
    let caller = func(
        "caller",
        sig(vec![param("arg", mut_ref(t(), t()))], Type::Unit),
        caller_body,
        FuncOpts::default(),
    );

    let mut prog = program_with(vec![(0, g), (1, caller)]);
    run(&mut prog).expect("stage 3 run should succeed");

    // g's signature: (x: T): (T, T) since R=T and one mut.
    let g_after = &prog.functions[&0];
    assert_eq!(g_after.signature.return_type, Type::Tuple(vec![t(), t()]));

    // caller's call site was rewritten to `let (r, r0) = g(r0)`.
    let caller_after = &prog.functions[&1];
    match &caller_after.body.stmts[1] {
        Stmt::Let { pattern, .. } => {
            assert_eq!(pattern, &vec![Some(vid("r")), Some(vid("r0"))]);
        }
        other => panic!("expected augmented destructure, got {:?}", other),
    }

    // caller's tail: was Unit, now Var(arg) (one mut, unit return).
    match &caller_after.body.tail {
        BlockTail::Value(Expr::Var(name)) => assert_eq!(name, &vid("arg")),
        other => panic!("expected Value(Var(arg)), got {:?}", other),
    }
}

#[test]
fn end_to_end_writeback_chain_lowers() {
    // f(local: T): T { let r0 = BorrowLoc(local);
    //                   WriteBack(LocalRoot(local), Direct, r0) }
    // After demut: writeback becomes `let local = ReadRef(r0)`.
    // (No mut params -- f is NOT in the demotion set, but rewrite_writebacks
    // still runs over its body.)
    let f_body = Block {
        stmts: vec![
            Stmt::Let {
                pattern: vec![Some(vid("r0"))],
                value: Expr::BorrowLoc(vid("local")),
            },
            Stmt::Eval(Expr::WriteBack {
                node: BorrowNode::LocalRoot(vid("local")),
                edge: BorrowEdge::Direct,
                child: vid("r0"),
                world: None,
            }),
        ],
        tail: BlockTail::Value(var("local")),
    };
    let f = func(
        "f",
        sig(vec![param("local", t())], t()),
        f_body,
        FuncOpts::default(),
    );
    let mut prog = program_with(vec![(0, f)]);
    run(&mut prog).expect("stage 3 run should succeed");

    let f_after = &prog.functions[&0];
    match &f_after.body.stmts[1] {
        Stmt::Let { pattern, value } => {
            assert_eq!(pattern, &vec![Some(vid("local"))]);
            assert_eq!(value, &Expr::ReadRef(Box::new(var("r0"))));
        }
        other => panic!("expected WriteBack rebind, got {:?}", other),
    }
}
