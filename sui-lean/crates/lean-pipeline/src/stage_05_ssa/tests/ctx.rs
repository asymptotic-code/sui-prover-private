//! Tests for `Ctx::fresh`, `lookup`, `bind`, `push_loop`, `loop_at`.

use crate::ir::VarId;
use crate::stage_05_ssa::{Ctx, LoopFrame, Stage5Error};

#[test]
fn fresh_advances_counter_per_base() {
    let mut ctx = Ctx::new(0);
    let a: VarId = "a".into();
    let b: VarId = "b".into();
    assert_eq!(&*ctx.fresh(&a), "a_0");
    assert_eq!(&*ctx.fresh(&a), "a_1");
    assert_eq!(&*ctx.fresh(&b), "b_0");
    assert_eq!(&*ctx.fresh(&a), "a_2");
}

#[test]
fn bind_then_lookup() {
    let mut ctx = Ctx::new(0);
    let a: VarId = "a".into();
    let a0 = ctx.fresh(&a);
    ctx.bind(a.clone(), a0.clone());
    assert_eq!(ctx.lookup(&a).unwrap(), a0);
}

#[test]
fn lookup_unbound_var_rejects() {
    let ctx = Ctx::new(7);
    let v: VarId = "v".into();
    let err = ctx.lookup(&v).unwrap_err();
    assert_eq!(
        err,
        Stage5Error::UnboundReference {
            function: 7,
            var: v,
        }
    );
}

#[test]
fn scope_clone_isolates_arm_bindings() {
    let mut outer = Ctx::new(0);
    let x: VarId = "x".into();
    let x0 = outer.fresh(&x);
    outer.bind(x.clone(), x0.clone());

    // Clone for an arm; bind a fresh name inside the arm.
    let mut arm = outer.clone();
    let x1 = arm.fresh(&x);
    arm.bind(x.clone(), x1.clone());
    assert_eq!(arm.lookup(&x).unwrap(), x1);

    // Outer scope unaffected.
    assert_eq!(outer.lookup(&x).unwrap(), x0);
}

#[test]
fn loop_stack_push_pop_and_lookup_by_level() {
    let mut ctx = Ctx::new(0);
    let outer = LoopFrame {
        loop_state: vec!["i".into()],
    };
    let inner = LoopFrame {
        loop_state: vec!["j".into(), "k".into()],
    };

    ctx.push_loop(outer.clone());
    ctx.push_loop(inner.clone());

    // level 0 = innermost
    assert_eq!(ctx.loop_at(0).unwrap().loop_state, inner.loop_state);
    // level 1 = next out
    assert_eq!(ctx.loop_at(1).unwrap().loop_state, outer.loop_state);
    // level 2 = out of bounds
    assert!(ctx.loop_at(2).is_none());

    let popped = ctx.pop_loop().unwrap();
    assert_eq!(popped.loop_state, inner.loop_state);
    assert_eq!(ctx.loop_at(0).unwrap().loop_state, outer.loop_state);
}
