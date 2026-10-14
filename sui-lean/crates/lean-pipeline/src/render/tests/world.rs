//! Stage-4 (effects) end-to-end render tests: verify that an Impure
//! function with `world: World` in its signature renders to the
//! expected Lean source.

use crate::ir::{Block, BlockTail, Expr, Stmt, Type};
use crate::render::render_program;
use crate::stage_04_effects;

use super::fixtures::*;

#[test]
fn world_struct_renders_as_world_abbreviation() {
    // To trigger stage 4 augmentation we need an actual transitive
    // dependency on a GlobalMut native; `classify_effects`
    // re-derives body effects at stage 4 entry and would demote a
    // bare `effects = CONSERVATIVE` fixture to `PURE` otherwise.
    // Build a native `transfer::transfer` plus a caller that uses
    // it.
    let mut prog = empty_program();

    let mut signature = sig(
        vec![param("o", Type::UInt(64)), param("a", Type::Address)],
        Type::Unit,
    );
    signature.type_params = vec!["T".to_string()];
    let transfer = native(
        "transfer",
        signature,
        0,
        crate::ir::Effects::CONSERVATIVE,
        true,
    );
    add_native(&mut prog, 0, transfer);

    let caller = func(
        "do_transfer",
        sig(vec![], Type::Unit),
        body(
            vec![Stmt::Eval(Expr::Call {
                fun: 0,
                type_args: vec![Type::UInt(64)],
                args: vec![
                    lit_u64(7),
                    Expr::Const(crate::ir::Const::Address(num::BigUint::from(0u8))),
                ],
            })],
            Expr::Unit,
        ),
        0,
    );
    add_function(&mut prog, 1, caller);

    stage_04_effects::run(&mut prog).expect("stage 4");
    let out = render_program(&prog).expect("render");

    // Stage 4 should have appended `world: World` and made the
    // return type `Tuple([World])` (rendered as just `World` by the
    // singleton-tuple collapse).
    assert!(
        out.contains("(world : World)"),
        "expected world param in output, got:\n{}",
        out
    );
    assert!(
        out.contains(": World :="),
        "expected World return type in output, got:\n{}",
        out
    );
    // The Prelude.World import must be present.
    assert!(
        out.contains("import Prelude.World"),
        "expected Prelude.World import, got:\n{}",
        out
    );
    // The per-package abbreviation must be present.
    assert!(
        out.contains("abbrev World := Prover.World.World AnyEvent AnyObject Unit Unit"),
        "expected World abbreviation in output, got:\n{}",
        out
    );
}

#[test]
fn impure_emitter_with_event_native_renders_threaded_world() {
    // Two functions: native `event::emit`, and a user caller that
    // emits a u64 event. Stage 4 threads world through both.
    let mut prog = empty_program();

    let mut signature = sig(vec![param("e", Type::UInt(64))], Type::Unit);
    signature.type_params = vec!["T".to_string()];
    let event_emit = native("emit", signature, 0, crate::ir::Effects::CONSERVATIVE, true);
    add_native(&mut prog, 0, event_emit);

    let mut caller = func(
        "fire",
        sig(vec![], Type::Unit),
        body(
            vec![Stmt::Eval(Expr::Call {
                fun: 0,
                type_args: vec![Type::UInt(64)],
                args: vec![lit_u64(42)],
            })],
            Expr::Unit,
        ),
        0,
    );
    caller.effects = crate::ir::Effects::CONSERVATIVE;
    add_function(&mut prog, 1, caller);

    stage_04_effects::run(&mut prog).expect("stage 4");
    let out = render_program(&prog).expect("render");

    // Per cd9bf803's placeholder-AnyEvent strategy, per-call variants
    // land as comments in the per-package `Generated/AnyEvent.lean`
    // header. The inlined single-string `render_program` output
    // strips those header comments (see `mod.rs::render_program_*`'s
    // `skip_while` on the inlined `any_event_body`), so we cannot
    // assert against `k_u64` here -- the unit placeholder is what
    // the in-memory render emits. Variant collection itself is
    // covered by `render::world::collect_any_event_object` tests.
    assert!(
        out.contains("inductive AnyEvent"),
        "expected AnyEvent inductive in output, got:\n{}",
        out
    );
    // Caller's signature: `(world : World) : World`.
    assert!(
        out.contains("(world : World)"),
        "expected world param in caller, got:\n{}",
        out
    );
    // The emit Call has `world` threaded as its final arg.
    assert!(
        out.contains("emit") && out.contains(" world)"),
        "expected world threaded through emit call, got:\n{}",
        out
    );
}

#[test]
fn pure_function_does_not_get_world_anywhere() {
    let mut prog = empty_program();
    let mut f = func(
        "add_one",
        sig(vec![param("a", Type::UInt(64))], Type::UInt(64)),
        body(vec![], add(var("a"), lit_u64(1))),
        0,
    );
    f.effects = crate::ir::Effects {
        aborts: crate::ir::AbortBit::Partial,
        det: crate::ir::DetBit::Det,
        mutation: crate::ir::MutLevel::NoMut,
        world_writes: false,
    };
    add_function(&mut prog, 0, f);

    stage_04_effects::run(&mut prog).expect("stage 4");
    let out = render_program(&prog).expect("render");

    // Pure function signature must NOT contain world.
    // (Find the `def add_one` line and check the head.)
    let signature_line = out
        .lines()
        .find(|l| l.contains("def add_one"))
        .expect("def add_one line");
    assert!(
        !signature_line.contains("world"),
        "pure function got world in signature: {}",
        signature_line
    );
    assert!(
        !signature_line.contains("World"),
        "pure function got World type in signature: {}",
        signature_line
    );
}

#[test]
fn abort_tail_uses_non_trailing_lifecycle_world() {
    let mut prog = empty_program();
    let world_id = stage_04_effects::ensure_world_struct(&mut prog);
    let world_ty = stage_04_effects::world_type(world_id);
    add_function(
        &mut prog,
        0,
        func(
            "abort_with_capture",
            sig(
                vec![
                    param("world_4", world_ty.clone()),
                    param("capture", Type::UInt(64)),
                ],
                Type::Tuple(vec![Type::UInt(64), world_ty]),
            ),
            Block {
                stmts: Vec::new(),
                tail: BlockTail::Abort {
                    code: Box::new(lit_u64(7)),
                },
            },
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("(default, world_4)"),
        "abort tail must preserve the non-trailing lifecycle World:\n{out}"
    );
}

#[test]
fn abort_tail_prefers_newest_canonical_world_over_trailing_snapshot() {
    let mut prog = empty_program();
    let world_id = stage_04_effects::ensure_world_struct(&mut prog);
    let world_ty = stage_04_effects::world_type(world_id);
    add_function(
        &mut prog,
        0,
        func(
            "abort_with_snapshots",
            sig(
                vec![
                    param("world_1", world_ty.clone()),
                    param("world_8", world_ty.clone()),
                    param("world_snapshot", world_ty.clone()),
                ],
                Type::Tuple(vec![Type::UInt(64), world_ty]),
            ),
            Block {
                stmts: Vec::new(),
                tail: BlockTail::Abort {
                    code: Box::new(lit_u64(7)),
                },
            },
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("(default, world_8)"),
        "abort tail must preserve the newest canonical World:\n{out}"
    );
    assert!(
        !out.contains("(default, world_snapshot)"),
        "abort tail must not preserve a stale snapshot:\n{out}"
    );
}

#[test]
fn abort_loop_tail_prefers_live_accumulator_world() {
    let mut prog = empty_program();
    let world_id = stage_04_effects::ensure_world_struct(&mut prog);
    let world_ty = stage_04_effects::world_type(world_id);
    let mut after = func(
        "source.aborts.while_0.after",
        sig(
            vec![
                param("world_0", world_ty.clone()),
                param("__la_world_a", world_ty.clone()),
            ],
            Type::Tuple(vec![Type::UInt(64), world_ty]),
        ),
        Block {
            stmts: Vec::new(),
            tail: BlockTail::Abort {
                code: Box::new(lit_u64(7)),
            },
        },
        0,
    );
    after.kind = crate::ir::FunctionKind::LoopAfter { parent: 3, slot: 0 };
    add_function(&mut prog, 0, after);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("(default, __la_world_a)"),
        "abort-loop tails must preserve the continuation World:\n{out}"
    );
    assert!(
        !out.contains("(default, world_0)"),
        "abort-loop tails must not restore the loop snapshot:\n{out}"
    );
}
