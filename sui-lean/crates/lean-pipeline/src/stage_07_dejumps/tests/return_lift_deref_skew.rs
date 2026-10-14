//! `return_lift` may not retype a slot the program already dereferences.
//!
//! `infer_let_value_type` recovers an SSA merge slot's "stable" type from an
//! earlier generation of the same stem, to undo a merge arm that holds a
//! BORROW of a carried slot (`&u64`) whose carrier is really the value
//! (`u64`). But `operand_normalization` -- Move's implicit auto-deref, which
//! stage 2 elides and later stages re-materialise -- already ran post-SSA and
//! wrapped every reference-typed operand in a `ReadRef`, using `type_of`'s
//! reading of that same slot. Demoting `&T` to `T` afterwards strands the
//! `ReadRef` on a value, and `ir-type-inference-succeeds` fails with
//! `MalformedAccess { ReadRef of non-reference type .. }`.
//!
//! The fixture is navi `lending_core::incentive::earned`'s shape at the
//! stage-7 boundary:
//!
//! ```move
//! let user_acc_rewards_paid = 0;                        // x_0 : u256
//! if (table::contains(paids, account)) {
//!     user_acc_rewards_paid = *table::borrow(paids, account);   // x_1 : &u256
//! };
//! .. *vector::borrow(rewards, i) - user_acc_rewards_paid ..     // *x_2
//! ```
//!
//! The `if` becomes an SSA merge of a `&u256` arm and a `u256` arm; the
//! callee-abort splice inside the borrow arm carries the inner `Return` that
//! makes `return_lift` lift the whole merge `let`, so `x_2` becomes a
//! continuation parameter with a DECLARED type -- the point at which the
//! disagreement stops being invisible.
//!
//! The renderer erases references (`&u256` and `u256` render alike), so this
//! never surfaces downstream: the invariant is the only thing that reports it.

use ethnum::U256;

use crate::ir::invariants::baseline::IrTypeInferenceSucceeds;
use crate::ir::invariants::Invariant;
use crate::ir::{
    Block, BlockTail, Const, Effects, Expr, Function, FunctionKind, MatchArm, Module, Param,
    Program, Signature, SpecKind, Stmt, Type, VarId,
};

use crate::stage_07_dejumps::option_aborts::{self, OPTION_NONE_TAG, OPTION_SOME_TAG};
use crate::stage_07_dejumps::return_lift;

/// `borrow(&u256) -> &u256` -- the `table::borrow` stand-in.
const BORROW: usize = 0;
const BORROW_ABORTS: usize = 1;
/// `sink(u256) -> u256` -- consumes the merged slot BY VALUE, which is why
/// `operand_normalization` wrapped its argument in a `ReadRef`.
const SINK: usize = 2;
const F: usize = 3;
const F_ABORTS: usize = 4;

fn module() -> Module {
    Module {
        name: "incentive".to_string(),
        package_name: "lending_core".to_string(),
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

fn var(name: &str) -> Expr {
    Expr::Var(VarId::from(name))
}

fn let1(name: &str, value: Expr) -> Stmt {
    Stmt::Let {
        pattern: vec![Some(VarId::from(name))],
        value,
    }
}

fn call(fid: usize, args: Vec<Expr>) -> Expr {
    Expr::Call {
        fun: fid,
        type_args: Vec::new(),
        args,
    }
}

fn value(e: Expr) -> Block {
    Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(e),
    }
}

fn u256(n: u64) -> Expr {
    Expr::Const(Const::UInt {
        bits: 256,
        value: U256::from(n),
    })
}

fn u256_ref() -> Type {
    Type::Reference(Box::new(Type::UInt(256)))
}

/// `f.aborts`, with the merged slot consumed either through a `ReadRef`
/// (`*x_2`, what `operand_normalization` leaves behind) or directly.
fn fixture(dereference_the_slot: bool) -> (Program, crate::ir::StructId) {
    let mut p = Program::default();
    p.modules.insert(0, module());

    p.functions.insert(
        BORROW,
        func(
            "borrow",
            vec![param("t", u256_ref())],
            u256_ref(),
            value(var("t")),
            FunctionKind::Source,
        ),
    );
    p.functions.insert(
        SINK,
        func(
            "sink",
            vec![param("v", Type::UInt(256))],
            Type::UInt(256),
            value(var("v")),
            FunctionKind::Source,
        ),
    );
    p.functions.insert(
        F,
        func(
            "earned",
            vec![param("c", Type::Bool), param("t", u256_ref())],
            Type::UInt(256),
            value(u256(0)),
            FunctionKind::Source,
        ),
    );

    let types = option_aborts::ensure_aborts_types(&mut p);
    let abort_result = types.option_abort_code_type();

    p.functions.insert(
        BORROW_ABORTS,
        func(
            "borrow.aborts",
            vec![param("t", u256_ref())],
            abort_result.clone(),
            value(types.make_none()),
            FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target: BORROW,
            },
        ),
    );

    // `let x_1 = borrow(t)` guarded by the callee-abort splice. The Aborted
    // arm's inner `Return` is what makes `return_lift` lift the enclosing
    // merge `let`.
    let borrow_arm = Block {
        stmts: vec![let1("__c_0", call(BORROW_ABORTS, vec![var("t")]))],
        tail: BlockTail::Value(Expr::Match {
            struct_id: types.option,
            selector: Box::new(var("__c_0")),
            cases: vec![
                MatchArm {
                    variant: OPTION_NONE_TAG,
                    bindings: vec![],
                    body: Box::new(Block {
                        stmts: vec![let1("x_1", call(BORROW, vec![var("t")]))],
                        tail: BlockTail::Value(var("x_1")),
                    }),
                },
                MatchArm {
                    variant: OPTION_SOME_TAG,
                    bindings: vec![VarId::from("__c_1")],
                    body: Box::new(Block {
                        stmts: Vec::new(),
                        tail: BlockTail::Return(Box::new(var("__c_0"))),
                    }),
                },
            ],
        }),
    };

    let consumed = if dereference_the_slot {
        Expr::ReadRef(Box::new(var("x_2")))
    } else {
        var("x_2")
    };

    let body = Block {
        stmts: vec![
            let1("x_0", u256(0)),
            let1(
                "x_2",
                Expr::If {
                    cond: Box::new(var("c")),
                    then_branch: Box::new(borrow_arm),
                    else_branch: Box::new(value(var("x_0"))),
                },
            ),
            Stmt::Eval(call(SINK, vec![consumed])),
        ],
        tail: BlockTail::Value(types.make_none()),
    };

    p.functions.insert(
        F_ABORTS,
        func(
            "earned.aborts",
            vec![param("c", Type::Bool), param("t", u256_ref())],
            abort_result,
            body,
            FunctionKind::Spec {
                kind: SpecKind::Aborts,
                target: F,
            },
        ),
    );
    (p, types.option)
}

fn slot_param_type(p: &Program, slot: &str) -> Type {
    p.functions
        .values()
        .filter(|f| f.name.starts_with("earned.aborts.cont_"))
        .find_map(|f| {
            f.signature
                .params
                .iter()
                .find(|param| param.var.as_ref() == slot)
                .map(|param| param.ty.clone())
        })
        .unwrap_or_else(|| panic!("no continuation carries `{slot}`"))
}

/// The property, not one function's output: after the lift, every expression
/// in every body still types.
fn assert_well_typed(p: &Program) {
    if let Err(violations) = IrTypeInferenceSucceeds.check(p) {
        let detail: Vec<String> = violations
            .iter()
            .map(|v| {
                let name = v
                    .function
                    .and_then(|fid| p.functions.get(&fid))
                    .map(|f| f.name.clone())
                    .unwrap_or_default();
                format!("[{name}] {}", v.detail)
            })
            .collect();
        panic!(
            "return_lift left the IR ill-typed:\n  {}",
            detail.join("\n  ")
        );
    }
}

/// The regression. `x_2` merges a `&u256` arm with a `u256` arm and is read
/// as `*x_2`; the stable-generation correction used to demote it to `u256`
/// on `x_0`'s evidence, stranding that `*` on a value.
#[test]
fn a_dereferenced_merge_slot_survives_the_lift_well_typed() {
    let (mut p, _) = fixture(true);
    return_lift::run(&mut p).expect("return_lift");
    assert_well_typed(&p);
    assert_eq!(slot_param_type(&p, "x_2"), u256_ref());
}

/// ...and the correction is not simply switched off: with no `*x_2` in the
/// body, nothing has been normalized against the reference reading, so the
/// slot still takes its stable generation's value type.
#[test]
fn an_undereferenced_merge_slot_still_takes_its_stable_generation_type() {
    let (mut p, _) = fixture(false);
    return_lift::run(&mut p).expect("return_lift");
    assert_well_typed(&p);
    assert_eq!(slot_param_type(&p, "x_2"), Type::UInt(256));
}

/// The set is taken from the WHOLE body before the first lift, because each
/// lift moves code out into a `cont_N`. navi
/// `incentive::base_claim_reward.aborts` is the shape that needs it: the
/// merge is bound in the parent and its only `*` ends up two continuations
/// deep. A set recomputed per iteration no longer sees it.
#[test]
fn a_dereference_is_seen_even_when_it_migrates_into_a_deeper_continuation() {
    let (mut p, types_option) = fixture(true);
    // Push the consumer behind a second callee-abort splice, so the first
    // lift moves it into `cont_0` and only a later lift binds the slot.
    let f = p.functions.get_mut(&F_ABORTS).unwrap();
    let consumer = f.body.stmts.pop().expect("the sink statement");
    let tail = std::mem::replace(&mut f.body.tail, BlockTail::Value(Expr::Unit));
    f.body
        .stmts
        .push(let1("__c_2", call(BORROW_ABORTS, vec![var("t")])));
    f.body.tail = BlockTail::Value(Expr::Match {
        struct_id: types_option,
        selector: Box::new(var("__c_2")),
        cases: vec![
            MatchArm {
                variant: OPTION_NONE_TAG,
                bindings: vec![],
                body: Box::new(Block {
                    stmts: vec![consumer],
                    tail,
                }),
            },
            MatchArm {
                variant: OPTION_SOME_TAG,
                bindings: vec![VarId::from("__c_3")],
                body: Box::new(Block {
                    stmts: Vec::new(),
                    tail: BlockTail::Return(Box::new(var("__c_2"))),
                }),
            },
        ],
    });

    return_lift::run(&mut p).expect("return_lift");
    assert_well_typed(&p);
}
