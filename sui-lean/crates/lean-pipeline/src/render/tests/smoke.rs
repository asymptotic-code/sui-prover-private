//! End-to-end smoke tests: build a small `Program`, render it, assert
//! the full Lean source text. Catches regressions across the entire
//! render path (types + expressions + functions + module wiring).

use crate::ir::{Expr, Function, FunctionKind, Type};
use crate::render::{render_program, RenderError};

use super::fixtures::*;

#[test]
fn add_two_u64() {
    // fn add(a: u64, b: u64): u64 { a + b }
    let mut prog = empty_program();
    let f = func(
        "add",
        sig(
            vec![param("a", Type::UInt(64)), param("b", Type::UInt(64))],
            Type::UInt(64),
        ),
        body(vec![], add(var("a"), var("b"))),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    let expected = "\
import Prelude.BoundedNat
import Prelude.ProgramState
import Prelude.Mutation
import Prelude.TypedMap
import Prelude.World

inductive AnyKey where
  | unit
  deriving BEq

class ToAnyKey (A : Type) where
  toAnyKey : A -> AnyKey

class FromAnyKey (A : Type) where
  fromAnyKey : AnyKey -> A

instance (priority := low) {A : Type} [ToAnyKey A] : IntoKey AnyKey A where intoKey := ToAnyKey.toAnyKey
instance (priority := low) {A : Type} [FromAnyKey A] : FromKey AnyKey A where fromKey := FromAnyKey.fromAnyKey

class LawfulAnyKey (A : Type) [ToAnyKey A] [FromAnyKey A] : Prop where
  from_to : ∀ k : A, (FromAnyKey.fromAnyKey (ToAnyKey.toAnyKey k) : A) = k

abbrev Mutation := Prover.Mutation.Mutation AnyKey
abbrev Edge     := Prover.Mutation.Edge     AnyKey

inductive AnyEvent where
  | unit
  deriving Inhabited

inductive AnyObject where
  | unit
  deriving Inhabited

abbrev World := Prover.World.World AnyEvent AnyObject Unit Unit

namespace p.M

def add (a : BoundedNat (2^64)) (b : BoundedNat (2^64)) : BoundedNat (2^64) :=
  (a + b)

end p.M

";
    assert_eq!(out, expected);
}

#[test]
fn let_then_use() {
    // fn f(a: u64): u64 { let x = a + 1; x }
    let mut prog = empty_program();
    let f = func(
        "f",
        sig(vec![param("a", Type::UInt(64))], Type::UInt(64)),
        body(vec![let_("x", add(var("a"), lit_u64(1)))], var("x")),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    // The tail-let peephole (`render::expr::peephole_tail_let`)
    // inlines the single-use `let x := ...; x` into the tail.
    let expected = "\
import Prelude.BoundedNat
import Prelude.ProgramState
import Prelude.Mutation
import Prelude.TypedMap
import Prelude.World

inductive AnyKey where
  | unit
  deriving BEq

class ToAnyKey (A : Type) where
  toAnyKey : A -> AnyKey

class FromAnyKey (A : Type) where
  fromAnyKey : AnyKey -> A

instance (priority := low) {A : Type} [ToAnyKey A] : IntoKey AnyKey A where intoKey := ToAnyKey.toAnyKey
instance (priority := low) {A : Type} [FromAnyKey A] : FromKey AnyKey A where fromKey := FromAnyKey.fromAnyKey

class LawfulAnyKey (A : Type) [ToAnyKey A] [FromAnyKey A] : Prop where
  from_to : ∀ k : A, (FromAnyKey.fromAnyKey (ToAnyKey.toAnyKey k) : A) = k

abbrev Mutation := Prover.Mutation.Mutation AnyKey
abbrev Edge     := Prover.Mutation.Edge     AnyKey

inductive AnyEvent where
  | unit
  deriving Inhabited

inductive AnyObject where
  | unit
  deriving Inhabited

abbrev World := Prover.World.World AnyEvent AnyObject Unit Unit

namespace p.M

def f (a : BoundedNat (2^64)) : BoundedNat (2^64) :=
  (a + (1 : BoundedNat (2^64)))

end p.M

";
    assert_eq!(out, expected);
}

#[test]
fn large_uint_literal_renders_as_opaque_alias() {
    let mut prog = empty_program();
    let f = func(
        "wad",
        sig(vec![], Type::UInt(256)),
        body(vec![], lit_u256(1_000_000_000_000_000_000)),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains(
            "opaque large_uint_u256_1000000000000000000 : BoundedNat (2^256) := 1000000000000000000"
        ),
        "got:\n{}",
        out
    );
    assert!(
        out.contains(
            "@[move_effect]\ntheorem large_uint_u256_1000000000000000000_val : large_uint_u256_1000000000000000000.val = 1000000000000000000 := by\n  native_decide"
        ),
        "got:\n{}",
        out
    );
    assert!(
        out.contains("def wad : BoundedNat (2^256) :=\n  large_uint_u256_1000000000000000000"),
        "got:\n{}",
        out
    );
    // `move_effect` is what makes the fact reachable from every `move_norm*`
    // rung, and `register_simp_attr` syntax is usable only after import.
    assert!(
        out.contains("import Prover.MoveAutoAttr"),
        "a module emitting alias `_val` facts must import the attribute module, got:\n{}",
        out
    );
}

#[test]
fn a_literal_at_or_above_the_value_ceiling_is_emitted_unregistered() {
    // 2^64 exactly -- the first value ABOVE the ceiling. The alias and its
    // `_val` fact are still emitted (they are what the corpus proofs cite by
    // name); only the AMBIENT registration is withheld, because a literal this
    // wide is what blows `grind` up once `move_norm` puts it in a goal. What it
    // carries instead is `@[move_wide_val]`, a `register_simp_attr` set nothing
    // ambient consults -- citable by name, never automatic. That is the
    // census's absolute-blocker class (45 leaves, 0 closes) getting a route
    // that does not re-open the 18.2 GB OOM.
    let mut prog = empty_program();
    add_function(
        &mut prog,
        0,
        func(
            "ceiling",
            sig(vec![], Type::UInt(256)),
            body(vec![], lit_u256(18_446_744_073_709_551_616)),
            0,
        ),
    );

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains(
            "opaque large_uint_u256_18446744073709551616 : BoundedNat (2^256) := 18446744073709551616\n\n@[move_wide_val]\ntheorem large_uint_u256_18446744073709551616_val"
        ),
        "an above-ceiling `_val` fact must carry the scoped set and nothing else, got:\n{}",
        out
    );
    assert!(
        !out.contains("@[move_effect]"),
        "nothing in this module is AMBIENT, got:\n{}",
        out
    );
    assert!(
        out.contains("import Prover.MoveAutoAttr"),
        "`move_wide_val` is declared there too, and `register_simp_attr` syntax \
         is usable only downstream of its registration, got:\n{}",
        out
    );
}

#[test]
fn a_module_without_wide_literals_does_not_import_the_attribute_module() {
    let mut prog = empty_program();
    let f = func(
        "small",
        sig(vec![], Type::UInt(64)),
        body(vec![], lit_u64(7)),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(!out.contains("large_uint_"), "got:\n{}", out);
    assert!(
        !out.contains("import Prover.MoveAutoAttr"),
        "the attribute import is conditional on an alias actually being emitted, got:\n{}",
        out
    );
}

#[test]
fn generic_struct_and_function_use_decidable_eq() {
    let mut prog = empty_program();
    let mut box_struct = simple_struct(0, "Box", vec![("value", Type::TypeParam(0))]);
    box_struct.type_params = vec!["T".to_string()];
    box_struct.qualified_name = "p::m::Box".to_string();
    add_struct(&mut prog, 0, box_struct);

    let mut signature = sig(vec![param("x", Type::TypeParam(0))], Type::TypeParam(0));
    signature.type_params = vec!["T".to_string()];
    let f = func("id", signature, body(vec![], var("x")), 0);
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(out.contains("structure Box (T : Type) where\n  value : T\nderiving DecidableEq"));
    assert!(out.contains(
        "def id (T : Type) [DecidableEq T] [Inhabited T] [HasCode _root_.TyCode T] (x : T) : T :="
    ));
}

#[test]
fn literal_total_aborts_companion_is_marked_simp() {
    let mut prog = empty_program();
    let source = func(
        "is_empty",
        sig(vec![param("b", Type::Bool)], Type::Bool),
        body(vec![], var("b")),
        0,
    );
    add_function(&mut prog, 0, source);

    let aborts = Function {
        module: 0,
        name: "is_empty.aborts".to_string(),
        signature: sig(vec![param("b", Type::Bool)], Type::Bool),
        body: body(vec![], Expr::Const(crate::ir::Const::Bool(false))),
        kind: FunctionKind::Spec {
            kind: crate::ir::SpecKind::Aborts,
            target: 0,
        },
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
    };
    add_function(&mut prog, 1, aborts);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("@[simp]\ndef is_empty.aborts (b : Bool) : Bool :=\n  false"),
        "got:\n{}",
        out
    );
}

#[test]
fn abort_result_enum_gets_match_simp_theorems() {
    let mut prog = empty_program();
    crate::stage_07_dejumps::option_aborts::ensure_aborts_types(&mut prog);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("@[simp] theorem AbortResult.match_noAbort"),
        "got:\n{}",
        out
    );
    assert!(
        out.contains("@[simp] theorem AbortResult.match_aborted"),
        "got:\n{}",
        out
    );
}

#[test]
fn struct_containing_mutable_ref_field_is_rejected() {
    let mut prog = empty_program();
    add_struct(
        &mut prog,
        0,
        simple_struct(
            0,
            "Inner",
            vec![(
                "m",
                Type::MutableRef {
                    inner: Box::new(Type::Unit),
                    root: Box::new(Type::Unit),
                },
            )],
        ),
    );
    add_struct(
        &mut prog,
        1,
        simple_struct(
            0,
            "Outer",
            vec![(
                "inner",
                Type::Struct {
                    struct_id: 0,
                    type_args: vec![],
                },
            )],
        ),
    );

    let err = render_program(&prog).expect_err("mutable-ref fields should be rejected");
    assert!(matches!(
        err,
        RenderError::InvalidStructFieldType {
            struct_name,
            field_name,
            reason: "Move struct fields must not contain mutable references after stage 3",
        } if struct_name == "p::m::Inner" && field_name == "m"
    ));
}

#[test]
fn param_with_ssa_var_renders_as_display_name() {
    // fn double(a: u64): u64 { a + a }
    // Where the parameter's SSA var is "$t0" but display name is "a".
    use crate::ir::{
        AbortBit, BinOp, Block, BlockTail, DetBit, Effects, Expr, Function, FunctionKind, MutLevel,
        Param, Signature, Stmt, VarId,
    };
    use ethnum::U256;

    let mut prog = empty_program();
    let f = Function {
        module: 0,
        name: "double".to_string(),
        signature: Signature {
            type_params: vec![],
            params: vec![Param {
                name: "a".to_string(),
                var: VarId::from("$t0"),
                ty: crate::ir::Type::UInt(64),
            }],
            return_type: crate::ir::Type::UInt(64),
        },
        body: Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some(VarId::from("$t1"))],
                value: Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(Expr::Var(VarId::from("$t0"))),
                    rhs: Box::new(Expr::Var(VarId::from("$t0"))),
                },
            }],
            tail: BlockTail::Value(Expr::Var(VarId::from("$t1"))),
        },
        kind: FunctionKind::Source,
        effects: Effects {
            aborts: AbortBit::Partial,
            det: DetBit::Det,
            mutation: MutLevel::NoMut,
            world_writes: false,
        },
        explicit_pure: false,
    };
    add_function(&mut prog, 0, f);

    let out = crate::render::render_program(&prog).expect("render");
    // Body must reference `a`, not `t_t0`. The tail-let peephole
    // inlines the single-use let.
    assert!(out.contains("(a + a)"), "got:\n{}", out);
    let _ = U256::from(0u32);
}

#[test]
fn unit_returning_function_empty_body() {
    // fn noop(): () { () }
    let mut prog = empty_program();
    let f = func(
        "noop",
        sig(vec![], Type::Unit),
        body(vec![], crate::ir::Expr::Unit),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(out.contains("def noop : Unit :="), "got:\n{}", out);
    assert!(out.contains("()"), "got:\n{}", out);
}

#[test]
fn match_arm_renders_variant_name() {
    // enum Color { Red, Green, Blue { brightness: u64 } }
    // fn show(c: Color): u64 { match c { Red => 0, Green => 1, Blue { brightness } => brightness } }
    use crate::ir::{
        Block, BlockTail, Expr, Field, Function, FunctionKind, MatchArm, Param, Signature, Stmt,
        Struct, VarId, Variant,
    };

    let mut prog = empty_program();
    let color = Struct {
        module_id: 0,
        name: "Color".to_string(),
        qualified_name: "p::m::Color".to_string(),
        type_params: vec![],
        fields: vec![],
        variants: Some(vec![
            Variant {
                name: "Red".to_string(),
                tag: 0,
                fields: vec![],
            },
            Variant {
                name: "Green".to_string(),
                tag: 1,
                fields: vec![],
            },
            Variant {
                name: "Blue".to_string(),
                tag: 2,
                fields: vec![Field {
                    name: "brightness".to_string(),
                    field_type: Type::UInt(64),
                }],
            },
        ]),
        is_native: false,
    };
    add_struct(&mut prog, 7, color);

    let match_expr = Expr::Match {
        struct_id: 7,
        selector: Box::new(Expr::Var(VarId::from("c"))),
        cases: vec![
            MatchArm {
                variant: 0,
                bindings: vec![],
                body: Box::new(Block::just(lit_u64(0))),
            },
            MatchArm {
                variant: 1,
                bindings: vec![],
                body: Box::new(Block::just(lit_u64(1))),
            },
            MatchArm {
                variant: 2,
                bindings: vec![VarId::from("brightness")],
                body: Box::new(Block::just(Expr::Var(VarId::from("brightness")))),
            },
        ],
    };
    let f = Function {
        module: 0,
        name: "show".to_string(),
        signature: Signature {
            type_params: vec![],
            params: vec![Param {
                name: "c".to_string(),
                var: VarId::from("c"),
                ty: Type::Struct {
                    struct_id: 7,
                    type_args: vec![],
                },
            }],
            return_type: Type::UInt(64),
        },
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(match_expr),
        },
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
    };
    add_function(&mut prog, 0, f);

    let out = crate::render::render_program(&prog).expect("render");
    assert!(out.contains("| .Red =>"), "got:\n{}", out);
    assert!(out.contains("| .Green =>"), "got:\n{}", out);
    assert!(out.contains("| .Blue brightness =>"), "got:\n{}", out);
    // No legacy `.tag<N>` placeholder.
    assert!(!out.contains(".tag"), "got:\n{}", out);
    // Discard unused stmt let
    let _ = Stmt::Eval(Expr::Unit);
}

#[test]
fn stub_body_non_unit_return_renders_as_sorry() {
    // fn unlifted(): u64 { /* stub body Unit, return type u64 */ }
    // Mirrors what the driver produces for functions filtered out of
    // bytecode lifting. Render as sorry so the Lean stays well-typed.
    let mut prog = empty_program();
    let f = func(
        "unlifted",
        sig(vec![], Type::UInt(64)),
        body(vec![], crate::ir::Expr::Unit),
        0,
    );
    add_function(&mut prog, 0, f);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains(
            "def unlifted : BoundedNat (2^64) :=
  sorry"
        ),
        "got:\n{}",
        out
    );
}

#[test]
fn axiom_obligation_renders_prop_def_plus_axiom_decl() {
    // A trusted obligation (stage 12, FunctionKind::Axiom) renders in
    // the module file as the named Prop def (same as Theorem) followed
    // by the assumed `axiom <name>_holds` referencing it. No proof
    // body, no `sorry`.
    let mut prog = empty_program();
    let target = func(
        "foo",
        sig(vec![param("x", Type::Bool)], Type::Bool),
        body(vec![], var("x")),
        0,
    );
    add_function(&mut prog, 0, target);
    let mut ob = func(
        "foo_correct",
        sig(vec![param("x", Type::Bool)], Type::Bool),
        body(vec![], var("x")),
        0,
    );
    ob.kind = FunctionKind::Axiom {
        target: 0,
        source: 0,
        reason: crate::ir::TrustReason::NonProve,
    };
    add_function(&mut prog, 1, ob);

    let out = render_program(&prog).expect("render");
    assert!(
        out.contains("def foo_correct (x : Bool) : Prop :="),
        "prop def missing:\n{}",
        out
    );
    assert!(
        out.contains("axiom foo_correct_holds (x : Bool) : p.M.foo_correct x"),
        "axiom decl missing:\n{}",
        out
    );
    assert!(
        !out.contains("sorry"),
        "axiom must carry no proof body:\n{}",
        out
    );
}

#[test]
fn theorem_with_control_flow_tail_is_rejected() {
    use crate::ir::{Block, BlockTail};

    let mut prog = empty_program();
    let target = func(
        "foo",
        sig(vec![], Type::Bool),
        body(vec![], crate::ir::Expr::Const(crate::ir::Const::Bool(true))),
        0,
    );
    add_function(&mut prog, 0, target);
    let mut obligation = func(
        "foo_correct",
        sig(vec![], Type::Bool),
        Block {
            stmts: vec![],
            tail: BlockTail::Return(Box::new(crate::ir::Expr::Const(crate::ir::Const::Bool(
                true,
            )))),
        },
        0,
    );
    obligation.kind = FunctionKind::Theorem {
        target: 0,
        source: 0,
    };
    add_function(&mut prog, 1, obligation);

    let err = render_program(&prog).expect_err("malformed theorem must fail closed");
    assert_eq!(
        err,
        crate::render::RenderError::MalformedTheoremBody {
            module: "p.M".to_string(),
            function: "foo_correct".to_string(),
            tail: "return",
        }
    );
}

#[test]
fn generic_key_obligation_carries_lawful_anykey_binder() {
    // A stage-12 obligation (`FunctionKind::Theorem`) over a generic map
    // key gains the round-trip law `[LawfulAnyKey T]` right after the
    // `[ToAnyKey T] [FromAnyKey T]` pair -- the obligation's provability
    // depends on `fromAnyKey (toAnyKey k) = k`. The impl it constrains
    // keeps only the pair: its body merely COMPUTES the composite, so
    // demanding the law there would break every helper lemma about it
    // (the two data classes do not imply the law). Taint flows: the impl
    // borrows a `TypeParam(0)`-keyed map (marking param 0), and the
    // obligation inherits the impl's per-typeparam constraints via its
    // `target` (`inherit_spec_companion_typeparam_deps`).
    use crate::ir::{Block, BlockTail, Const, FunId, Param, Signature, VarId};

    let mut prog = empty_program();

    // impl `bk<K>(t: &mut _, k: K): K` -- borrows a K-keyed map.
    let impl_fn = Function {
        module: 0,
        name: "bk".to_string(),
        signature: Signature {
            type_params: vec!["K".to_string()],
            params: vec![
                Param {
                    name: "t".to_string(),
                    var: VarId::from("t"),
                    ty: Type::MutableRef {
                        inner: Box::new(Type::TypeParam(0)),
                        root: Box::new(Type::TypeParam(0)),
                    },
                },
                Param {
                    name: "k".to_string(),
                    var: VarId::from("k"),
                    ty: Type::TypeParam(0),
                },
            ],
            return_type: Type::TypeParam(0),
        },
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Borrow {
                step: crate::ir::path::PathStep::MapKey {
                    key: Box::new(var("k")),
                    key_type: Type::TypeParam(0),
                    value_type: Type::TypeParam(0),
                    df_value: None,
                },
                base: Box::new(var("t")),
            }),
        },
        kind: FunctionKind::Source,
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    };
    add_function(&mut prog, 0 as FunId, impl_fn);

    // obligation `bk_correct<K>` -- Theorem targeting the impl.
    let ob = Function {
        module: 0,
        name: "bk_correct".to_string(),
        signature: Signature {
            type_params: vec!["K".to_string()],
            params: vec![Param {
                name: "k".to_string(),
                var: VarId::from("k"),
                ty: Type::TypeParam(0),
            }],
            return_type: Type::Bool,
        },
        body: Block {
            stmts: vec![],
            tail: BlockTail::Value(Expr::Const(Const::Bool(true))),
        },
        kind: FunctionKind::Theorem {
            target: 0,
            source: 0,
        },
        effects: crate::ir::Effects::PURE,
        explicit_pure: false,
    };
    add_function(&mut prog, 1 as FunId, ob);

    let out = render_program(&prog).expect("render");

    // The obligation prop def carries the law binder after the pair.
    // (The test harness renders type params by their source name `K`;
    // production monomorphized params are `t_tv0` -- same gating.)
    assert!(
        out.contains("[ToAnyKey K] [FromAnyKey K] [LawfulAnyKey K]"),
        "obligation missing LawfulAnyKey binder:\n{out}"
    );
    // The impl def carries only the pair, never the law.
    let impl_line = out
        .lines()
        .find(|l| l.trim_start().starts_with("def bk "))
        .expect("impl def line present");
    assert!(
        impl_line.contains("[ToAnyKey K] [FromAnyKey K]") && !impl_line.contains("LawfulAnyKey"),
        "impl def should carry only the pair, not the law:\n{impl_line}"
    );
    // The generated AnyKey scaffold carries the law class unconditionally.
    assert!(
        out.contains("class LawfulAnyKey (A : Type) [ToAnyKey A] [FromAnyKey A] : Prop where"),
        "missing LawfulAnyKey class scaffold:\n{out}"
    );
}

#[test]
fn a_loop_step_inductive_derives_nonempty_but_not_inhabited() {
    // A step function that falls back to `partial def` (deepbook
    // `math::quick_sort.aborts.while_0_step`) needs its return type to be
    // `Nonempty`; the step inductive had no instance at all. `Nonempty` is a
    // Prop, so unlike `Inhabited` it compiles no code inside the
    // `noncomputable section` the step inductives live in.
    use crate::ir::{Field, Struct, Variant};

    let mut program = empty_program();
    add_struct(
        &mut program,
        0,
        Struct {
            module_id: 0,
            name: "loop_while_0_Step".to_string(),
            qualified_name: "p::m::loop_while_0_Step".to_string(),
            type_params: Vec::new(),
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "cont".to_string(),
                    tag: 0,
                    fields: vec![Field {
                        name: "i".to_string(),
                        field_type: Type::UInt(64),
                    }],
                },
                Variant {
                    name: "done".to_string(),
                    tag: 1,
                    fields: vec![Field {
                        name: "r".to_string(),
                        field_type: Type::Bool,
                    }],
                },
            ]),
            is_native: false,
        },
    );
    let output = render_program(&program).expect("render");
    let decl = output
        .split("inductive loop_while_0_Step")
        .nth(1)
        .expect("step inductive rendered");
    let decl = &decl[..decl.find("\n\n").unwrap_or(decl.len())];

    assert!(decl.contains("deriving Nonempty"), "{decl}");
    assert!(!decl.contains("Inhabited"), "{decl}");
}

#[test]
fn mutually_recursive_source_functions_render_as_partial_defs() {
    // deepbook `big_vector::{slice_remove, node_remove}` recurse into each
    // other; neither calls itself by name, so the block used to render plain
    // `def`s and Lean rejected it ("fail to show termination"). A non-trivial
    // SCC that is not `partial_fixpoint`-eligible is recursive by
    // construction: every member is `partial`.
    let mut prog = empty_program();
    let call = |fun| Expr::Call {
        fun,
        type_args: vec![],
        args: vec![var("n")],
    };
    add_function(
        &mut prog,
        0,
        func(
            "a",
            sig(vec![param("n", Type::UInt(64))], Type::UInt(64)),
            body(vec![], call(1)),
            0,
        ),
    );
    add_function(
        &mut prog,
        1,
        func(
            "b",
            sig(vec![param("n", Type::UInt(64))], Type::UInt(64)),
            body(vec![], call(0)),
            0,
        ),
    );

    let output = render_program(&prog).expect("render");

    assert!(output.contains("mutual"), "{output}");
    assert!(output.contains("partial def a "), "{output}");
    assert!(output.contains("partial def b "), "{output}");
}
