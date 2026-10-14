//! Shared helpers for stage 4 (effects).
//!
//! Mirrors `stage_03_mut_to_let::common` in shape. Core primitives:
//!
//! - [`compute_needs_world`] -- which translated functions are threaded.
//! - [`augment_return_type_with_world`] -- compute the augmented
//!   return type given the original.
//! - [`augment_value_with_world`] -- wrap a tail value expression
//!   with `Var(world)` at the end, flattening tuples.
//!
//! The threading parallel with stage 3: where stage 3 augments per
//! `&mut` parameter (one extra slot per `&mut`), stage 4 augments
//! once per function in `needs_world` (one extra slot for `World`).

use crate::ir::{Expr, Function, MutLevel, Param, StructId, Type, VarId};

/// Canonical name of the world parameter / binder introduced by
/// stage 4.
pub const WORLD_VAR: &str = "world";

/// True iff `func` directly depends on external World state and therefore
/// seeds world threading. Native bodies stay
/// hand-written, but stage 4 augments their IR declarations so every
/// signature consumer sees the same shape as the Lean prelude.
///
/// `GlobalMut` includes World readers and writers; `effects.world_writes`
/// distinguishes whether the dependency can change World.
pub fn is_impure_user(func: &Function) -> bool {
    func.effects.mutation == MutLevel::GlobalMut
}

/// Compute the augmented return type for a World-threaded function.
///
/// Same always-Tuple invariant as stage 3: the augmented type is
/// always `Type::Tuple([...])`, even when there's a single trailing
/// slot. The renderer collapses singleton tuples when emitting Lean.
///
/// Rules:
/// - `orig == Unit`: `Tuple([World])`.
/// - `orig` is a Tuple: extend with `World`.
/// - Otherwise: `Tuple([orig, World])`.
pub fn augment_return_type_with_world(orig: Type, world_ty: &Type) -> Type {
    match orig {
        Type::Unit => Type::Tuple(vec![world_ty.clone()]),
        Type::Tuple(mut items) => {
            items.push(world_ty.clone());
            Type::Tuple(items)
        }
        other => Type::Tuple(vec![other, world_ty.clone()]),
    }
}

/// Augment a tail value expression with `Var(world)` at the end.
///
/// Mirrors [`augment_return_type_with_world`]: the augmented value is
/// always `Expr::Tuple([...])`. `ret_is_unit` tells us whether the
/// original return type was Unit (in which case we drop the original
/// value and produce `Tuple([Var(world)])` directly).
pub fn augment_value_with_world(value: Expr, world_var: &VarId, ret_is_unit: bool) -> Expr {
    let world_expr = Expr::Var(world_var.clone());
    if ret_is_unit {
        return Expr::Tuple(vec![world_expr]);
    }
    match value {
        Expr::Tuple(mut items) => {
            items.push(world_expr);
            Expr::Tuple(items)
        }
        other => Expr::Tuple(vec![other, world_expr]),
    }
}

/// True iff `ty` is the World struct type. Used by idempotency
/// detection.
pub fn is_world_type(ty: &Type, world_id: StructId) -> bool {
    matches!(
        ty,
        Type::Struct { struct_id, type_args } if *struct_id == world_id && type_args.is_empty()
    )
}

pub(crate) fn direct_world_positions(ty: &Type, world_id: StructId) -> Vec<usize> {
    match ty {
        Type::Tuple(items) => items
            .iter()
            .enumerate()
            .filter_map(|(index, ty)| is_world_type(ty, world_id).then_some(index))
            .collect(),
        ty if is_world_type(ty, world_id) => vec![0],
        _ => Vec::new(),
    }
}

pub(crate) fn type_carries_world(ty: &Type, world_id: StructId) -> bool {
    !direct_world_positions(ty, world_id).is_empty()
}

pub(crate) fn lifecycle_world_position(params: &[Param], world_id: StructId) -> Option<usize> {
    let positions: Vec<_> = params
        .iter()
        .enumerate()
        .filter(|(_, param)| is_world_type(&param.ty, world_id))
        .map(|(index, _)| index)
        .collect();
    positions
        .iter()
        .copied()
        .filter_map(|index| {
            crate::ir::names::world_ssa_generation(params[index].var.as_ref())
                .map(|generation| (index, generation))
        })
        .max_by(
            |(left_index, left_generation), (right_index, right_generation)| {
                left_generation
                    .cmp(right_generation)
                    .then_with(|| params[*left_index].var.cmp(&params[*right_index].var))
            },
        )
        .map(|(index, _)| index)
        .or_else(|| positions.first().copied())
}

pub(crate) fn function_lifecycle_world_position(
    function: &Function,
    world_id: StructId,
) -> Option<usize> {
    if crate::ir::names::is_aborts_family_name(&function.name) {
        let live_accumulator = function.signature.params.iter().position(|param| {
            is_world_type(&param.ty, world_id)
                && matches!(param.var.as_ref(), "__la_world_w" | "__la_world_a")
        });
        if live_accumulator.is_some() {
            return live_accumulator;
        }
    }
    lifecycle_world_position(&function.signature.params, world_id)
}

/// Detect whether `current` is already in the augmented shape with
/// world as the last tuple slot.
///
/// Per the always-Tuple invariant, an augmented World return type
/// is **always** a Tuple whose last element is `World`. Non-Tuple
/// types are unambiguously NOT yet augmented.
pub fn return_already_world_augmented(current: &Type, world_id: StructId) -> bool {
    match current {
        Type::Tuple(items) => items
            .last()
            .map(|t| is_world_type(t, world_id))
            .unwrap_or(false),
        _ => false,
    }
}

/// Detect whether a body's tail Expr is already augmented with
/// `Var(world)` as the last tuple element.
pub fn value_already_world_augmented(value: &Expr, world_var: &VarId) -> bool {
    match value {
        Expr::Tuple(items) => match items.last() {
            Some(Expr::Var(v)) => v == world_var,
            _ => false,
        },
        _ => false,
    }
}

/// Detect whether the function's original (pre-stage-4) return type
/// was `Unit`. Used by [`augment_value_with_world`] to choose between
/// "drop original value, emit just world" and "keep original value,
/// append world".
///
/// Per the always-Tuple invariant, an augmented return type for an
/// World-threaded function with originally `Unit` return is `Tuple([World])`
/// -- a singleton tuple. For other shapes the tuple has >= 2 elements.
pub fn original_was_unit_world(augmented: &Type, world_id: StructId) -> bool {
    match augmented {
        Type::Tuple(items) if items.len() == 1 => is_world_type(&items[0], world_id),
        _ => false,
    }
}

/// World binder VarId.
pub fn world_varid() -> VarId {
    VarId::from(WORLD_VAR)
}

/// True iff calling the callee at `fid` requires the caller to
/// thread `world` into the call. Two cases produce world-augmented
/// Lean signatures the caller must match:
///
/// 1. GlobalMut native callees (`NativeDecl` with
///    `effects.mutation == GlobalMut`).
/// 2. Translated functions in `needs_world`, including explicitly-pure
///    callers with a transitive world dependency.
///
/// Transform B augments the IR signature in both cases.
pub fn is_world_callee(
    callee: crate::ir::CalleeRef<'_>,
    fid: crate::ir::FunId,
    needs_world: &std::collections::BTreeSet<crate::ir::FunId>,
) -> bool {
    match callee {
        crate::ir::CalleeRef::Native(d) => d.effects.mutation == MutLevel::GlobalMut,
        crate::ir::CalleeRef::Translated(_) => needs_world.contains(&fid),
    }
}

/// Compute the transitive closure of functions that need a `world:
/// World` parameter threaded through them. A function needs world
/// iff it directly depends on external World state or transitively calls a
/// World source (a GlobalMut native or another `needs_world` member).
/// `needs_world` is an input-dependency closure; it is deliberately distinct
/// from `effects.world_writes`, which tracks whether the World may change.
///
/// This subsumes the previous `is_impure_user` predicate: stage 4's
/// signature / call-site / body-tail augmentation passes all gate
/// on `needs_world` membership uniformly, which means a
/// `#[ext(pure)]` user helper that calls World-dependent
/// framework natives (e.g. `math_specs::math_div` calling
/// `Integer::mul`) gets a `world` parameter even though its
/// `Function::effects` is locked at [`Effects::PURE`] (the
/// `explicit_pure` annotation locks the per-function classification
/// for downstream optimization decisions, not for effect
/// threading).
pub fn compute_needs_world(
    program: &crate::ir::Program,
) -> std::collections::BTreeSet<crate::ir::FunId> {
    use crate::ir::FunId;
    use std::collections::BTreeSet;

    let mut needs_world: BTreeSet<FunId> = program
        .functions
        .iter()
        .filter(|(_, f)| f.effects.mutation == MutLevel::GlobalMut)
        .map(|(id, _)| *id)
        .collect();

    let impure_natives: BTreeSet<FunId> = program
        .natives
        .decls
        .iter()
        .filter(|(_, d)| d.effects.mutation == MutLevel::GlobalMut)
        .map(|(id, _)| *id)
        .collect();

    loop {
        let mut changed = false;
        for (fid, func) in &program.functions {
            if needs_world.contains(fid) {
                continue;
            }
            // A function needs a world if ANY callee -- including ones
            // inside a Quantifier body -- is world-threaded. A predicate
            // that reads df-backed state (e.g. `forall!(|a|
            // acl_addr_not_in_table(a, table))` over a LinkedTable) calls
            // a world-threaded helper; stage 4 threads it
            // (`thread_world_in_quantifier_body`) and the renderer emits a
            // real call, so the enclosing spec function must carry a world
            // to supply it. Pure predicates add nothing -- their callees
            // aren't world-threaded -- so logical-only lemmas (e.g.
            // ember-vaults' `lemma_account_properties_after_update_spec`)
            // are not over-threaded.
            let needs = collect_callees(&func.body)
                .iter()
                .any(|c| needs_world.contains(c) || impure_natives.contains(c));
            if needs {
                needs_world.insert(*fid);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    needs_world
}

/// Conservatively propagate the World-write bit through the final call
/// graph. This is deliberately separate from `classify_effects`: stage 7
/// creates loop and continuation helpers after normal effect
/// classification, and those helpers may now own calls that were formerly
/// in their parent. Existing write evidence and direct dynamic-field
/// writebacks are retained, writing natives seed the closure, and an
/// unresolved call is treated as writing.
pub fn propagate_world_writes(program: &mut crate::ir::Program) {
    use crate::ir::FunId;
    use std::collections::BTreeSet;

    let native_writers: BTreeSet<FunId> = program
        .natives
        .decls
        .iter()
        .filter(|(_, d)| d.effects.world_writes)
        .map(|(id, _)| *id)
        .collect();
    let known_callees: BTreeSet<FunId> = program
        .functions
        .keys()
        .chain(program.natives.decls.keys())
        .copied()
        .collect();
    let mut writers: BTreeSet<FunId> = program
        .functions
        .iter()
        .filter(|(_, function)| participates_in_world_write_closure(function))
        .filter(|(_, f)| f.effects.world_writes || block_has_world_write(&f.body))
        .map(|(id, _)| *id)
        .collect();

    loop {
        let mut changed = false;
        for (fid, func) in &program.functions {
            if writers.contains(fid) || !participates_in_world_write_closure(func) {
                continue;
            }
            let writes = collect_callees(&func.body).iter().any(|callee| {
                writers.contains(callee)
                    || native_writers.contains(callee)
                    || !known_callees.contains(callee)
            });
            if writes {
                writers.insert(*fid);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    for fid in writers {
        if let Some(func) = program.functions.get_mut(&fid) {
            func.effects.world_writes = true;
        }
    }
}

fn participates_in_world_write_closure(function: &crate::ir::Function) -> bool {
    !crate::ir::names::is_aborts_family_name(&function.name)
        && !matches!(
            function.kind,
            crate::ir::FunctionKind::Theorem { .. } | crate::ir::FunctionKind::Axiom { .. }
        )
}

fn block_has_world_write(block: &crate::ir::Block) -> bool {
    use crate::ir::visit::{walk_expr_default, Visitor};
    use crate::ir::Expr;

    struct WorldWriteFinder(bool);
    impl Visitor for WorldWriteFinder {
        fn visit_expr(&mut self, expr: &Expr) {
            if matches!(expr, Expr::WriteBack { world: Some(_), .. }) {
                self.0 = true;
            }
            walk_expr_default(self, expr);
        }
    }

    let mut finder = WorldWriteFinder(false);
    finder.visit_block(block);
    finder.0
}

/// Collect every Call FunId in `block`, including inside
/// `Expr::Quantifier` bodies (a world-threaded callee in a predicate makes
/// the enclosing function need a world -- see `compute_needs_world`).
pub(crate) fn collect_callees(block: &crate::ir::Block) -> Vec<crate::ir::FunId> {
    use crate::ir::visit::{walk_expr_default, Visitor};
    use crate::ir::Expr;

    struct CalleeCollector(Vec<crate::ir::FunId>);
    impl Visitor for CalleeCollector {
        fn visit_expr(&mut self, expr: &Expr) {
            if let Expr::Call { fun, .. } = expr {
                self.0.push(*fun);
            }
            walk_expr_default(self, expr);
        }
    }

    let mut collector = CalleeCollector(Vec::new());
    collector.visit_block(block);
    collector.0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::builder::{call, forall, just, unit, var};
    use crate::ir::natives::NativeDecl;
    use crate::ir::{
        BitOp, Block, BorrowEdge, BorrowNode, Effects, FunctionKind, Module, Program, Signature,
    };

    fn empty_module() -> Module {
        Module {
            name: String::new(),
            package_name: String::new(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: false,
        }
    }

    fn func(name: &str, effects: Effects, body: Block) -> Function {
        Function {
            module: 0,
            name: name.to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: Vec::new(),
                return_type: Type::Unit,
            },
            body,
            kind: FunctionKind::Source,
            effects,
            explicit_pure: false,
        }
    }

    fn impure_native() -> NativeDecl {
        NativeDecl {
            module: 0,
            name: "native_mut".to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: Vec::new(),
                return_type: Type::Unit,
            },
            effects: Effects {
                mutation: MutLevel::GlobalMut,
                ..Effects::PURE
            },
            explicit_pure: false,
            is_framework: false,
            spec_target: None,
            user_native: None,
        }
    }

    /// needs_world = the GlobalMut functions plus their transitive
    /// (non-native) callers -- including callers through an impure native
    /// and through a `Quantifier` body; pure leaves and the natives
    /// themselves are excluded. Recomputation is stable.
    #[test]
    fn needs_world_seeds_and_propagates() {
        let gm = Effects {
            mutation: MutLevel::GlobalMut,
            ..Effects::PURE
        };
        let mut p = Program::default();
        p.modules.insert(0, empty_module());
        p.functions.insert(1, func("f_mut", gm, just(unit())));
        p.functions
            .insert(2, func("caller", Effects::PURE, just(call(1, vec![]))));
        p.functions
            .insert(3, func("pure_leaf", Effects::PURE, just(unit())));
        p.functions.insert(
            5,
            func("native_caller", Effects::PURE, just(call(4, vec![]))),
        );
        p.functions.insert(
            6,
            func(
                "quant_caller",
                Effects::PURE,
                just(forall("x", just(call(1, vec![])))),
            ),
        );
        p.natives.decls.insert(4, impure_native());

        let nw = compute_needs_world(&p);
        assert!(nw.contains(&1), "GlobalMut function seeds needs_world");
        assert!(
            nw.contains(&2),
            "transitive caller of a mutator needs world"
        );
        assert!(nw.contains(&5), "caller of an impure native needs world");
        assert!(
            nw.contains(&6),
            "caller inside a Quantifier body needs world"
        );
        assert!(!nw.contains(&3), "a pure leaf does not need world");
        assert!(!nw.contains(&4), "natives are not needs_world members");
        assert_eq!(compute_needs_world(&p), nw, "recomputation is stable");
    }

    #[test]
    fn world_writes_propagate_conservatively_through_final_graph() {
        let mut p = Program::default();
        p.modules.insert(0, empty_module());
        p.natives.decls.insert(10, impure_native());
        let mut writer = impure_native();
        writer.name = "native_writer".to_string();
        writer.effects.world_writes = true;
        p.natives.decls.insert(11, writer);

        p.functions
            .insert(1, func("read_only", Effects::WORLD, just(call(10, vec![]))));
        p.functions
            .insert(2, func("writes", Effects::WORLD, just(call(11, vec![]))));
        p.functions
            .insert(3, func("transitive", Effects::WORLD, just(call(2, vec![]))));
        p.functions
            .insert(4, func("unknown", Effects::WORLD, just(call(999, vec![]))));
        p.functions.insert(
            5,
            func(
                "direct_writeback",
                Effects::WORLD,
                just(Expr::WriteBack {
                    node: BorrowNode::LocalRoot("parent".into()),
                    edge: BorrowEdge::Direct,
                    child: "child".into(),
                    world: Some("world".into()),
                }),
            ),
        );
        let bit_ops = [
            Expr::BitOp(BitOp::Extract {
                high: 7,
                low: 0,
                operand: Box::new(call(11, vec![])),
            }),
            Expr::BitOp(BitOp::ZeroExtend {
                bits: 8,
                operand: Box::new(call(11, vec![])),
            }),
            Expr::BitOp(BitOp::SignExtend {
                bits: 8,
                operand: Box::new(call(11, vec![])),
            }),
            Expr::BitOp(BitOp::Concat {
                high: Box::new(call(11, vec![])),
                low: Box::new(unit()),
            }),
        ];
        for (index, expr) in bit_ops.into_iter().enumerate() {
            let fid = 6 + index;
            p.functions
                .insert(fid, func("bitop_writer", Effects::WORLD, just(expr)));
        }
        let mut theorem = func("theorem", Effects::PURE, just(call(11, vec![])));
        theorem.kind = FunctionKind::Theorem {
            target: 2,
            source: 2,
        };
        p.functions.insert(12, theorem);
        let mut axiom = func("axiom", Effects::PURE, just(call(11, vec![])));
        axiom.kind = FunctionKind::Axiom {
            target: 2,
            source: 2,
            reason: crate::ir::TrustReason::NonProve,
        };
        p.functions.insert(13, axiom);
        let mut abort_cont = func(
            "source.aborts.cont_0",
            Effects::PURE,
            just(call(11, vec![])),
        );
        abort_cont.kind = FunctionKind::Synthetic;
        p.functions.insert(14, abort_cont);
        let mut ordinary_cont = func("source.cont_0", Effects::PURE, just(call(11, vec![])));
        ordinary_cont.kind = FunctionKind::Synthetic;
        p.functions.insert(15, ordinary_cont);

        propagate_world_writes(&mut p);
        assert!(!p.functions[&1].effects.world_writes);
        for fid in [2, 3, 4, 5, 6, 7, 8, 9] {
            assert!(
                p.functions[&fid].effects.world_writes,
                "function {fid} must be conservatively classified as writing"
            );
        }
        assert!(!p.functions[&12].effects.world_writes);
        assert!(!p.functions[&13].effects.world_writes);
        assert!(
            !p.functions[&14].effects.world_writes,
            "logical abort-family helpers do not expose a changed World"
        );
        assert!(
            p.functions[&15].effects.world_writes,
            "ordinary continuations remain in the executable write closure"
        );
        let once = p.clone();
        propagate_world_writes(&mut p);
        assert_eq!(p, once, "World-write propagation is idempotent");
    }

    /// Stage 4's return-type augmentation is always a Tuple ending in
    /// World; its idempotency detectors recognise exactly that shape (so
    /// the pass never double-augments).
    #[test]
    fn world_augmentation_shape_and_idempotency() {
        let world_id: StructId = 99;
        let wt = Type::Struct {
            struct_id: world_id,
            type_args: Vec::new(),
        };

        assert_eq!(
            augment_return_type_with_world(Type::Unit, &wt),
            Type::Tuple(vec![wt.clone()])
        );
        assert_eq!(
            augment_return_type_with_world(Type::Bool, &wt),
            Type::Tuple(vec![Type::Bool, wt.clone()])
        );
        assert_eq!(
            augment_return_type_with_world(Type::Tuple(vec![Type::Bool]), &wt),
            Type::Tuple(vec![Type::Bool, wt.clone()])
        );

        let two = augment_return_type_with_world(Type::Bool, &wt);
        assert!(return_already_world_augmented(&two, world_id));
        assert!(!return_already_world_augmented(&Type::Bool, world_id));
        assert!(!return_already_world_augmented(
            &Type::Tuple(vec![Type::Bool, Type::Bool]),
            world_id
        ));

        let unit_aug = augment_return_type_with_world(Type::Unit, &wt);
        assert!(original_was_unit_world(&unit_aug, world_id));
        assert!(!original_was_unit_world(&two, world_id));

        let world = world_varid();
        let from_unit = augment_value_with_world(Expr::Unit, &world, true);
        assert_eq!(from_unit, Expr::Tuple(vec![Expr::Var(world.clone())]));
        assert!(value_already_world_augmented(&from_unit, &world));
        let from_val = augment_value_with_world(var("x"), &world, false);
        assert_eq!(
            from_val,
            Expr::Tuple(vec![var("x"), Expr::Var(world.clone())])
        );
        assert!(value_already_world_augmented(&from_val, &world));
    }
}
