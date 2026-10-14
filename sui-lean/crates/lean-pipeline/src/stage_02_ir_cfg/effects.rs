//! Effects classification pre-pass (Pre-pass C).
//!
//! Computes [`crate::ir::Effects`] for every [`Function`] in the
//! program along four orthogonal axes:
//!
//! - [`crate::ir::AbortBit`] -- emitted as `Partial` when the body
//!   contains a `BinOp` classified by `BinOp::can_abort_on_uint`, a
//!   `UnOp::Cast(_)`, a `BlockTail::Abort`, or an `Expr::While`
//!   (potentially non-terminating).
//! - [`crate::ir::DetBit`] -- never set by the body walker; flips
//!   to `NonDet` only through the fixpoint when a `random::*`
//!   native shows up as a transitive callee.
//! - [`crate::ir::MutLevel`] -- emitted as `LocalMut` when the
//!   body contains `Expr::WriteRef` / `Expr::WriteBack` (stage-3
//!   value-form augmentation markers; never touch global state).
//!   `GlobalMut` propagates only through the fixpoint, from
//!   framework natives that touch global state
//!   (transfer::transfer, transfer::share_object, event::emit,
//!   dynamic_field::* on &mut UID).
//! - `world_writes` -- propagated from callees that may change the
//!   threaded World. Read-only World natives leave this false.
//!
//! The fixpoint walks each Call and narrows the caller's effects
//! via the pointwise [`crate::ir::Effects::meet`] lattice.
//! Recursive and mutually-recursive functions converge because the
//! lattice only narrows. Native functions retain their lift-time
//! effects (the native registry classifies framework natives
//! explicitly).

use std::collections::BTreeMap;

use crate::ir::visit::{walk_expr_default, walk_tail_default, Visitor};
use crate::ir::{BinOp, BlockTail, Expr, FunId, Program, UnOp};

pub(crate) fn collect_callees(body: &crate::ir::Block) -> Vec<FunId> {
    struct CalleeCollector(Vec<FunId>);
    impl Visitor for CalleeCollector {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, .. } = e {
                self.0.push(*fun);
            }
            walk_expr_default(self, e);
        }
    }
    let mut c = CalleeCollector(Vec::new());
    c.visit_block(body);
    c.0
}

fn is_aborting_binop(op: BinOp) -> bool {
    op.can_abort_on_uint()
}

/// Body-only [`crate::ir::Effects`] classification, ignoring
/// callees. Used by [`classify_effects`] as the initial
/// classification, and by [`super::function_lift`] to seed
/// [`crate::ir::Function::effects`] post-lift.
///
/// Emits intrinsic evidence along the abort and local-mutation axes;
/// direct World writes are represented by routed native calls or final
/// `WriteBack { world: Some(_) }` markers and are handled by the final
/// World-write closure.
///
/// - aborting fixed-width `BinOp`s, `UnOp::Cast(_)`,
///   `BlockTail::Abort`, `Expr::While` -- narrow
///   [`crate::ir::AbortBit`] to `Partial`. (Note: this folds "may
///   abort" and "may loop forever" into the same bit.)
/// - `Expr::WriteRef`, `Expr::WriteBack` -- narrow
///   [`crate::ir::MutLevel`] to `LocalMut`. These are stage-3
///   value-form augmentation markers that never touch global state;
///   stage 4 absorbs them via the `&mut` return-value rewrite.
///
/// The [`crate::ir::DetBit`] axis is never set by the body walker --
/// in today's Move there are no source-level constructs that signal
/// non-determinism. NonDet propagates exclusively through the
/// fixpoint, from `random::*` framework natives.
pub fn intrinsic_effects(func: &crate::ir::Function) -> crate::ir::Effects {
    let mut walker = EffectsWalker(crate::ir::Effects::PURE);
    walker.visit_block(&func.body);
    walker.0
}

struct EffectsWalker(crate::ir::Effects);

impl EffectsWalker {
    fn observe(&mut self, e: crate::ir::Effects) {
        self.0 = self.0.meet(e);
    }
    fn narrow_aborts(&mut self) {
        self.observe(crate::ir::Effects {
            aborts: crate::ir::AbortBit::Partial,
            det: crate::ir::DetBit::Det,
            mutation: crate::ir::MutLevel::NoMut,
            world_writes: false,
        });
    }
    fn narrow_local_mut(&mut self) {
        self.observe(crate::ir::Effects {
            aborts: crate::ir::AbortBit::Total,
            det: crate::ir::DetBit::Det,
            mutation: crate::ir::MutLevel::LocalMut,
            world_writes: false,
        });
    }
}

impl Visitor for EffectsWalker {
    fn visit_tail(&mut self, t: &BlockTail) {
        if matches!(t, BlockTail::Abort { .. }) {
            self.narrow_aborts();
        }
        walk_tail_default(self, t);
    }

    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::BinOp { op, .. } if is_aborting_binop(*op) => self.narrow_aborts(),
            Expr::UnOp {
                op: UnOp::Cast(_), ..
            }
            | Expr::While { .. } => self.narrow_aborts(),
            // Local-mutation IR markers; never touch global state.
            // Stage 3's value-form return augmentation absorbs the
            // mutation; the body walker records LocalMut so the
            // fixpoint propagates "this function takes / produces
            // a `&mut`" up the call graph without conflating it
            // with global-state mutation.
            Expr::WriteRef { .. } | Expr::WriteBack { .. } => self.narrow_local_mut(),
            _ => {}
        }
        walk_expr_default(self, e);
    }
}

/// Run the [`crate::ir::Effects`] classification fixpoint over
/// `program`. Mutates each non-native
/// [`crate::ir::Function::effects`] in place.
pub fn classify_effects(program: &mut Program) {
    use crate::ir::Effects;

    let mut effects: BTreeMap<FunId, Effects> = program
        .functions
        .iter()
        .map(|(id, f)| {
            let initial = if f.explicit_pure {
                f.effects
            } else {
                intrinsic_effects(f)
            };
            (*id, initial)
        })
        .collect();
    for (fid, decl) in &program.natives.decls {
        effects.insert(*fid, decl.effects);
    }

    loop {
        let mut changed = false;
        for (fid, func) in &program.functions {
            // `#[ext(pure)]` locks at the lift-time value (which is
            // `Effects::PURE` per the function_lift path). The
            // annotation is an explicit user assertion that must
            // win over the call-graph meet.
            if func.explicit_pure {
                continue;
            }
            let mut current = effects[fid];
            for callee in collect_callees(&func.body) {
                // Conservative fallback for unresolvable FunIds;
                // natives are pre-seeded above so they hit the
                // explicit branch with their declared Effects.
                current = current.meet(
                    effects
                        .get(&callee)
                        .copied()
                        .unwrap_or(Effects::CONSERVATIVE),
                );
            }
            if current != effects[fid] {
                effects.insert(*fid, current);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    for (fid, func) in program.functions.iter_mut() {
        func.effects = effects[fid];
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::builder::{lit_u64, var};
    use crate::ir::natives::NativeDecl;
    use crate::ir::{
        BinOp, Block, BlockTail, Expr, Function, FunctionKind, Module, Program, Signature, Stmt,
        Type,
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

    fn pure_function() -> Function {
        Function {
            module: 0,
            name: "f".to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: Vec::new(),
                return_type: Type::Unit,
            },
            body: Block {
                stmts: Vec::new(),
                tail: BlockTail::Value(Expr::Unit),
            },
            kind: FunctionKind::Source,
            effects: crate::ir::Effects::CONSERVATIVE,
            explicit_pure: false,
        }
    }

    fn make_prog(funcs: Vec<(FunId, Function)>) -> Program {
        let mut p = Program::default();
        p.modules.insert(0, empty_module());
        for (id, f) in funcs {
            p.functions.insert(id, f);
        }
        p
    }

    // ---- intrinsic_effects ------------------------------------------

    fn arith_body() -> Block {
        Block {
            stmts: vec![Stmt::Let {
                pattern: vec![Some("x".into())],
                value: Expr::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(lit_u64(1)),
                    rhs: Box::new(lit_u64(2)),
                },
            }],
            tail: BlockTail::Value(Expr::Unit),
        }
    }

    #[test]
    fn intrinsic_effects_empty_is_pure() {
        let f = pure_function();
        assert_eq!(intrinsic_effects(&f), crate::ir::Effects::PURE);
    }

    #[test]
    fn intrinsic_effects_arith_is_partial_no_mut() {
        // Aborting BinOp -> Partial; no WriteRef -> NoMut.
        let mut f = pure_function();
        f.body = arith_body();
        let e = intrinsic_effects(&f);
        assert_eq!(e.aborts, crate::ir::AbortBit::Partial);
        assert_eq!(e.det, crate::ir::DetBit::Det);
        assert_eq!(e.mutation, crate::ir::MutLevel::NoMut);
    }

    #[test]
    fn intrinsic_effects_abort_tail_is_partial() {
        let mut f = pure_function();
        f.body = Block {
            stmts: Vec::new(),
            tail: BlockTail::Abort {
                code: Box::new(lit_u64(0)),
            },
        };
        assert_eq!(intrinsic_effects(&f).aborts, crate::ir::AbortBit::Partial);
        assert_eq!(intrinsic_effects(&f).mutation, crate::ir::MutLevel::NoMut);
    }

    #[test]
    fn intrinsic_effects_write_ref_is_local_mut() {
        // WriteRef -> LocalMut, NOT GlobalMut. Body-walker never
        // emits GlobalMut directly.
        let mut f = pure_function();
        f.body = Block {
            stmts: vec![Stmt::Eval(Expr::WriteRef {
                reference: Box::new(var("p")),
                value: Box::new(lit_u64(1)),
            })],
            tail: BlockTail::Value(Expr::Unit),
        };
        let e = intrinsic_effects(&f);
        assert_eq!(e.aborts, crate::ir::AbortBit::Total);
        assert_eq!(e.mutation, crate::ir::MutLevel::LocalMut);
    }

    // ---- classify_effects ------------------------------------------

    fn impure_native(name: &str) -> NativeDecl {
        NativeDecl {
            module: 0,
            name: name.to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: Vec::new(),
                return_type: Type::Unit,
            },
            effects: crate::ir::Effects::CONSERVATIVE,
            explicit_pure: false,
            is_framework: true,
            spec_target: None,
            user_native: None,
        }
    }

    fn nondet_native(name: &str) -> NativeDecl {
        // Models `random::next_u64`: (Total, NonDet, GlobalMut).
        NativeDecl {
            module: 0,
            name: name.to_string(),
            signature: Signature {
                type_params: Vec::new(),
                params: Vec::new(),
                return_type: Type::Unit,
            },
            effects: crate::ir::Effects {
                aborts: crate::ir::AbortBit::Total,
                det: crate::ir::DetBit::NonDet,
                mutation: crate::ir::MutLevel::GlobalMut,
                world_writes: true,
            },
            explicit_pure: false,
            is_framework: true,
            spec_target: None,
            user_native: None,
        }
    }

    #[test]
    fn classify_effects_empty_is_pure() {
        let mut p = make_prog(vec![(0, pure_function())]);
        classify_effects(&mut p);
        assert_eq!(p.functions[&0].effects, crate::ir::Effects::PURE);
    }

    #[test]
    fn classify_effects_propagates_global_mut_via_callee() {
        let mut caller = pure_function();
        caller.body = Block {
            stmts: vec![Stmt::Eval(Expr::Call {
                fun: 99,
                type_args: Vec::new(),
                args: Vec::new(),
            })],
            tail: BlockTail::Value(Expr::Unit),
        };
        let mut p = make_prog(vec![(0, caller)]);
        p.natives.decls.insert(99, impure_native("n"));
        classify_effects(&mut p);
        assert_eq!(
            p.functions[&0].effects.mutation,
            crate::ir::MutLevel::GlobalMut
        );
    }

    #[test]
    fn classify_effects_propagates_nondet() {
        // A function that transitively calls a NonDet native
        // becomes NonDet itself.
        let mut caller = pure_function();
        caller.body = Block {
            stmts: vec![Stmt::Eval(Expr::Call {
                fun: 99,
                type_args: Vec::new(),
                args: Vec::new(),
            })],
            tail: BlockTail::Value(Expr::Unit),
        };
        let mut p = make_prog(vec![(0, caller)]);
        p.natives.decls.insert(99, nondet_native("random_next"));
        classify_effects(&mut p);
        assert_eq!(p.functions[&0].effects.det, crate::ir::DetBit::NonDet);
        assert_eq!(
            p.functions[&0].effects.mutation,
            crate::ir::MutLevel::GlobalMut
        );
    }

    #[test]
    fn classify_effects_ext_pure_stays_pure_even_with_impure_callee() {
        // An explicitly pure function stays at Effects::PURE even
        // though it calls an Impure native.
        let mut f = pure_function();
        f.effects = crate::ir::Effects::PURE;
        f.explicit_pure = true;
        f.body = Block {
            stmts: vec![Stmt::Eval(Expr::Call {
                fun: 99,
                type_args: Vec::new(),
                args: Vec::new(),
            })],
            tail: BlockTail::Value(Expr::Unit),
        };
        let mut p = make_prog(vec![(0, f)]);
        p.natives.decls.insert(99, impure_native("n"));
        classify_effects(&mut p);
        assert_eq!(p.functions[&0].effects, crate::ir::Effects::PURE);
    }

    #[test]
    fn classify_effects_recursive_function_converges() {
        // f calls f; arithmetic in body. Should land at
        // (Partial, Det, NoMut), not loop.
        let mut f = pure_function();
        f.body = Block {
            stmts: vec![
                Stmt::Let {
                    pattern: vec![Some("x".into())],
                    value: Expr::BinOp {
                        op: BinOp::Add,
                        lhs: Box::new(lit_u64(1)),
                        rhs: Box::new(lit_u64(2)),
                    },
                },
                Stmt::Eval(Expr::Call {
                    fun: 0, // self
                    type_args: Vec::new(),
                    args: Vec::new(),
                }),
            ],
            tail: BlockTail::Value(Expr::Unit),
        };
        let mut p = make_prog(vec![(0, f)]);
        classify_effects(&mut p);
        assert_eq!(p.functions[&0].effects.aborts, crate::ir::AbortBit::Partial);
        assert_eq!(p.functions[&0].effects.mutation, crate::ir::MutLevel::NoMut);
    }
}
