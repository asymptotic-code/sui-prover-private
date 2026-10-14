//! Per-stage Invariant umbrellas.
//!
//! Each pipeline stage's existing `postcondition::check` becomes one
//! [`Invariant`] impl with `established_by = SNN_*, held_through =
//! Render`. The framework then automatically re-checks each stage's
//! invariants at every later stage that's supposed to preserve them.
//!
//! ## Side-channel data
//!
//! Some stage postconditions take extra args (stage 4 wants
//! `world_id`, stage 7 wants `&ProverFnIds`). The invariant wrapper
//! discovers those from the program structure by convention:
//!
//! - World: `program.structs` entry whose `qualified_name` is
//!   [`crate::stage_04_effects::WORLD_QUALIFIED_NAME`].
//! - Prover ids: `program.natives.decls` entries in the
//!   `Prover/prover` module named `requires`/`ensures`/`asserts`.
//!
//! When the side-channel data isn't discoverable (e.g. stage 4
//! hasn't run yet so the World struct is absent), the invariant
//! returns `Ok(())` rather than spuriously failing -- the precondition
//! check at the next stage catches the real problem.

use crate::ir::{builder::ProverFnIds, Program, StructId};

use super::traits::{Invariant, InvariantViolation, Stage};

// ---------------------------------------------------------------------
// Discovery helpers
// ---------------------------------------------------------------------

fn find_world_struct_id(program: &Program) -> Option<StructId> {
    program.struct_id_by_qualified_name(crate::stage_04_effects::WORLD_QUALIFIED_NAME)
}

fn discover_prover_ids(program: &Program) -> ProverFnIds {
    let mut out = ProverFnIds::default();
    // Find the Prover/prover module first.
    let prover_module = program.module_id_by_name("Prover", "prover");
    let Some(prover_mod) = prover_module else {
        return out;
    };
    for (fid, decl) in &program.natives.decls {
        if decl.module != prover_mod {
            continue;
        }
        match decl.name.as_str() {
            "requires" => out.requires = Some(*fid),
            "ensures" => out.ensures = Some(*fid),
            "asserts" => out.asserts = Some(*fid),
            _ => {}
        }
    }
    out
}

// ---------------------------------------------------------------------
// Stage 02: MapKey edge types must not be Unit/Unit (placeholder leak).
// ---------------------------------------------------------------------

/// Every `BorrowEdge::MapKey { key_type, value_type }` in the IR has
/// non-`Type::Unit` slots for both key and value.
///
/// Stage 2's `lift_borrow_edge` emits `MapKey { Unit, Unit }` for
/// upstream `Index(Table | Custom)` cases, relying on
/// `fill_map_key_types` to patch the slot from `ctx.borrow_mut_kv`
/// before the function body lands in the IR. When the surrounding
/// `Operation::Function` callsite isn't on the recognised-natives
/// allowlist (e.g. `wit_table::borrow_mut` in scallop), no patch
/// happens and the placeholder reaches downstream stages. The
/// renderer then emits broken Lean with `AnyKey.k_unit` constructors
/// that don't carry real key data.
///
/// This invariant fires immediately at stage 2's postcondition with
/// the offending function's name. Catches the bug class described in
/// `plans/lean-pipeline/native-field-collapse-loses-map-key.md`.
pub struct MapKeyTypesNotUnit;

impl Invariant for MapKeyTypesNotUnit {
    fn id(&self) -> &'static str {
        "map-key-types-not-unit"
    }

    fn established_by(&self) -> Stage {
        Stage::S02IrCfg
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        use crate::ir::visit::{walk_expr_default, Visitor};
        use crate::ir::{BorrowEdge, Expr, Type};

        struct W<'a> {
            current_fn: Option<crate::ir::FunId>,
            violations: Vec<InvariantViolation>,
            _p: std::marker::PhantomData<&'a ()>,
        }

        impl<'a> W<'a> {
            fn check_edge(&mut self, edge: &BorrowEdge, ctx: &str) {
                match edge {
                    BorrowEdge::MapKey {
                        key_type,
                        value_type,
                    } => {
                        let key_unit = matches!(key_type, Type::Unit);
                        let val_unit = matches!(value_type, Type::Unit);
                        if key_unit || val_unit {
                            self.violations.push(InvariantViolation::new(
                                "map-key-types-not-unit",
                                self.current_fn,
                                format!(
                                    "{}: MapKey edge has placeholder Unit types (key_unit={}, value_unit={}). \
                                     `lift_borrow_edge` emitted a placeholder that `fill_map_key_types` failed to patch -- \
                                     the surrounding borrow_mut callsite is likely a user-defined wrapper container \
                                     not on the recognised-natives allowlist.",
                                    ctx, key_unit, val_unit,
                                ),
                            ));
                        }
                    }
                    BorrowEdge::Hyper(inner) => {
                        for e in inner {
                            self.check_edge(e, ctx);
                        }
                    }
                    _ => {}
                }
            }
        }

        impl<'a> Visitor for W<'a> {
            fn visit_expr(&mut self, e: &Expr) {
                if let Expr::WriteBack { edge, .. } | Expr::IsParent { edge, .. } = e {
                    self.check_edge(edge, "WriteBack/IsParent");
                }
                walk_expr_default(self, e);
            }
        }

        let mut w = W {
            current_fn: None,
            violations: Vec::new(),
            _p: std::marker::PhantomData,
        };
        for (fid, func) in &program.functions {
            w.current_fn = Some(*fid);
            w.visit_block(&func.body);
        }
        if w.violations.is_empty() {
            Ok(())
        } else {
            Err(w.violations)
        }
    }
}

static MAP_KEY_TYPES_NOT_UNIT: MapKeyTypesNotUnit = MapKeyTypesNotUnit;

// ---------------------------------------------------------------------
// Stage 03 (mut_to_let): pure check.
// ---------------------------------------------------------------------

pub struct Stage03MutToLetPostcondition;

impl Invariant for Stage03MutToLetPostcondition {
    fn id(&self) -> &'static str {
        "stage-03-mut-to-let-postcondition"
    }
    fn established_by(&self) -> Stage {
        Stage::S03MutToLet
    }
    fn held_through(&self) -> Stage {
        Stage::Render
    }
    fn check(&self, p: &Program) -> Result<(), Vec<InvariantViolation>> {
        crate::stage_03_mut_to_let::postcondition::check(p).map_err(|e| {
            vec![InvariantViolation::new(
                "stage-03-mut-to-let-postcondition",
                None,
                format!("{:?}", e),
            )]
        })
    }
}

static STAGE_03_MUT_TO_LET: Stage03MutToLetPostcondition = Stage03MutToLetPostcondition;

// ---------------------------------------------------------------------
// Stage 04 (effects): needs world_id; discover from program.structs.
// ---------------------------------------------------------------------

pub struct Stage04EffectsPostcondition;

impl Invariant for Stage04EffectsPostcondition {
    fn id(&self) -> &'static str {
        "stage-04-effects-postcondition"
    }
    fn established_by(&self) -> Stage {
        Stage::S04Effects
    }
    fn held_through(&self) -> Stage {
        Stage::Render
    }
    fn check(&self, p: &Program) -> Result<(), Vec<InvariantViolation>> {
        // World struct must exist after stage 4 has run. If it
        // doesn't, the check is vacuously satisfied -- the missing
        // struct is itself a stage-4 violation that the local
        // postcondition would catch, but only if the local
        // postcondition was invoked with a valid world_id. Here we
        // can only check what's reachable.
        let Some(world_id) = find_world_struct_id(p) else {
            return Ok(());
        };
        crate::stage_04_effects::postcondition::check(p, world_id).map_err(|e| {
            use crate::stage_04_effects::postcondition::PostconditionError;
            let function = match &e {
                PostconditionError::MalformedSignature { function }
                | PostconditionError::MalformedWorldWriteBack { function }
                | PostconditionError::StaleWorldToken { function }
                | PostconditionError::LingeringUnthreadedCall { function, .. }
                | PostconditionError::ReturnMissingWorld { function }
                | PostconditionError::WorldOnPureFunction { function }
                | PostconditionError::MutCallInQuantifier { function, .. } => Some(*function),
                PostconditionError::MalformedNativeSignature { native } => Some(*native),
            };
            vec![InvariantViolation::new(
                "stage-04-effects-postcondition",
                function,
                format!("{:?}", e),
            )]
        })
    }
}

static STAGE_04_EFFECTS: Stage04EffectsPostcondition = Stage04EffectsPostcondition;

// ---------------------------------------------------------------------
// Stage 05 (SSA): pure check.
// ---------------------------------------------------------------------

pub struct Stage05SsaPostcondition;

impl Invariant for Stage05SsaPostcondition {
    fn id(&self) -> &'static str {
        "stage-05-ssa-postcondition"
    }
    fn established_by(&self) -> Stage {
        Stage::S05Ssa
    }
    fn held_through(&self) -> Stage {
        // SSA's `JumpArityMismatch` / `BodyTailArityMismatch` only
        // apply while While / Break / Continue still exist. After
        // stage 7 they're gone -- the check is vacuously true. The
        // no-shadowing invariant is the only piece that survives to
        // Render, but a split would require two invariants. For now
        // hold the whole umbrella through Render; the vacuous
        // branches are cheap.
        Stage::Render
    }
    fn check(&self, p: &Program) -> Result<(), Vec<InvariantViolation>> {
        crate::stage_05_ssa::postcondition::check(p).map_err(|e| {
            vec![InvariantViolation::new(
                "stage-05-ssa-postcondition",
                None,
                format!("{:?}", e),
            )]
        })
    }
}

static STAGE_05_SSA: Stage05SsaPostcondition = Stage05SsaPostcondition;

// ---------------------------------------------------------------------
// Stage 06 (let-inline + DCE): pure check.
// ---------------------------------------------------------------------

pub struct Stage06LetInlinePostcondition;

impl Invariant for Stage06LetInlinePostcondition {
    fn id(&self) -> &'static str {
        "stage-06-let-inline-postcondition"
    }
    fn established_by(&self) -> Stage {
        Stage::S06LetInline
    }
    fn held_through(&self) -> Stage {
        Stage::Render
    }
    fn check(&self, p: &Program) -> Result<(), Vec<InvariantViolation>> {
        crate::stage_06_let_inline::postcondition::check(p).map_err(|e| {
            vec![InvariantViolation::new(
                "stage-06-let-inline-postcondition",
                None,
                format!("{:?}", e),
            )]
        })
    }
}

static STAGE_06_LET_INLINE: Stage06LetInlinePostcondition = Stage06LetInlinePostcondition;

// ---------------------------------------------------------------------
// Stage 07 (rewrite): the `.aborts`-variant + unified control-flow
// extraction postcondition. Needs prover_ids; discover from
// program.natives. (Struct/id keep the historical `dejumps` name for
// stable invariant ids; the legacy dejumps path was retired.)
// ---------------------------------------------------------------------

pub struct Stage07DejumpsPostcondition;

impl Invariant for Stage07DejumpsPostcondition {
    fn id(&self) -> &'static str {
        "stage-07-dejumps-postcondition"
    }
    fn established_by(&self) -> Stage {
        Stage::S07Dejumps
    }
    fn held_through(&self) -> Stage {
        Stage::Render
    }
    fn check(&self, p: &Program) -> Result<(), Vec<InvariantViolation>> {
        let prover_ids = discover_prover_ids(p);
        crate::stage_07_dejumps::postcondition::check(p, &prover_ids).map_err(|e| {
            vec![InvariantViolation::new(
                "stage-07-dejumps-postcondition",
                None,
                format!("{:?}", e),
            )]
        })
    }
}

static STAGE_07_DEJUMPS: Stage07DejumpsPostcondition = Stage07DejumpsPostcondition;

// ---------------------------------------------------------------------
// Stage 08: final World-write closure.
// ---------------------------------------------------------------------

pub struct Stage08WorldWritesClosed;

impl Invariant for Stage08WorldWritesClosed {
    fn id(&self) -> &'static str {
        "stage-08-world-writes-closed"
    }
    fn established_by(&self) -> Stage {
        Stage::S08Loops
    }
    fn held_through(&self) -> Stage {
        Stage::Render
    }
    fn check(&self, p: &Program) -> Result<(), Vec<InvariantViolation>> {
        crate::stage_08_loops::world_writes_postcondition::check(p).map_err(|errors| {
            errors
                .into_iter()
                .map(|error| {
                    InvariantViolation::new(
                        "stage-08-world-writes-closed",
                        Some(error.function),
                        "function can transitively write World but effects.world_writes is false",
                    )
                })
                .collect()
        })
    }
}

static STAGE_08_WORLD_WRITES_CLOSED: Stage08WorldWritesClosed = Stage08WorldWritesClosed;

// ---------------------------------------------------------------------
// Stage 10 (bounded-nat): pure check.
// ---------------------------------------------------------------------

pub struct Stage10BoundedNatPostcondition;

impl Invariant for Stage10BoundedNatPostcondition {
    fn id(&self) -> &'static str {
        "stage-10-bounded-nat-postcondition"
    }
    fn established_by(&self) -> Stage {
        Stage::S10BoundedNat
    }
    fn held_through(&self) -> Stage {
        Stage::Render
    }
    fn check(&self, p: &Program) -> Result<(), Vec<InvariantViolation>> {
        crate::stage_10_bounded_nat::postcondition::check(p).map_err(|e| {
            vec![InvariantViolation::new(
                "stage-10-bounded-nat-postcondition",
                None,
                format!("{:?}", e),
            )]
        })
    }
}

static STAGE_10_BOUNDED_NAT: Stage10BoundedNatPostcondition = Stage10BoundedNatPostcondition;

// =====================================================================
// Tier 4: per-stage tightening
// =====================================================================

// ---------------------------------------------------------------------
// Stage05IterLocalsEmptyPreSsa (Tier 4)
// ---------------------------------------------------------------------

/// Before stage 5 runs, every `Expr::While::iter_locals` is empty.
/// Stage 5 populates iter_locals; if anything pre-stage-5 has a
/// non-empty iter_locals, that's a producer bug.
///
/// Lifespan: `Baseline .. S04Effects` (the last stage before S5Ssa).
/// At S5Ssa and later the invariant is vacuously inapplicable
/// because stage 5 has run.
pub struct Stage05IterLocalsEmptyPreSsa;

impl Invariant for Stage05IterLocalsEmptyPreSsa {
    fn id(&self) -> &'static str {
        "stage-05-iter-locals-empty-pre-ssa"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::S04Effects
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        use crate::ir::visit::{walk_expr_default, Visitor};
        use crate::ir::Expr;

        struct W<'a> {
            current_fn: Option<crate::ir::FunId>,
            violations: Vec<InvariantViolation>,
            _p: std::marker::PhantomData<&'a ()>,
        }

        impl<'a> Visitor for W<'a> {
            fn visit_expr(&mut self, e: &Expr) {
                if let Expr::While { iter_locals, .. } = e {
                    if !iter_locals.is_empty() {
                        self.violations.push(InvariantViolation::new(
                            "stage-05-iter-locals-empty-pre-ssa",
                            self.current_fn,
                            format!(
                                "While has {} iter_locals before stage 5 ran",
                                iter_locals.len(),
                            ),
                        ));
                    }
                }
                walk_expr_default(self, e);
            }
        }

        let mut w = W {
            current_fn: None,
            violations: Vec::new(),
            _p: std::marker::PhantomData,
        };
        for (fid, func) in &program.functions {
            w.current_fn = Some(*fid);
            w.visit_block(&func.body);
        }
        if w.violations.is_empty() {
            Ok(())
        } else {
            Err(w.violations)
        }
    }
}

static STAGE_05_ITER_LOCALS_EMPTY_PRE_SSA: Stage05IterLocalsEmptyPreSsa =
    Stage05IterLocalsEmptyPreSsa;

// ---------------------------------------------------------------------
// Stage05ReadRefInnerIsReference (Tier 4)
// ---------------------------------------------------------------------

/// After stage 5, every `Expr::ReadRef(inner)` has an `inner` that
/// types to a `Reference` / `MutableRef`. A `ReadRef` over a value
/// type is malformed IR that panics stage 7's `type_of`-based scope
/// build (`ReadRef of non-reference type ...`).
///
/// Deliberately a stage-5-ONLY invariant (`established_by =
/// held_through = S05Ssa`): later stages transform the IR, and a
/// `type_of` re-evaluation at render on the transformed shape could
/// false-fire (the stage-N-postcondition-on-transformed-IR trap
/// documented in the lean-pipeline-dev skill). It is NOT re-run at
/// the render gate. The live check runs in `stage_05_ssa::run`'s
/// debug self-check; this registration makes it greppable and
/// unit-testable through the framework.
pub struct Stage05ReadRefInnerIsReference;

impl Invariant for Stage05ReadRefInnerIsReference {
    fn id(&self) -> &'static str {
        "stage-05-readref-inner-is-reference"
    }

    fn established_by(&self) -> Stage {
        Stage::S05Ssa
    }

    fn held_through(&self) -> Stage {
        Stage::S05Ssa
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let violations: Vec<InvariantViolation> =
            crate::stage_05_ssa::postcondition::readref_over_value_findings(program)
                .into_iter()
                .map(|(fid, detail)| {
                    InvariantViolation::new(
                        "stage-05-readref-inner-is-reference",
                        Some(fid),
                        detail,
                    )
                })
                .collect();
        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }
}

static STAGE_05_READREF_INNER_IS_REFERENCE: Stage05ReadRefInnerIsReference =
    Stage05ReadRefInnerIsReference;

// ---------------------------------------------------------------------
// Stage07SourceFnHasAbortsCompanion (Tier 4)
// ---------------------------------------------------------------------

/// After stage 7, every `FunctionKind::Source` non-native function
/// has at least one corresponding
/// `FunctionKind::Spec { kind: Aborts, target: source_fid }`
/// companion registered in `program.functions`.
///
/// Stage 7 emits one `.aborts` companion per source function; a
/// missing companion means stage 7's spec_extract pass dropped a
/// source function on the floor (or never ran on it). The renderer
/// would then have no abort predicate to call from compositional
/// `.aborts` callsites.
pub struct Stage07SourceFnHasAbortsCompanion;

impl Invariant for Stage07SourceFnHasAbortsCompanion {
    fn id(&self) -> &'static str {
        "stage-07-source-fn-has-aborts-companion"
    }

    fn established_by(&self) -> Stage {
        Stage::S07Dejumps
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        use crate::ir::function::{FunctionKind, SpecKind};
        use std::collections::BTreeSet;

        // Collect every Source FunId that should have an Aborts
        // companion: all FunctionKind::Source non-native entries.
        let mut sources: BTreeSet<crate::ir::FunId> = BTreeSet::new();
        let mut have_companion: BTreeSet<crate::ir::FunId> = BTreeSet::new();
        for (fid, func) in &program.functions {
            match &func.kind {
                FunctionKind::Source => {
                    sources.insert(*fid);
                }
                FunctionKind::Spec {
                    kind: SpecKind::Aborts,
                    target,
                } => {
                    have_companion.insert(*target);
                }
                _ => {}
            }
        }
        // Also consider native-side aborts (stage 10 synth natives
        // can register aborts companions via NativeDecl::spec_target).
        for decl in program.natives.decls.values() {
            if let Some(target) = decl.spec_target {
                have_companion.insert(target);
            }
        }
        let mut violations = Vec::new();
        for source_fid in &sources {
            if !have_companion.contains(source_fid) {
                violations.push(InvariantViolation::new(
                    "stage-07-source-fn-has-aborts-companion",
                    Some(*source_fid),
                    format!("Source FunId {} has no Aborts companion", source_fid),
                ));
            }
        }
        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }
}

static STAGE_07_SOURCE_FN_HAS_ABORTS_COMPANION: Stage07SourceFnHasAbortsCompanion =
    Stage07SourceFnHasAbortsCompanion;

// ---------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------

pub(crate) static INVARIANTS: &[&'static dyn Invariant] = &[
    &MAP_KEY_TYPES_NOT_UNIT,
    &STAGE_03_MUT_TO_LET,
    &STAGE_04_EFFECTS,
    &STAGE_05_SSA,
    &STAGE_06_LET_INLINE,
    &STAGE_07_DEJUMPS,
    &STAGE_08_WORLD_WRITES_CLOSED,
    &STAGE_10_BOUNDED_NAT,
    // Tier 4: per-stage tightening
    &STAGE_05_ITER_LOCALS_EMPTY_PRE_SSA,
    &STAGE_05_READREF_INNER_IS_REFERENCE,
    &STAGE_07_SOURCE_FN_HAS_ABORTS_COMPANION,
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::invariants::registry::verify_at;

    #[test]
    fn empty_program_passes_verify_at_render() {
        let p = Program::default();
        assert!(verify_at(Stage::Render, &p).is_ok());
    }

    #[test]
    fn discover_prover_ids_returns_default_when_module_absent() {
        let p = Program::default();
        let ids = discover_prover_ids(&p);
        assert_eq!(ids.requires, None);
        assert_eq!(ids.ensures, None);
        assert_eq!(ids.asserts, None);
    }

    #[test]
    fn find_world_struct_returns_none_when_absent() {
        let p = Program::default();
        assert!(find_world_struct_id(&p).is_none());
    }

    #[test]
    fn stage_03_invariant_passes_on_empty_program() {
        let p = Program::default();
        assert!(STAGE_03_MUT_TO_LET.check(&p).is_ok());
    }

    #[test]
    fn stage_04_invariant_is_vacuous_when_world_absent() {
        // Empty program has no World struct -> invariant returns Ok
        // because there's nothing to check yet (stage 4 hasn't run).
        let p = Program::default();
        assert!(STAGE_04_EFFECTS.check(&p).is_ok());
    }

    #[test]
    fn stage_07_invariant_passes_on_empty_program() {
        let p = Program::default();
        assert!(STAGE_07_DEJUMPS.check(&p).is_ok());
    }

    #[test]
    fn stage_08_world_writes_invariant_passes_on_empty_program() {
        let p = Program::default();
        assert!(STAGE_08_WORLD_WRITES_CLOSED.check(&p).is_ok());
    }

    // -----------------------------------------------------------------
    // Tier 1: MapKeyTypesNotUnit
    // -----------------------------------------------------------------

    use crate::ir::{
        builder::*, BorrowEdge, BorrowNode, Expr, Function, FunctionKind, Module, Param, Signature,
        Stmt, Type,
    };

    fn module_program() -> Program {
        let mut p = Program::default();
        p.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "test".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        p
    }

    fn add_fn_with_body(p: &mut Program, body: crate::ir::Block) -> crate::ir::FunId {
        let id = p.functions.len();
        p.functions.insert(
            id,
            Function {
                module: 0,
                name: format!("f{id}"),
                signature: Signature {
                    type_params: Vec::new(),
                    params: vec![Param {
                        name: "self".to_string(),
                        var: "self".into(),
                        ty: Type::UInt(64),
                    }],
                    return_type: Type::Unit,
                },
                body,
                kind: FunctionKind::Source,
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
            },
        );
        id
    }

    #[test]
    fn map_key_types_not_unit_passes_on_concrete_types() {
        let mut p = module_program();
        // WriteBack with MapKey { key_type: u64, value_type: u64 } -- valid.
        let mut body = just(unit());
        body.stmts.push(Stmt::Let {
            pattern: vec![Some("child".into())],
            value: lit_u64(0),
        });
        body.stmts.push(Stmt::Eval(Expr::WriteBack {
            node: BorrowNode::LocalRoot("self".into()),
            edge: BorrowEdge::MapKey {
                key_type: Type::UInt(64),
                value_type: Type::UInt(64),
            },
            child: "child".into(),
            world: None,
        }));
        add_fn_with_body(&mut p, body);
        assert!(MAP_KEY_TYPES_NOT_UNIT.check(&p).is_ok());
    }

    #[test]
    fn map_key_types_not_unit_catches_placeholder_unit_unit() {
        let mut p = module_program();
        // WriteBack with MapKey { Unit, Unit } -- placeholder leak.
        let mut body = just(unit());
        body.stmts.push(Stmt::Let {
            pattern: vec![Some("child".into())],
            value: lit_u64(0),
        });
        body.stmts.push(Stmt::Eval(Expr::WriteBack {
            node: BorrowNode::LocalRoot("self".into()),
            edge: BorrowEdge::MapKey {
                key_type: Type::Unit,
                value_type: Type::Unit,
            },
            child: "child".into(),
            world: None,
        }));
        add_fn_with_body(&mut p, body);
        let errs = MAP_KEY_TYPES_NOT_UNIT.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert_eq!(errs[0].invariant, "map-key-types-not-unit");
        assert!(errs[0].detail.contains("placeholder Unit types"));
    }

    #[test]
    fn map_key_types_not_unit_catches_unit_inside_hyper() {
        let mut p = module_program();
        // WriteBack with Hyper containing a Unit/Unit MapKey -- still caught.
        let mut body = just(unit());
        body.stmts.push(Stmt::Let {
            pattern: vec![Some("child".into())],
            value: lit_u64(0),
        });
        body.stmts.push(Stmt::Eval(Expr::WriteBack {
            node: BorrowNode::LocalRoot("self".into()),
            edge: BorrowEdge::Hyper(vec![
                BorrowEdge::StructField {
                    struct_id: 0,
                    field_index: 0,
                },
                BorrowEdge::MapKey {
                    key_type: Type::Unit,
                    value_type: Type::UInt(64),
                },
            ]),
            child: "child".into(),
            world: None,
        }));
        add_fn_with_body(&mut p, body);
        let errs = MAP_KEY_TYPES_NOT_UNIT.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("key_unit=true"));
    }

    // -----------------------------------------------------------------
    // Tier 4: Stage05IterLocalsEmptyPreSsa
    // -----------------------------------------------------------------

    #[test]
    fn stage_05_iter_locals_empty_pre_ssa_passes_on_empty() {
        let p = Program::default();
        assert!(STAGE_05_ITER_LOCALS_EMPTY_PRE_SSA.check(&p).is_ok());
    }

    #[test]
    fn stage_05_iter_locals_empty_pre_ssa_catches_non_empty() {
        let mut p = module_program();
        let mut body = just(unit());
        body.stmts.push(Stmt::Eval(Expr::While {
            header: Box::new(just(unit())),
            cond: Box::new(lit_bool(true)),
            body: Box::new(crate::ir::Block {
                stmts: Vec::new(),
                tail: crate::ir::BlockTail::Continue {
                    level: 0,
                    value: Box::new(unit()),
                },
            }),
            iter_locals: vec![("x".into(), lit_u64(0))],
            header_exit_locals: vec!["x".into()],
            live_out: vec![],
        }));
        add_fn_with_body(&mut p, body);
        let errs = STAGE_05_ITER_LOCALS_EMPTY_PRE_SSA.check(&p).unwrap_err();
        assert!(errs[0].detail.contains("1 iter_locals"));
    }

    // -----------------------------------------------------------------
    // Tier 4: Stage07SourceFnHasAbortsCompanion
    // -----------------------------------------------------------------

    #[test]
    fn stage_07_source_fn_has_aborts_companion_passes_on_empty() {
        let p = Program::default();
        assert!(STAGE_07_SOURCE_FN_HAS_ABORTS_COMPANION.check(&p).is_ok());
    }

    #[test]
    fn stage_07_source_fn_has_aborts_companion_passes_when_companion_present() {
        let mut p = module_program();
        // Source fid 0
        add_fn_with_body(&mut p, just(unit()));
        // Aborts companion for fid 0 (will be fid 1)
        let fid = p.functions.len();
        p.functions.insert(
            fid,
            Function {
                module: 0,
                name: "f.aborts".to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: Type::Bool,
                },
                body: just(lit_bool(false)),
                kind: FunctionKind::Spec {
                    kind: crate::ir::SpecKind::Aborts,
                    target: 0,
                },
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
            },
        );
        assert!(STAGE_07_SOURCE_FN_HAS_ABORTS_COMPANION.check(&p).is_ok());
    }

    #[test]
    fn stage_07_source_fn_has_aborts_companion_catches_missing() {
        let mut p = module_program();
        // Source fid 0 -- no Aborts companion registered.
        add_fn_with_body(&mut p, just(unit()));
        let errs = STAGE_07_SOURCE_FN_HAS_ABORTS_COMPANION
            .check(&p)
            .unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("no Aborts companion"));
    }
}

// =====================================================================
// Tier 5: program-counts helper (test-only utility)
// =====================================================================

/// Counts of every notable program-level entity. Useful for fixture
/// assertions (`assert_eq!(counts(&p).functions, expected)`) and for
/// printing in diagnostic output when an invariant fires.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProgramCounts {
    pub modules: usize,
    pub structs: usize,
    pub functions: usize,
    pub natives: usize,
    pub loop_bodies: usize,
    pub loop_afters: usize,
    pub aborts_companions: usize,
    pub requires_companions: usize,
    pub ensures_companions: usize,
    pub asserts_companions: usize,
    pub source_functions: usize,
}

/// Compute counts for `program`. Pure, allocates nothing beyond
/// the returned struct.
pub fn counts(program: &Program) -> ProgramCounts {
    use crate::ir::function::{FunctionKind, SpecKind};
    let mut c = ProgramCounts {
        modules: program.modules.len(),
        structs: program.structs.len(),
        functions: program.functions.len(),
        natives: program.natives.decls.len(),
        loop_bodies: 0,
        loop_afters: 0,
        aborts_companions: 0,
        requires_companions: 0,
        asserts_companions: 0,
        ensures_companions: 0,
        source_functions: 0,
    };
    for func in program.functions.values() {
        match &func.kind {
            FunctionKind::Source => c.source_functions += 1,
            FunctionKind::LoopBody { .. } => c.loop_bodies += 1,
            FunctionKind::LoopAfter { .. } => c.loop_afters += 1,
            FunctionKind::Spec { kind, .. } => match kind {
                SpecKind::Aborts => c.aborts_companions += 1,
                SpecKind::Requires => c.requires_companions += 1,
                SpecKind::Ensures => c.ensures_companions += 1,
                SpecKind::Asserts => c.asserts_companions += 1,
            },
            _ => {}
        }
    }
    c
}

#[cfg(test)]
mod tier5_tests {
    use super::*;

    #[test]
    fn counts_on_empty_program() {
        let p = Program::default();
        let c = counts(&p);
        assert_eq!(c.modules, 0);
        assert_eq!(c.structs, 0);
        assert_eq!(c.functions, 0);
        assert_eq!(c.natives, 0);
        assert_eq!(c.source_functions, 0);
    }
}
