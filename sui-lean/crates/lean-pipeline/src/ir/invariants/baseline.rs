//! Cross-pipeline structural invariants. Most are established by
//! `ProgramBuilder` / stage 2 and held through `Stage::Render`; the exact
//! auto-dereference form checks are established only at the render boundary.
//!
//! ## Coverage
//!
//! - [`BaselineWellFormedness`] -- umbrella that runs the existing
//!   [`crate::ir::validate::validate_program`] checker. Covers every
//!   [`crate::ir::validate::ValidationErrorKind`] variant in one
//!   pass.
//! - [`CallArityMatchesSignature`] -- every `Expr::Call`'s arg count
//!   equals the callee's `Signature::params.len()`. The baseline
//!   validator only checks `FunId` resolution today; this is the
//!   silent-failure path most relevant to the renderer.
//! - [`CallTypesMatchSignature`] -- at the render boundary, every call has
//!   the callee's type-argument arity and every value argument can be emitted
//!   at its instantiated parameter type.
//! - `MatchArm::bindings` arity is enforced by the baseline validator from
//!   `Expr::Match::struct_id` and the arm's declared variant tag.

use crate::ir::validate::validate_program;
use crate::ir::visit::{walk_expr_default, Visitor};
use crate::ir::{Expr, Program, Type};

use super::traits::{Invariant, InvariantViolation, Stage};

// ---------------------------------------------------------------------
// BaselineWellFormedness
// ---------------------------------------------------------------------

/// Runs [`crate::ir::validate::validate_program`] -- the existing,
/// always-on well-formedness checker. Translates the first
/// [`ValidationError`] into an [`InvariantViolation`] with a stringly
/// formatted detail.
///
/// Fine-grained per-variant invariants can be added later as a pure
/// refactor (split this umbrella into N impls). For now the umbrella
/// shape is enough to plumb baseline checks into the framework at
/// every stage.
pub struct BaselineWellFormedness;

impl Invariant for BaselineWellFormedness {
    fn id(&self) -> &'static str {
        "baseline-well-formedness"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        match validate_program(program) {
            Ok(()) => Ok(()),
            Err(e) => Err(vec![InvariantViolation::new(
                "baseline-well-formedness",
                e.function,
                format!("{:?}", e.kind),
            )]),
        }
    }
}

static BASELINE_WELL_FORMEDNESS: BaselineWellFormedness = BaselineWellFormedness;

// ---------------------------------------------------------------------
// CallArityMatchesSignature
// ---------------------------------------------------------------------

/// Every `Expr::Call { fun, args }`'s argument count matches the
/// resolved callee's `Signature::params.len()`. The base validator
/// catches `UnknownFunctionId` but not arity drift.
///
/// Arity drift is a common silent failure: stage 4 augments callers to pass
/// `world`, and stage 7 synthesizes helper signatures and their callsites. A
/// missed callsite leaves args.len() off by one and the renderer emits broken
/// Lean. The invariant catches it at the earliest stage where the discrepancy
/// exists.
pub struct CallArityMatchesSignature;

impl Invariant for CallArityMatchesSignature {
    fn id(&self) -> &'static str {
        "call-arity-matches-signature"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut walker = CallArityWalker {
            program,
            current_fn: None,
            violations: Vec::new(),
        };
        for (fid, func) in &program.functions {
            walker.current_fn = Some(*fid);
            walker.visit_block(&func.body);
        }
        if walker.violations.is_empty() {
            Ok(())
        } else {
            Err(walker.violations)
        }
    }
}

static CALL_ARITY_MATCHES_SIGNATURE: CallArityMatchesSignature = CallArityMatchesSignature;

struct CallArityWalker<'a> {
    program: &'a Program,
    current_fn: Option<crate::ir::FunId>,
    violations: Vec<InvariantViolation>,
}

impl<'a> Visitor for CallArityWalker<'a> {
    fn visit_expr(&mut self, e: &Expr) {
        // Skip Quantifier bodies. Stage 4's call-augment pass
        // deliberately leaves Calls inside Quantifier bodies
        // un-threaded (see the doc on `compute_needs_world` in
        // `stage_04_effects::common`), so a Quantifier-body callsite
        // can legitimately have N args when its callee's signature
        // has N+1 params (the trailing World slot stage 4 added).
        // The renderer treats those Calls as uninterpreted symbols
        // anyway -- the arity mismatch is invisible at the Lean
        // boundary. Checking inside would surface a forest of
        // false positives for every `forall!` / `exists!` /
        // `sum_map!` over impure framework natives.
        if let Expr::Quantifier { domain, .. } = e {
            use crate::ir::QuantDomain;
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    self.visit_expr(start);
                    self.visit_expr(end);
                }
                QuantDomain::Collection(c) => self.visit_expr(c),
                QuantDomain::VecRange { vec, start, end } => {
                    self.visit_expr(vec);
                    self.visit_expr(start);
                    self.visit_expr(end);
                }
            }
            return;
        }
        if let Expr::Call { fun, args, .. } = e {
            if let Some(callee) = self.program.lookup_callee(*fun) {
                let expected = callee.signature().params.len();
                let actual = args.len();
                if expected != actual {
                    self.violations.push(InvariantViolation::new(
                        "call-arity-matches-signature",
                        self.current_fn,
                        format!("callee {} expects {} args, got {}", fun, expected, actual,),
                    ));
                }
            }
            // Unknown FunIds are handled by the BaselineWellFormedness
            // invariant -- not our responsibility here.
        }
        walk_expr_default(self, e);
    }
}

// ---------------------------------------------------------------------
// FunctionModuleRegistered
// ---------------------------------------------------------------------

/// Every `Function::module` field points at a `ModId` that has a
/// corresponding entry in `program.modules`. Same for every
/// `NativeDecl::module`.
///
/// The base validator's `UnknownModuleId` walker fires only when it
/// traverses a function body. Bodyless entries (natives in
/// `program.natives.decls`, function stubs) can carry a dangling
/// `module` slot that the body walker never visits. Promoted to
/// baseline so the invariant holds across every stage and covers
/// both `program.functions` and `program.natives.decls`.
pub struct FunctionModuleRegistered;

impl Invariant for FunctionModuleRegistered {
    fn id(&self) -> &'static str {
        "function-module-registered"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut violations = Vec::new();
        for (fid, func) in &program.functions {
            if !program.modules.contains_key(&func.module) {
                violations.push(InvariantViolation::new(
                    "function-module-registered",
                    Some(*fid),
                    format!("Function::module {} not in program.modules", func.module),
                ));
            }
        }
        for (fid, decl) in &program.natives.decls {
            if !program.modules.contains_key(&decl.module) {
                violations.push(InvariantViolation::new(
                    "function-module-registered",
                    Some(*fid),
                    format!("NativeDecl::module {} not in program.modules", decl.module),
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

static FUNCTION_MODULE_REGISTERED: FunctionModuleRegistered = FunctionModuleRegistered;

// ---------------------------------------------------------------------
// ReferencedStructIdResolves
// ---------------------------------------------------------------------

/// Every `StructId` reachable from the IR (via type position or any
/// `struct_id`-carrying expression) has a corresponding `Struct`
/// entry in `program.structs`.
///
/// The base validator's `UnknownStructId` fires only at the use
/// sites it walks (function body expressions). Signatures, struct
/// field types, enum-variant field types, and unreferenced
/// `Function`s can carry a dangling id that the body walker never
/// sees. This invariant broadens the check to every reachable
/// `StructId` -- promoted from stage 2's local postcondition.
pub struct ReferencedStructIdResolves;

impl Invariant for ReferencedStructIdResolves {
    fn id(&self) -> &'static str {
        "referenced-struct-id-resolves"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut walker = StructIdWalker {
            program,
            violations: Vec::new(),
            current_fn: None,
        };
        for (fid, func) in &program.functions {
            walker.current_fn = Some(*fid);
            for p in &func.signature.params {
                walker.check_type(&p.ty);
            }
            walker.check_type(&func.signature.return_type);
            walker.visit_block(&func.body);
        }
        for (fid, decl) in &program.natives.decls {
            walker.current_fn = Some(*fid);
            for p in &decl.signature.params {
                walker.check_type(&p.ty);
            }
            walker.check_type(&decl.signature.return_type);
        }
        walker.current_fn = None;
        for global in program.globals.values() {
            walker.check_type(&global.ty);
        }
        for s in program.structs.values() {
            for f in &s.fields {
                walker.check_type(&f.field_type);
            }
            if let Some(variants) = &s.variants {
                for v in variants {
                    for f in &v.fields {
                        walker.check_type(&f.field_type);
                    }
                }
            }
        }
        if walker.violations.is_empty() {
            Ok(())
        } else {
            Err(walker.violations)
        }
    }
}

static REFERENCED_STRUCT_ID_RESOLVES: ReferencedStructIdResolves = ReferencedStructIdResolves;

struct StructIdWalker<'a> {
    program: &'a Program,
    violations: Vec<InvariantViolation>,
    current_fn: Option<crate::ir::FunId>,
}

impl<'a> StructIdWalker<'a> {
    fn flag(&mut self, struct_id: usize) {
        if !self.program.structs.contains_key(&struct_id) {
            self.violations.push(InvariantViolation::new(
                "referenced-struct-id-resolves",
                self.current_fn,
                format!("struct id {} not in program.structs", struct_id),
            ));
        }
    }

    fn check_type(&mut self, ty: &crate::ir::Type) {
        match ty {
            crate::ir::Type::Struct {
                struct_id,
                type_args,
            } => {
                self.flag(*struct_id);
                type_args.iter().for_each(|a| self.check_type(a));
            }
            crate::ir::Type::Vector(inner) | crate::ir::Type::Reference(inner) => {
                self.check_type(inner)
            }
            crate::ir::Type::MutableRef { inner, root } => {
                self.check_type(inner);
                self.check_type(root);
            }
            crate::ir::Type::Tuple(elems) => elems.iter().for_each(|e| self.check_type(e)),
            crate::ir::Type::Unit
            | crate::ir::Type::Bool
            | crate::ir::Type::Prop
            | crate::ir::Type::UInt(_)
            | crate::ir::Type::Address
            | crate::ir::Type::TypeParam(_) => {}
        }
    }
}

impl<'a> Visitor for StructIdWalker<'a> {
    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::Pack {
                struct_id,
                type_args,
                ..
            } => {
                self.flag(*struct_id);
                type_args.iter().for_each(|a| self.check_type(a));
            }
            Expr::Unpack { struct_id, .. } | Expr::Field { struct_id, .. } => self.flag(*struct_id),
            Expr::Borrow { step, .. } | Expr::Update { step, .. } => match step {
                crate::ir::path::PathStep::Field { struct_id, .. }
                | crate::ir::path::PathStep::VariantField { struct_id, .. } => {
                    self.flag(*struct_id)
                }
                crate::ir::path::PathStep::VecIndex(_)
                | crate::ir::path::PathStep::MapKey { .. } => {}
            },
            Expr::Call { type_args, .. } => type_args.iter().for_each(|a| self.check_type(a)),
            Expr::Quantifier { binder_type, .. } => self.check_type(binder_type),
            _ => {}
        }
        walk_expr_default(self, e);
    }
}

// ---------------------------------------------------------------------
// FieldIndexInRange
// ---------------------------------------------------------------------

/// Every `Expr::Field/UpdateField/BorrowField { struct_id, field_index }`
/// has `field_index` within the registered struct's field count.
/// Same for `BorrowEdge::StructField { struct_id, field_index }`
/// (including those nested inside `BorrowEdge::Hyper`).
///
/// Catches the silent corruption class where a stage's transformation
/// rewrites a Pack/UpdateField site with a stale field index. Without
/// this check the renderer emits `vault.field_7` for a 4-field struct
/// and Lean rejects with an unrelated "field_N is not a field of
/// structure" diagnostic many seconds of pipeline later.
///
/// See `plans/lean-pipeline/new-invariant-checks.md` Tier 1 #2.
pub struct FieldIndexInRange;

impl Invariant for FieldIndexInRange {
    fn id(&self) -> &'static str {
        "field-index-in-range"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut w = FieldIndexWalker {
            program,
            current_fn: None,
            violations: Vec::new(),
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

static FIELD_INDEX_IN_RANGE: FieldIndexInRange = FieldIndexInRange;

struct FieldIndexWalker<'a> {
    program: &'a Program,
    current_fn: Option<crate::ir::FunId>,
    violations: Vec<InvariantViolation>,
}

impl<'a> FieldIndexWalker<'a> {
    /// Check a `(struct_id, variant: Option<usize>, field_index)`
    /// triple against the registered struct. Reports an
    /// `out-of-range` violation if the struct exists but the
    /// field_index is too high. A missing struct id is the
    /// `referenced-struct-id-resolves` invariant's problem, not
    /// ours.
    fn check_field(
        &mut self,
        struct_id: crate::ir::StructId,
        variant: Option<usize>,
        field_index: usize,
        ctx: &str,
    ) {
        let Some(s) = self.program.structs.get(&struct_id) else {
            return;
        };
        let max = match (variant, s.variants.as_ref()) {
            (Some(tag), Some(_)) => s.variant_by_tag(tag).map(|variant| variant.fields.len()),
            _ => Some(s.fields.len()),
        };
        let Some(max) = max else {
            // Variant out of range -- not our concern.
            return;
        };
        if field_index >= max {
            self.violations.push(InvariantViolation::new(
                "field-index-in-range",
                self.current_fn,
                format!(
                    "{}: struct_id {} field_index {} >= {} fields",
                    ctx, struct_id, field_index, max,
                ),
            ));
        }
    }

    fn check_edge(&mut self, edge: &crate::ir::BorrowEdge, ctx: &str) {
        match edge {
            crate::ir::BorrowEdge::StructField {
                struct_id,
                field_index,
            } => self.check_field(*struct_id, None, *field_index, ctx),
            crate::ir::BorrowEdge::EnumField {
                struct_id,
                variant,
                field_index,
            } => self.check_field(*struct_id, Some(*variant), *field_index, ctx),
            crate::ir::BorrowEdge::Hyper(inner) => {
                for e in inner {
                    self.check_edge(e, ctx);
                }
            }
            _ => {}
        }
    }
}

impl<'a> Visitor for FieldIndexWalker<'a> {
    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::Field {
                struct_id,
                field_index,
                ..
            } => self.check_field(*struct_id, None, *field_index, "Field"),
            Expr::Borrow {
                step:
                    crate::ir::path::PathStep::Field {
                        struct_id,
                        field_index,
                    },
                ..
            }
            | Expr::Update {
                step:
                    crate::ir::path::PathStep::Field {
                        struct_id,
                        field_index,
                    },
                ..
            } => self.check_field(*struct_id, None, *field_index, "Borrow/Update Field step"),
            Expr::Borrow {
                step:
                    crate::ir::path::PathStep::VariantField {
                        struct_id,
                        variant,
                        field_index,
                    },
                ..
            } => self.check_field(
                *struct_id,
                Some(*variant),
                *field_index,
                "VariantField step",
            ),
            Expr::Update {
                step:
                    crate::ir::path::PathStep::VariantField {
                        struct_id,
                        variant,
                        field_index,
                    },
                ..
            } => self.check_field(
                *struct_id,
                Some(*variant),
                *field_index,
                "VariantField step",
            ),
            Expr::WriteBack { edge, .. } | Expr::IsParent { edge, .. } => {
                self.check_edge(edge, "WriteBack/IsParent edge");
            }
            _ => {}
        }
        walk_expr_default(self, e);
    }
}

// ---------------------------------------------------------------------
// VariantTagsResolveUniquely
// ---------------------------------------------------------------------

/// Every `variant: usize` tag in the IR resolves uniquely in the referenced
/// enum.
///
/// Covered sites:
/// - `MatchArm::variant`
/// - `Expr::Pack` / `Expr::Unpack` (enum tags must be present and resolve)
/// - `PathStep::VariantField { variant, .. }`
/// - `BorrowEdge::EnumField { variant, .. }` (including nested in Hyper)
///
/// See `plans/lean-pipeline/new-invariant-checks.md` Tier 1 #3.
pub struct VariantTagsResolveUniquely;

impl Invariant for VariantTagsResolveUniquely {
    fn id(&self) -> &'static str {
        "variant-tags-resolve-uniquely"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut violations = Vec::new();
        for (struct_id, structure) in &program.structs {
            let Some(variants) = &structure.variants else {
                continue;
            };
            let mut seen = std::collections::BTreeSet::new();
            let mut duplicates = std::collections::BTreeSet::new();
            for variant in variants {
                if !seen.insert(variant.tag) {
                    duplicates.insert(variant.tag);
                }
            }
            for tag in duplicates {
                violations.push(InvariantViolation::new(
                    "variant-tags-resolve-uniquely",
                    None,
                    format!("struct_id {struct_id} has duplicate variant tag {tag}"),
                ));
            }
        }
        let mut w = VariantWalker {
            program,
            current_fn: None,
            violations,
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

static VARIANT_TAGS_RESOLVE_UNIQUELY: VariantTagsResolveUniquely = VariantTagsResolveUniquely;

struct VariantWalker<'a> {
    program: &'a Program,
    current_fn: Option<crate::ir::FunId>,
    violations: Vec<InvariantViolation>,
}

impl<'a> VariantWalker<'a> {
    fn check_optional_variant(
        &mut self,
        struct_id: crate::ir::StructId,
        variant: Option<usize>,
        ctx: &str,
    ) {
        if let Some(tag) = variant {
            self.check_variant(struct_id, tag, ctx);
        } else if self
            .program
            .structs
            .get(&struct_id)
            .is_some_and(|structure| structure.variants.is_some())
        {
            self.violations.push(InvariantViolation::new(
                "variant-tags-resolve-uniquely",
                self.current_fn,
                format!("{ctx}: enum struct_id {struct_id} is missing a variant tag"),
            ));
        }
    }

    fn check_variant(&mut self, struct_id: crate::ir::StructId, variant: usize, ctx: &str) {
        let Some(s) = self.program.structs.get(&struct_id) else {
            return;
        };
        let Some(vs) = &s.variants else {
            self.violations.push(InvariantViolation::new(
                "variant-tags-resolve-uniquely",
                self.current_fn,
                format!(
                    "{}: struct_id {} has no variants (plain struct) but variant {} was used",
                    ctx, struct_id, variant,
                ),
            ));
            return;
        };
        if s.variant_by_tag(variant).is_none() {
            let known_tags = vs
                .iter()
                .map(|candidate| candidate.tag.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            self.violations.push(InvariantViolation::new(
                "variant-tags-resolve-uniquely",
                self.current_fn,
                format!(
                    "{ctx}: struct_id {struct_id} variant tag {variant} does not resolve; known tags: [{known_tags}]",
                ),
            ));
        }
    }

    fn check_edge(&mut self, edge: &crate::ir::BorrowEdge, ctx: &str) {
        match edge {
            crate::ir::BorrowEdge::EnumField {
                struct_id, variant, ..
            } => self.check_variant(*struct_id, *variant, ctx),
            crate::ir::BorrowEdge::Hyper(inner) => {
                for e in inner {
                    self.check_edge(e, ctx);
                }
            }
            _ => {}
        }
    }
}

impl<'a> Visitor for VariantWalker<'a> {
    fn visit_expr(&mut self, e: &Expr) {
        match e {
            Expr::Pack {
                struct_id, variant, ..
            }
            | Expr::Unpack {
                struct_id, variant, ..
            } => self.check_optional_variant(*struct_id, *variant, "Pack/Unpack variant"),
            Expr::Borrow {
                step:
                    crate::ir::path::PathStep::VariantField {
                        struct_id, variant, ..
                    },
                ..
            }
            | Expr::Update {
                step:
                    crate::ir::path::PathStep::VariantField {
                        struct_id, variant, ..
                    },
                ..
            } => self.check_variant(*struct_id, *variant, "VariantField step"),
            Expr::WriteBack { edge, .. } | Expr::IsParent { edge, .. } => {
                self.check_edge(edge, "WriteBack/IsParent edge");
            }
            Expr::Match {
                struct_id,
                selector,
                cases,
            } => {
                self.visit_expr(selector);
                for arm in cases {
                    self.check_variant(*struct_id, arm.variant, "MatchArm variant");
                    self.visit_block(&arm.body);
                }
                return;
            }
            _ => {}
        }
        walk_expr_default(self, e);
    }
}

// ---------------------------------------------------------------------
// StructFieldsXorVariants
// ---------------------------------------------------------------------

/// A `Struct` has either non-empty `fields` OR `Some(variants)`, not
/// both. The convention is fields for plain structs, variants for
/// enums.
///
/// Catches data-corruption bugs in struct-construction code paths
/// (stage 2's `module_lift`, stage 4's synthetic World, stage 10's
/// bounded-nat prelude). Cheap, no false positives.
///
/// See `plans/lean-pipeline/new-invariant-checks.md` Tier 1 #4.
pub struct StructFieldsXorVariants;

impl Invariant for StructFieldsXorVariants {
    fn id(&self) -> &'static str {
        "struct-fields-xor-variants"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut violations = Vec::new();
        for (sid, s) in &program.structs {
            if !s.fields.is_empty() && s.variants.is_some() {
                violations.push(InvariantViolation::new(
                    "struct-fields-xor-variants",
                    None,
                    format!(
                        "struct_id {}: has both non-empty fields ({}) and Some(variants) ({})",
                        sid,
                        s.fields.len(),
                        s.variants.as_ref().map(|v| v.len()).unwrap_or(0),
                    ),
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

static STRUCT_FIELDS_XOR_VARIANTS: StructFieldsXorVariants = StructFieldsXorVariants;

// ---------------------------------------------------------------------
// FunctionKindReferencesResolve (Tier 2)
// ---------------------------------------------------------------------

/// Every `FunctionKind::Spec { target }`, `LoopBody { parent }`, and
/// `LoopAfter { parent }` field points at a `FunId` that resolves
/// via `program.lookup_callee`.
///
/// The base validator's `UnknownFunctionId` walker catches Call
/// references but never walks `FunctionKind` fields. Stage 7's
/// LoopBody/LoopAfter extractor can off-by-one on slot allocation
/// and produce a parent pointer to a dropped function -- the
/// renderer then can't find the loop's source function and emits
/// broken Lean. Catches that at the stage boundary.
///
/// See `plans/lean-pipeline/new-invariant-checks.md` Tier 2 #1.
pub struct FunctionKindReferencesResolve;

impl Invariant for FunctionKindReferencesResolve {
    fn id(&self) -> &'static str {
        "function-kind-references-resolve"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        use crate::ir::function::FunctionKind;
        let mut violations = Vec::new();
        for (fid, func) in &program.functions {
            let referenced: Option<(&str, crate::ir::FunId)> = match &func.kind {
                FunctionKind::Spec { target, .. } => Some(("Spec.target", *target)),
                FunctionKind::LoopBody { parent, .. } => Some(("LoopBody.parent", *parent)),
                FunctionKind::LoopAfter { parent, .. } => Some(("LoopAfter.parent", *parent)),
                _ => None,
            };
            if let Some((slot, ref_fid)) = referenced {
                if program.lookup_callee(ref_fid).is_none() {
                    violations.push(InvariantViolation::new(
                        "function-kind-references-resolve",
                        Some(*fid),
                        format!("{} = {} does not resolve via lookup_callee", slot, ref_fid),
                    ));
                }
            }
        }
        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }
}

static FUNCTION_KIND_REFERENCES_RESOLVE: FunctionKindReferencesResolve =
    FunctionKindReferencesResolve;

// ---------------------------------------------------------------------
// BorrowEdgeHyperNonDegenerate (Tier 2)
// ---------------------------------------------------------------------

/// Every `BorrowEdge::Hyper(inner)` has `inner.len() >= 2`. Length 0
/// is meaningless; length 1 should be normalised to the inner edge.
///
/// Locks `ir.md` decision-log #8 as "fail validation rather than
/// silently normalise". Hyper-of-one is a producer bug, not a
/// shape we want flowing through.
///
/// See `plans/lean-pipeline/new-invariant-checks.md` Tier 2 #2.
pub struct BorrowEdgeHyperNonDegenerate;

impl Invariant for BorrowEdgeHyperNonDegenerate {
    fn id(&self) -> &'static str {
        "borrow-edge-hyper-non-degenerate"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut w = HyperWalker {
            current_fn: None,
            violations: Vec::new(),
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

static BORROW_EDGE_HYPER_NON_DEGENERATE: BorrowEdgeHyperNonDegenerate =
    BorrowEdgeHyperNonDegenerate;

struct HyperWalker {
    current_fn: Option<crate::ir::FunId>,
    violations: Vec<InvariantViolation>,
}

impl HyperWalker {
    fn check_edge(&mut self, edge: &crate::ir::BorrowEdge, ctx: &str) {
        if let crate::ir::BorrowEdge::Hyper(inner) = edge {
            if inner.len() < 2 {
                self.violations.push(InvariantViolation::new(
                    "borrow-edge-hyper-non-degenerate",
                    self.current_fn,
                    format!(
                        "{}: Hyper has {} inner edges (must be >= 2)",
                        ctx,
                        inner.len(),
                    ),
                ));
            }
            for e in inner {
                self.check_edge(e, ctx);
            }
        }
    }
}

impl Visitor for HyperWalker {
    fn visit_expr(&mut self, e: &Expr) {
        if let Expr::WriteBack { edge, .. } | Expr::IsParent { edge, .. } = e {
            self.check_edge(edge, "WriteBack/IsParent edge");
        }
        walk_expr_default(self, e);
    }
}

// ---------------------------------------------------------------------
// MatchArmTagsCoverEnumExactly (Tier 2)
// ---------------------------------------------------------------------

/// Every enum match has exactly one arm for each declared variant tag.
pub struct MatchArmTagsCoverEnumExactly;

impl Invariant for MatchArmTagsCoverEnumExactly {
    fn id(&self) -> &'static str {
        "match-arm-tags-cover-enum-exactly"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut w = MatchArmWalker {
            program,
            current_fn: None,
            violations: Vec::new(),
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

static MATCH_ARM_TAGS_COVER_ENUM_EXACTLY: MatchArmTagsCoverEnumExactly =
    MatchArmTagsCoverEnumExactly;

struct MatchArmWalker<'a> {
    program: &'a Program,
    current_fn: Option<crate::ir::FunId>,
    violations: Vec<InvariantViolation>,
}

impl Visitor for MatchArmWalker<'_> {
    fn visit_expr(&mut self, e: &Expr) {
        if let Expr::Match {
            struct_id, cases, ..
        } = e
        {
            let Some(variants) = self
                .program
                .structs
                .get(struct_id)
                .and_then(|structure| structure.variants.as_ref())
            else {
                walk_expr_default(self, e);
                return;
            };
            let expected = variants
                .iter()
                .map(|variant| variant.tag)
                .collect::<std::collections::BTreeSet<_>>();
            let mut actual = std::collections::BTreeSet::new();
            let mut duplicates = std::collections::BTreeSet::new();
            for case in cases {
                if !actual.insert(case.variant) {
                    duplicates.insert(case.variant);
                }
            }
            let missing = expected.difference(&actual).copied().collect::<Vec<_>>();
            let duplicates = duplicates.into_iter().collect::<Vec<_>>();
            let unexpected = actual.difference(&expected).copied().collect::<Vec<_>>();
            if cases.is_empty()
                || !missing.is_empty()
                || !duplicates.is_empty()
                || !unexpected.is_empty()
            {
                self.violations.push(InvariantViolation::new(
                    "match-arm-tags-cover-enum-exactly",
                    self.current_fn,
                    format!(
                        "Match for struct_id {struct_id} must contain each variant tag exactly once; missing {missing:?}, duplicate {duplicates:?}, unexpected {unexpected:?}",
                    ),
                ));
            }
        }
        walk_expr_default(self, e);
    }
}

// ---------------------------------------------------------------------
// FunIdDisjointBetweenFunctionsAndNatives (Tier 2)
// ---------------------------------------------------------------------

/// No `FunId` appears in both `program.functions` and
/// `program.natives.decls`. Per `no-stubs-templated-natives.md`,
/// the two maps share a namespace but their entries should be
/// disjoint after stage 2.
///
/// During the dual-population migration (step 3 of the no-stubs
/// plan) this invariant tolerates: it does nothing on its own to
/// resolve the duplication. But once step 4 lands (drop the
/// `program.functions` stub for natives), the invariant guards
/// against regression.
///
/// See `plans/lean-pipeline/new-invariant-checks.md` Tier 2 #4.
pub struct FunIdDisjointBetweenFunctionsAndNatives;

impl Invariant for FunIdDisjointBetweenFunctionsAndNatives {
    fn id(&self) -> &'static str {
        "funid-disjoint-between-functions-and-natives"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut violations = Vec::new();
        for fid in program.functions.keys() {
            if program.natives.decls.contains_key(fid) {
                violations.push(InvariantViolation::new(
                    "funid-disjoint-between-functions-and-natives",
                    Some(*fid),
                    format!(
                        "FunId {} appears in both program.functions and program.natives.decls",
                        fid,
                    ),
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

static FUNID_DISJOINT_FUNCTIONS_NATIVES: FunIdDisjointBetweenFunctionsAndNatives =
    FunIdDisjointBetweenFunctionsAndNatives;

// ---------------------------------------------------------------------
// NativeDeclNameNonEmpty (Tier 2)
// ---------------------------------------------------------------------

/// Every `NativeDecl::name` is non-empty. Empty names are a data-
/// corruption signal -- stage 2's module_lift is the only producer
/// of NativeDecls and the move-model env never reports an empty
/// name. If one slips through, this fires immediately.
///
/// See `plans/lean-pipeline/new-invariant-checks.md` Tier 2 #5.
pub struct NativeDeclNameNonEmpty;

impl Invariant for NativeDeclNameNonEmpty {
    fn id(&self) -> &'static str {
        "native-decl-name-non-empty"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut violations = Vec::new();
        for (fid, decl) in &program.natives.decls {
            if decl.name.is_empty() {
                violations.push(InvariantViolation::new(
                    "native-decl-name-non-empty",
                    Some(*fid),
                    format!("NativeDecl FunId {} has empty name", fid),
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

static NATIVE_DECL_NAME_NON_EMPTY: NativeDeclNameNonEmpty = NativeDeclNameNonEmpty;

// ---------------------------------------------------------------------
// NoDuplicateModuleNameWithinPackage (Tier 2)
// ---------------------------------------------------------------------

/// No two `Module` entries share the same `(package_name, name)`
/// pair. ModId is unique by BTreeMap, but the (package, name)
/// identity has no enforced uniqueness -- a synthetic-module
/// allocator (stage 4's `ensure_world_module`, stage 10's
/// bounded-nat prelude) could collide with a user-defined module
/// of the same name if the lookup heuristic is wrong.
///
/// Catches the silent-corruption case where two ModIds map to what
/// the renderer treats as "the same" module: cross-module imports
/// would resolve ambiguously, generic Any* generation would emit
/// duplicate declarations.
///
/// See `plans/lean-pipeline/new-invariant-checks.md` Tier 2 #6.
pub struct NoDuplicateModuleNameWithinPackage;

impl Invariant for NoDuplicateModuleNameWithinPackage {
    fn id(&self) -> &'static str {
        "no-duplicate-module-name-within-package"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        use std::collections::BTreeMap;
        let mut by_key: BTreeMap<(&str, &str), Vec<crate::ir::ModId>> = BTreeMap::new();
        for (mid, module) in &program.modules {
            by_key
                .entry((module.package_name.as_str(), module.name.as_str()))
                .or_default()
                .push(*mid);
        }
        let mut violations = Vec::new();
        for ((pkg, name), mids) in &by_key {
            if mids.len() > 1 {
                violations.push(InvariantViolation::new(
                    "no-duplicate-module-name-within-package",
                    None,
                    format!(
                        "package {:?} module {:?} has {} ModIds: {:?}",
                        pkg,
                        name,
                        mids.len(),
                        mids,
                    ),
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

static NO_DUPLICATE_MODULE_NAME: NoDuplicateModuleNameWithinPackage =
    NoDuplicateModuleNameWithinPackage;

// =====================================================================
// Tier 3: type_of-based invariants
// =====================================================================
//
// These invariants leverage `crate::ir::analysis::type_of` to check
// type consistency at sites where the surface IR allows but Lean
// would later reject. Each maintains a scope stack as it walks so
// `type_of` has the binders it needs to resolve `Var` references.

use crate::ir::analysis::scope::{walk_typed_block, TypedScope, TypedScopeVisitor};
use crate::ir::analysis::type_of::{substitute_type_params, type_of, TypeOfError};
use crate::ir::{Block, Function};

/// Build the initial function scope: param name -> type.
fn function_param_scope(
    func: &Function,
) -> std::collections::BTreeMap<crate::ir::VarId, crate::ir::Type> {
    func.signature
        .params
        .iter()
        .map(|p| (p.var.clone(), p.ty.clone()))
        .collect()
}

/// Walk a block with an explicit typed scope, invoking `check_expr` at
/// every expression position.
///
/// Binder types come from the shared typed-scope walker
/// ([`crate::ir::analysis::scope`]): the always-Tuple singleton flatten,
/// accurate match-arm field types, and `While` iter-local typing all
/// live there now. Specialized checks defer scope-building failures to
/// `ir-type-inference-succeeds`, which reports them alongside
/// expression-local failures.
fn walk_block_with_scope(
    block: &Block,
    scope: &mut std::collections::BTreeMap<crate::ir::VarId, crate::ir::Type>,
    program: &Program,
    check_expr: &mut dyn FnMut(
        &Expr,
        &std::collections::BTreeMap<crate::ir::VarId, crate::ir::Type>,
        &Program,
    ),
) {
    let _ = try_walk_block_with_scope(block, scope, program, check_expr);
}

fn try_walk_block_with_scope(
    block: &Block,
    scope: &mut std::collections::BTreeMap<crate::ir::VarId, crate::ir::Type>,
    program: &Program,
    check_expr: &mut dyn FnMut(
        &Expr,
        &std::collections::BTreeMap<crate::ir::VarId, crate::ir::Type>,
        &Program,
    ),
) -> Result<(), TypeOfError> {
    let mut visitor = ScopedCheck {
        check: check_expr,
        program,
    };
    walk_typed_block(&mut visitor, block, scope.clone(), program)
}

/// Adapts an invariant's `check_expr` callback onto the typed-scope read
/// walker.
struct ScopedCheck<'a> {
    check: &'a mut dyn FnMut(
        &Expr,
        &std::collections::BTreeMap<crate::ir::VarId, crate::ir::Type>,
        &Program,
    ),
    program: &'a Program,
}

impl TypedScopeVisitor for ScopedCheck<'_> {
    type Error = TypeOfError;

    fn visit_expr(&mut self, e: &Expr, scope: &TypedScope) -> Result<(), TypeOfError> {
        (self.check)(e, scope, self.program);
        Ok(())
    }
}

// ---------------------------------------------------------------------
// Call type compatibility (Tier 3)
// ---------------------------------------------------------------------

/// Every rendered call has the callee's exact generic arity, and each value
/// argument can be rendered at the corresponding instantiated parameter type.
///
/// This is deliberately a render-boundary invariant: ordinary calls may cross
/// the value/`Mutation` representation boundary during earlier stages, while
/// the renderer has explicit, type-directed coercions for those forms. Calls
/// inside quantifier bodies remain uninterpreted renderer syntax and follow
/// the same exemption as [`CallArityMatchesSignature`].
pub struct CallTypesMatchSignature;

impl Invariant for CallTypesMatchSignature {
    fn id(&self) -> &'static str {
        "call-types-match-signature"
    }

    fn established_by(&self) -> Stage {
        Stage::Render
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut violations = Vec::new();
        for (fid, function) in &program.functions {
            let ignored = quantifier_body_expressions(&function.body);
            let mut scope = function_param_scope(function);
            walk_block_with_scope(
                &function.body,
                &mut scope,
                program,
                &mut |expression, scope, program| {
                    if ignored.contains(&std::ptr::from_ref(expression)) {
                        return;
                    }
                    let Expr::Call {
                        fun,
                        type_args,
                        args,
                    } = expression
                    else {
                        return;
                    };
                    // Native callees are modeled by hand in Lean; their IR
                    // signature is a nominal placeholder that does NOT drive
                    // rendering. The logical connectives (`$prover_imp/iff/neg`)
                    // render as `→`/`↔`/`¬` over ToProp-coerced (Prop) operands,
                    // and the OP-name-dispatched map/dynamic-field natives
                    // (`borrow`/`add`/`remove`/`has` and their `.aborts`) render
                    // via per-native dispatch, not their placeholder signatures.
                    // A signature-based argument-type check therefore produces
                    // false positives on these (Bool-vs-Prop, Unit-vs-MutableRef).
                    // The contract that matters is the hand-written Lean model,
                    // so validate only calls to generated functions.
                    if program.natives.decls.contains_key(fun) {
                        return;
                    }
                    let Some(callee) = program.lookup_callee(*fun) else {
                        return;
                    };
                    let signature = callee.signature();
                    if type_args.len() != signature.type_params.len() {
                        violations.push(InvariantViolation::new(
                            "call-types-match-signature",
                            Some(*fid),
                            format!(
                                "callee {fun} expects {} type args, got {}",
                                signature.type_params.len(),
                                type_args.len(),
                            ),
                        ));
                        return;
                    }
                    // Value arity has its own baseline invariant. Avoid
                    // duplicating that diagnostic and zip only exact calls.
                    if args.len() != signature.params.len() {
                        return;
                    }
                    for (index, (argument, parameter)) in
                        args.iter().zip(&signature.params).enumerate()
                    {
                        let expected = substitute_type_params(&parameter.ty, type_args.as_slice());
                        if crate::render::effective_expr_can_render_as_type(
                            argument, &expected, program, scope,
                        ) {
                            continue;
                        }
                        let actual = type_of(argument, scope, program).map_or_else(
                            |error| format!("<unknown: {error:?}>"),
                            |ty| format!("{ty:?}"),
                        );
                        violations.push(InvariantViolation::new(
                            "call-types-match-signature",
                            Some(*fid),
                            format!(
                                "callee {fun} argument {index} expects {expected:?}, got {actual}"
                            ),
                        ));
                    }
                },
            );
        }
        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }
}

static CALL_TYPES_MATCH_SIGNATURE: CallTypesMatchSignature = CallTypesMatchSignature;

fn quantifier_body_expressions(block: &Block) -> std::collections::BTreeSet<*const Expr> {
    struct Collector {
        depth: usize,
        expressions: std::collections::BTreeSet<*const Expr>,
    }

    impl Visitor for Collector {
        fn visit_expr(&mut self, expression: &Expr) {
            if self.depth > 0 {
                self.expressions.insert(std::ptr::from_ref(expression));
            }
            let Expr::Quantifier { domain, body, .. } = expression else {
                walk_expr_default(self, expression);
                return;
            };
            use crate::ir::QuantDomain;
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    self.visit_expr(start);
                    self.visit_expr(end);
                }
                QuantDomain::Collection(collection) => self.visit_expr(collection),
                QuantDomain::VecRange { vec, start, end } => {
                    self.visit_expr(vec);
                    self.visit_expr(start);
                    self.visit_expr(end);
                }
            }
            self.depth += 1;
            self.visit_block(body);
            self.depth -= 1;
        }
    }

    let mut collector = Collector {
        depth: 0,
        expressions: std::collections::BTreeSet::new(),
    };
    collector.visit_block(block);
    collector.expressions
}

// ---------------------------------------------------------------------
// Rendered branch value compatibility (Tier 3)
// ---------------------------------------------------------------------

pub struct RenderedBranchValueTypesCompatible;

impl Invariant for RenderedBranchValueTypesCompatible {
    fn id(&self) -> &'static str {
        "rendered-branch-value-types-compatible"
    }

    fn established_by(&self) -> Stage {
        Stage::Render
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut violations = Vec::new();
        for (fid, func) in &program.functions {
            let mut scope = function_param_scope(func);
            let fid = *fid;
            let violations = &mut violations;
            let discarded_branches = discarded_branch_nodes(&func.body);
            let let_patterns = let_patterns_by_value(&func.body);
            let var_target_types =
                crate::render::rendered_var_target_types(&func.body, &func.signature.return_type);
            let mut effective_bindings: std::collections::BTreeMap<
                crate::ir::VarId,
                crate::ir::Type,
            > = std::collections::BTreeMap::new();
            walk_block_with_scope(&func.body, &mut scope, program, &mut |e, scope, p| {
                let mut effective_scope = scope.clone();
                for var in scope.keys() {
                    if let Some(rendered_type) = effective_bindings.get(var) {
                        effective_scope.insert(var.clone(), rendered_type.clone());
                    }
                }
                if let Some(pattern) = let_patterns.get(&std::ptr::from_ref(e)) {
                    let target = crate::render::rendered_let_target_type(
                        pattern,
                        e,
                        &var_target_types,
                        p,
                        &effective_scope,
                    );
                    for (var, ty) in crate::render::rendered_let_bindings(
                        pattern,
                        e,
                        target.as_ref(),
                        p,
                        &effective_scope,
                    ) {
                        effective_bindings.insert(var, ty);
                    }
                }
                if discarded_branches.contains(&std::ptr::from_ref(e)) {
                    return;
                }
                let (kind, arms) = match e {
                    Expr::If {
                        then_branch,
                        else_branch,
                        ..
                    } => (
                        "If",
                        vec![
                            (then_branch.as_ref(), effective_scope.clone()),
                            (else_branch.as_ref(), effective_scope.clone()),
                        ],
                    ),
                    Expr::Match {
                        struct_id,
                        selector,
                        cases,
                    } => {
                        let type_args = crate::render::rendered_match_selector_type_args(
                            *struct_id,
                            selector.as_ref(),
                            p,
                            &effective_scope,
                        );
                        let Some(structure) = p.structs.get(struct_id) else {
                            return;
                        };
                        let arms = cases
                            .iter()
                            .filter_map(|arm| {
                                let variant = structure.variant_by_tag(arm.variant)?;
                                let mut arm_scope = effective_scope.clone();
                                arm_scope.extend(arm.bindings.iter().zip(&variant.fields).map(
                                    |(binding, field)| {
                                        (
                                            binding.clone(),
                                            substitute_type_params(&field.field_type, &type_args),
                                        )
                                    },
                                ));
                                Some((arm.body.as_ref(), arm_scope))
                            })
                            .collect();
                        ("Match", arms)
                    }
                    _ => return,
                };

                let arm_types = arms
                    .iter()
                    .map(|(block, arm_scope)| {
                        crate::render::effective_block_branch_type(block, p, arm_scope)
                    })
                    .collect::<Vec<_>>();
                if arm_types
                    .iter()
                    .any(|arm| matches!(arm, crate::render::EffectiveBranchType::Unknown))
                {
                    violations.push(InvariantViolation::new(
                        "rendered-branch-value-types-compatible",
                        Some(fid),
                        format!("{kind} has a value arm whose emitted type is unknown"),
                    ));
                    return;
                }
                let Ok(unified) = crate::render::unify_effective_branch_types(&arm_types) else {
                    let (left, right) = first_incompatible_rendered_arm_types(&arm_types)
                        .unwrap_or((Type::Unit, Type::Unit));
                    violations.push(InvariantViolation::new(
                        "rendered-branch-value-types-compatible",
                        Some(fid),
                        format!(
                            "{kind} value arms emit incompatible types: {left:?} versus {right:?}"
                        ),
                    ));
                    return;
                };
                let Some(target) = unified else {
                    return;
                };
                if arms.iter().any(|(block, arm_scope)| {
                    !crate::render::effective_block_can_render_as_type(block, &target, p, arm_scope)
                }) {
                    violations.push(InvariantViolation::new(
                        "rendered-branch-value-types-compatible",
                        Some(fid),
                        format!(
                            "{kind} value arms require a coercion the renderer cannot emit to {target:?}"
                        ),
                    ));
                }
            });
        }
        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }
}

fn first_incompatible_rendered_arm_types(
    arm_types: &[crate::render::EffectiveBranchType],
) -> Option<(Type, Type)> {
    let mut unified = None;
    for next in arm_types.iter().filter_map(|arm| match arm {
        crate::render::EffectiveBranchType::Known(ty) => Some(ty.clone()),
        crate::render::EffectiveBranchType::Terminal
        | crate::render::EffectiveBranchType::Unknown => None,
    }) {
        let Some(previous) = unified.take() else {
            unified = Some(next);
            continue;
        };
        let pair = [
            crate::render::EffectiveBranchType::Known(previous.clone()),
            crate::render::EffectiveBranchType::Known(next.clone()),
        ];
        let Ok(Some(next_unified)) = crate::render::unify_effective_branch_types(&pair) else {
            return Some((previous, next));
        };
        unified = Some(next_unified);
    }
    None
}

fn let_patterns_by_value(
    block: &Block,
) -> std::collections::BTreeMap<*const Expr, Vec<Option<crate::ir::VarId>>> {
    struct Collector {
        patterns: std::collections::BTreeMap<*const Expr, Vec<Option<crate::ir::VarId>>>,
    }

    impl Visitor for Collector {
        fn visit_stmt(&mut self, statement: &crate::ir::Stmt) {
            if let crate::ir::Stmt::Let { pattern, value } = statement {
                self.patterns
                    .insert(std::ptr::from_ref(value), pattern.clone());
            }
            crate::ir::visit::walk_stmt_default(self, statement);
        }
    }

    let mut collector = Collector {
        patterns: std::collections::BTreeMap::new(),
    };
    collector.visit_block(block);
    collector.patterns
}

fn discarded_branch_nodes(block: &Block) -> std::collections::BTreeSet<*const Expr> {
    struct Collector {
        nodes: std::collections::BTreeSet<*const Expr>,
    }

    impl Collector {
        fn mark_all_branches(&mut self, expression: &Expr) {
            struct AllBranches<'a> {
                nodes: &'a mut std::collections::BTreeSet<*const Expr>,
            }

            impl Visitor for AllBranches<'_> {
                fn visit_expr(&mut self, expression: &Expr) {
                    if matches!(expression, Expr::If { .. } | Expr::Match { .. }) {
                        self.nodes.insert(std::ptr::from_ref(expression));
                    }
                    walk_expr_default(self, expression);
                }
            }

            AllBranches {
                nodes: &mut self.nodes,
            }
            .visit_expr(expression);
        }

        fn mark_statement_branches(&mut self, statement: &crate::ir::Stmt) {
            match statement {
                crate::ir::Stmt::Let { value, .. } | crate::ir::Stmt::Eval(value) => {
                    self.mark_all_branches(value);
                }
            }
        }

        fn visit_function_block(&mut self, block: &Block) {
            for statement in &block.stmts {
                self.visit_stmt(statement);
            }
            match &block.tail {
                crate::ir::BlockTail::Value(expression) => self.visit_expr(expression),
                crate::ir::BlockTail::Return(expression)
                | crate::ir::BlockTail::ReturnFromBlock {
                    value: expression, ..
                } => self.visit_expr(expression.as_ref()),
                crate::ir::BlockTail::Abort { code }
                | crate::ir::BlockTail::Break { value: code, .. }
                | crate::ir::BlockTail::Continue { value: code, .. } => {
                    self.mark_all_branches(code);
                }
            }
        }

        fn visit_inner_value_block(&mut self, block: &Block) {
            for statement in &block.stmts {
                if crate::render::rendered_inner_statement_is_erased(statement) {
                    self.mark_statement_branches(statement);
                } else {
                    self.visit_stmt(statement);
                }
            }
            match &block.tail {
                crate::ir::BlockTail::Value(expression) => self.visit_expr(expression),
                crate::ir::BlockTail::Abort { code }
                | crate::ir::BlockTail::Break { value: code, .. }
                | crate::ir::BlockTail::Continue { value: code, .. }
                | crate::ir::BlockTail::Return(code)
                | crate::ir::BlockTail::ReturnFromBlock { value: code, .. } => {
                    self.mark_all_branches(code);
                }
            }
        }

        fn visit_eval_expr(&mut self, expression: &Expr) {
            match expression {
                Expr::If {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    self.nodes.insert(std::ptr::from_ref(expression));
                    self.visit_expr(cond);
                    self.visit_eval_block(then_branch);
                    self.visit_eval_block(else_branch);
                }
                Expr::Match {
                    selector, cases, ..
                } => {
                    self.nodes.insert(std::ptr::from_ref(expression));
                    self.visit_expr(selector);
                    for arm in cases {
                        self.visit_eval_block(&arm.body);
                    }
                }
                _ => self.visit_expr(expression),
            }
        }

        fn visit_eval_block(&mut self, block: &Block) {
            for statement in &block.stmts {
                self.visit_stmt(statement);
            }
            match &block.tail {
                crate::ir::BlockTail::Value(expression) => self.visit_eval_expr(expression),
                crate::ir::BlockTail::Abort { code }
                | crate::ir::BlockTail::Break { value: code, .. }
                | crate::ir::BlockTail::Continue { value: code, .. }
                | crate::ir::BlockTail::Return(code)
                | crate::ir::BlockTail::ReturnFromBlock { value: code, .. } => {
                    self.mark_all_branches(code);
                }
            }
        }
    }

    impl Visitor for Collector {
        fn visit_block(&mut self, block: &Block) {
            self.visit_inner_value_block(block);
        }

        fn visit_stmt(&mut self, statement: &crate::ir::Stmt) {
            match statement {
                crate::ir::Stmt::Let { value, .. } => self.visit_expr(value),
                crate::ir::Stmt::Eval(expression) => self.visit_eval_expr(expression),
            }
        }

        fn visit_expr(&mut self, expression: &Expr) {
            match expression {
                Expr::If {
                    cond,
                    then_branch,
                    else_branch,
                } => {
                    self.visit_expr(cond);
                    self.visit_inner_value_block(then_branch);
                    self.visit_inner_value_block(else_branch);
                }
                Expr::Match {
                    selector, cases, ..
                } => {
                    self.visit_expr(selector);
                    for arm in cases {
                        self.visit_inner_value_block(&arm.body);
                    }
                }
                _ => walk_expr_default(self, expression),
            }
        }
    }

    let mut collector = Collector {
        nodes: std::collections::BTreeSet::new(),
    };
    collector.visit_function_block(block);
    collector.nodes
}

static RENDERED_BRANCH_VALUE_TYPES_COMPATIBLE: RenderedBranchValueTypesCompatible =
    RenderedBranchValueTypesCompatible;

// ---------------------------------------------------------------------
// Auto-dereference compatibility and final value-form checks (Tier 3)
// ---------------------------------------------------------------------

fn auto_deref_type(ty: &Type) -> &Type {
    match ty {
        Type::Reference(inner) | Type::MutableRef { inner, .. } => inner,
        _ => ty,
    }
}

fn check_if_while_cond_types(
    program: &Program,
    invariant: &'static str,
    auto_deref: bool,
) -> Result<(), Vec<InvariantViolation>> {
    let mut violations = Vec::new();
    for (fid, func) in &program.functions {
        let mut scope = function_param_scope(func);
        let fid_copy = *fid;
        let viol_ref = &mut violations;
        walk_block_with_scope(&func.body, &mut scope, program, &mut |e, s, p| {
            if let Expr::If { cond, .. } | Expr::While { cond, .. } = e {
                if let Ok(ty) = type_of(cond, s, p) {
                    let checked = if auto_deref {
                        auto_deref_type(&ty)
                    } else {
                        &ty
                    };
                    if !matches!(checked, Type::Bool) {
                        viol_ref.push(InvariantViolation::new(
                            invariant,
                            Some(fid_copy),
                            format!("cond has type {:?}, expected Bool", ty),
                        ));
                    }
                }
            }
        });
    }
    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

/// Every condition denotes a Bool after Move's implicit auto-dereference.
pub struct IfWhileCondValuesAreBool;

impl Invariant for IfWhileCondValuesAreBool {
    fn id(&self) -> &'static str {
        "if-while-cond-values-are-bool"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        check_if_while_cond_types(program, self.id(), true)
    }
}

static IF_WHILE_COND_VALUES_ARE_BOOL: IfWhileCondValuesAreBool = IfWhileCondValuesAreBool;

/// At render, every condition has literal type `Bool`, with no implicit
/// reference projection left for the renderer to guess.
///
/// See `plans/lean-pipeline/new-invariant-checks.md` Tier 3.
pub struct IfWhileCondsAreBool;

impl Invariant for IfWhileCondsAreBool {
    fn id(&self) -> &'static str {
        "if-while-conds-are-bool"
    }

    fn established_by(&self) -> Stage {
        Stage::Render
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        check_if_while_cond_types(program, self.id(), false)
    }
}

static IF_WHILE_CONDS_ARE_BOOL: IfWhileCondsAreBool = IfWhileCondsAreBool;

// ---------------------------------------------------------------------
// BinOp operand compatibility and final agreement (Tier 3)
// ---------------------------------------------------------------------

fn check_binop_operand_types(
    program: &Program,
    invariant: &'static str,
    auto_deref: bool,
) -> Result<(), Vec<InvariantViolation>> {
    use crate::ir::ops::BinOp;
    let mut violations = Vec::new();
    for (fid, func) in &program.functions {
        let mut scope = function_param_scope(func);
        let fid_copy = *fid;
        let viol_ref = &mut violations;
        walk_block_with_scope(&func.body, &mut scope, program, &mut |e, s, p| {
            if let Expr::BinOp { op, lhs, rhs } = e {
                let lhs_ty = type_of(lhs, s, p).ok();
                let rhs_ty = type_of(rhs, s, p).ok();
                let (Some(lt), Some(rt)) = (lhs_ty, rhs_ty) else {
                    return;
                };
                let checked_lt = if auto_deref {
                    auto_deref_type(&lt)
                } else {
                    &lt
                };
                let checked_rt = if auto_deref {
                    auto_deref_type(&rt)
                } else {
                    &rt
                };
                let allow_width_mismatch =
                    matches!(op, BinOp::Shl | BinOp::Shr | BinOp::LShr | BinOp::AShr);
                let has_raw_reference = matches!(&lt, Type::Reference(_) | Type::MutableRef { .. })
                    || matches!(&rt, Type::Reference(_) | Type::MutableRef { .. });
                let violates = if auto_deref {
                    !allow_width_mismatch && checked_lt != checked_rt
                } else {
                    has_raw_reference || (!allow_width_mismatch && checked_lt != checked_rt)
                };
                if violates {
                    viol_ref.push(InvariantViolation::new(
                        invariant,
                        Some(fid_copy),
                        format!(
                            "BinOp {:?}: lhs has type {:?}, rhs has type {:?}",
                            op, lt, rt,
                        ),
                    ));
                }
            }
        });
    }
    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

/// Every binary operation's operands agree after Move auto-dereference.
pub struct BinOpOperandValueTypesAgree;

impl Invariant for BinOpOperandValueTypesAgree {
    fn id(&self) -> &'static str {
        "binop-operand-value-types-agree"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        check_binop_operand_types(program, self.id(), true)
    }
}

static BINOP_OPERAND_VALUE_TYPES_AGREE: BinOpOperandValueTypesAgree = BinOpOperandValueTypesAgree;

/// For every `Expr::BinOp { op, lhs, rhs }` where `op` requires
/// matching operand types (arithmetic / bitwise / shift / comparison
/// over the same `UInt(N)`, logical `And`/`Or` over `Bool`), check
/// that `type_of(lhs) == type_of(rhs)` (modulo shift's per-side
/// allowance for different `UInt` widths).
///
/// This is the final-form companion to [`BinOpOperandValueTypesAgree`].
/// Intermediate Move auto-deref shapes may differ by one reference layer;
/// final normalization must make the operand types literally agree.
///
/// See `plans/lean-pipeline/new-invariant-checks.md` Tier 3.
pub struct BinOpOperandTypesAgree;

impl Invariant for BinOpOperandTypesAgree {
    fn id(&self) -> &'static str {
        "binop-operand-types-agree"
    }

    fn established_by(&self) -> Stage {
        Stage::Render
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        check_binop_operand_types(program, self.id(), false)
    }
}

static BINOP_OPERAND_TYPES_AGREE: BinOpOperandTypesAgree = BinOpOperandTypesAgree;

// ---------------------------------------------------------------------
// Pack field compatibility and final agreement (Tier 3)
// ---------------------------------------------------------------------

fn same_value_type_ignoring_mutable_roots(actual: &Type, expected: &Type) -> bool {
    match (actual, expected) {
        (
            Type::MutableRef { inner: actual, .. },
            Type::MutableRef {
                inner: expected, ..
            },
        )
        | (Type::Reference(actual), Type::Reference(expected))
        | (Type::Vector(actual), Type::Vector(expected)) => {
            same_value_type_ignoring_mutable_roots(actual, expected)
        }
        (Type::Tuple(actual), Type::Tuple(expected)) => {
            actual.len() == expected.len()
                && actual.iter().zip(expected).all(|(actual, expected)| {
                    same_value_type_ignoring_mutable_roots(actual, expected)
                })
        }
        (
            Type::Struct {
                struct_id: actual_id,
                type_args: actual_args,
            },
            Type::Struct {
                struct_id: expected_id,
                type_args: expected_args,
            },
        ) => {
            actual_id == expected_id
                && actual_args.len() == expected_args.len()
                && actual_args
                    .iter()
                    .zip(expected_args)
                    .all(|(actual, expected)| {
                        same_value_type_ignoring_mutable_roots(actual, expected)
                    })
        }
        _ => actual == expected,
    }
}

fn check_pack_field_types(
    program: &Program,
    invariant: &'static str,
    auto_deref: bool,
) -> Result<(), Vec<InvariantViolation>> {
    let mut violations = Vec::new();
    for (fid, func) in &program.functions {
        let mut scope = function_param_scope(func);
        let fid_copy = *fid;
        let viol_ref = &mut violations;
        walk_block_with_scope(&func.body, &mut scope, program, &mut |e, s, p| {
            let Expr::Pack {
                struct_id,
                type_args,
                variant,
                fields,
            } = e
            else {
                return;
            };
            let Some(decl) = p.structs.get(struct_id) else {
                return;
            };
            let declared_fields = match (variant, decl.variants.as_ref()) {
                (Some(tag), Some(_)) => match decl.variant_by_tag(*tag) {
                    Some(variant_decl) => &variant_decl.fields,
                    None => return,
                },
                _ => &decl.fields,
            };
            if declared_fields.len() != fields.len() {
                return;
            }
            for (i, (field_expr, decl_field)) in
                fields.iter().zip(declared_fields.iter()).enumerate()
            {
                let Ok(actual_ty) = type_of(field_expr, s, p) else {
                    continue;
                };
                let expected_ty = substitute_type_params(&decl_field.field_type, type_args);
                let types_match = same_value_type_ignoring_mutable_roots(&actual_ty, &expected_ty)
                    || (auto_deref
                        && same_value_type_ignoring_mutable_roots(
                            auto_deref_type(&actual_ty),
                            &expected_ty,
                        ));
                if !types_match {
                    viol_ref.push(InvariantViolation::new(
                        invariant,
                        Some(fid_copy),
                        format!(
                            "Pack struct_id {} field {} ({:?}): expected {:?}, got {:?}",
                            struct_id, i, decl_field.name, expected_ty, actual_ty,
                        ),
                    ));
                }
            }
        });
    }
    if violations.is_empty() {
        Ok(())
    } else {
        Err(violations)
    }
}

/// Every packed field has the declared value type after Move auto-dereference.
pub struct PackFieldValueTypesMatchStructDefinition;

impl Invariant for PackFieldValueTypesMatchStructDefinition {
    fn id(&self) -> &'static str {
        "pack-field-value-types-match-struct-definition"
    }

    fn established_by(&self) -> Stage {
        Stage::Baseline
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        check_pack_field_types(program, self.id(), true)
    }
}

static PACK_FIELD_VALUE_TYPES_MATCH: PackFieldValueTypesMatchStructDefinition =
    PackFieldValueTypesMatchStructDefinition;

/// For every `Expr::Pack { struct_id, type_args, variant, fields }`,
/// each `type_of(fields[i])` matches the declared field value type at
/// position `i` (after `type_args` substitution). `MutableRef.root` is
/// borrow-path provenance rather than part of the value type, so only the
/// mutable reference's `inner` type participates in this comparison.
///
/// This is the final-form companion to
/// [`PackFieldValueTypesMatchStructDefinition`]. Intermediate fields may use
/// Move auto-deref; final normalization must make the value types match.
///
/// See `plans/lean-pipeline/new-invariant-checks.md` Tier 3.
pub struct PackFieldTypesMatchStructDefinition;

impl Invariant for PackFieldTypesMatchStructDefinition {
    fn id(&self) -> &'static str {
        "pack-field-types-match-struct-definition"
    }

    fn established_by(&self) -> Stage {
        Stage::Render
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        check_pack_field_types(program, self.id(), false)
    }
}

static PACK_FIELD_TYPES_MATCH: PackFieldTypesMatchStructDefinition =
    PackFieldTypesMatchStructDefinition;

// ---------------------------------------------------------------------
// IrTypeInferenceSucceeds (Tier 3 umbrella)
// ---------------------------------------------------------------------

/// After SSA has made cross-arm merges explicit, every reachable
/// expression in every function body passes `type_of` without error --
/// catching unbound variables, unknown references, `FieldOutOfRange`,
/// `UnknownVariantTag`, `MalformedAccess`, and `Unsupported` surface bugs
/// in one pass. The provisional pre-SSA IR can legitimately reference an
/// arm-local merge value that stage 5 has not hoisted yet, so this contract
/// is established by stage 5 rather than by the baseline builder.
///
/// See `plans/lean-pipeline/new-invariant-checks.md` Tier 3.
pub struct IrTypeInferenceSucceeds;

impl Invariant for IrTypeInferenceSucceeds {
    fn id(&self) -> &'static str {
        "ir-type-inference-succeeds"
    }

    fn established_by(&self) -> Stage {
        Stage::S05Ssa
    }

    fn held_through(&self) -> Stage {
        Stage::Render
    }

    fn check(&self, program: &Program) -> Result<(), Vec<InvariantViolation>> {
        let mut violations: Vec<InvariantViolation> = Vec::new();
        for (fid, func) in &program.functions {
            let mut scope = function_param_scope(func);
            let mut details = std::collections::BTreeSet::new();
            let walk_result =
                try_walk_block_with_scope(&func.body, &mut scope, program, &mut |e, s, p| {
                    let Err(err) = type_of(e, s, p) else {
                        return;
                    };
                    details.insert(format!("{:?}", err));
                });
            if let Err(err) = walk_result {
                details.insert(format!("{:?}", err));
            }
            violations.extend(details.into_iter().map(|detail| {
                InvariantViolation::new("ir-type-inference-succeeds", Some(*fid), detail)
            }));
        }
        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }
}

static IR_TYPE_INFERENCE_SUCCEEDS: IrTypeInferenceSucceeds = IrTypeInferenceSucceeds;

// ---------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------

pub(crate) static INVARIANTS: &[&'static dyn Invariant] = &[
    &BASELINE_WELL_FORMEDNESS,
    &CALL_ARITY_MATCHES_SIGNATURE,
    &FUNCTION_MODULE_REGISTERED,
    &REFERENCED_STRUCT_ID_RESOLVES,
    &FIELD_INDEX_IN_RANGE,
    &VARIANT_TAGS_RESOLVE_UNIQUELY,
    &STRUCT_FIELDS_XOR_VARIANTS,
    // Tier 2
    &FUNCTION_KIND_REFERENCES_RESOLVE,
    &BORROW_EDGE_HYPER_NON_DEGENERATE,
    &MATCH_ARM_TAGS_COVER_ENUM_EXACTLY,
    &FUNID_DISJOINT_FUNCTIONS_NATIVES,
    &NATIVE_DECL_NAME_NON_EMPTY,
    &NO_DUPLICATE_MODULE_NAME,
    // Tier 3
    &IF_WHILE_COND_VALUES_ARE_BOOL,
    &IF_WHILE_CONDS_ARE_BOOL,
    &BINOP_OPERAND_VALUE_TYPES_AGREE,
    &BINOP_OPERAND_TYPES_AGREE,
    &PACK_FIELD_VALUE_TYPES_MATCH,
    &PACK_FIELD_TYPES_MATCH,
    &CALL_TYPES_MATCH_SIGNATURE,
    &RENDERED_BRANCH_VALUE_TYPES_COMPATIBLE,
    &IR_TYPE_INFERENCE_SUCCEEDS,
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::builder::*;
    use crate::ir::{
        Block, BlockTail, Function, FunctionKind, Module, Param, Signature, Stmt, Type,
    };

    fn empty_module() -> (Program, crate::ir::ModId) {
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
        (p, 0)
    }

    fn make_fn(p: &mut Program, params: Vec<Type>, body: Block) -> crate::ir::FunId {
        let id = p.functions.len();
        p.functions.insert(
            id,
            Function {
                module: 0,
                name: format!("f{id}"),
                signature: Signature {
                    type_params: Vec::new(),
                    params: params
                        .into_iter()
                        .enumerate()
                        .map(|(i, ty)| Param {
                            name: format!("p{i}"),
                            var: format!("p{i}").into(),
                            ty,
                        })
                        .collect(),
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
    fn call_with_correct_arity_passes() {
        let (mut p, _mid) = empty_module();
        // f0 takes one param.
        let callee = make_fn(&mut p, vec![Type::UInt(64)], just(unit()));
        // f1 calls f0 with one arg.
        let mut caller_body = just(unit());
        caller_body
            .stmts
            .push(Stmt::Eval(call(callee, vec![lit_u64(0)])));
        make_fn(&mut p, vec![], caller_body);
        assert!(CallArityMatchesSignature.check(&p).is_ok());
    }

    #[test]
    fn call_with_too_few_args_fails() {
        let (mut p, _mid) = empty_module();
        let callee = make_fn(&mut p, vec![Type::UInt(64), Type::UInt(64)], just(unit()));
        let mut caller_body = just(unit());
        caller_body
            .stmts
            .push(Stmt::Eval(call(callee, vec![lit_u64(0)])));
        make_fn(&mut p, vec![], caller_body);
        let err = CallArityMatchesSignature.check(&p).unwrap_err();
        let err = &err[0];
        assert_eq!(err.invariant, "call-arity-matches-signature");
        assert!(err.detail.contains("expects 2 args, got 1"));
    }

    #[test]
    fn call_with_too_many_args_fails() {
        let (mut p, _mid) = empty_module();
        let callee = make_fn(&mut p, vec![Type::UInt(64)], just(unit()));
        let mut caller_body = just(unit());
        caller_body
            .stmts
            .push(Stmt::Eval(call(callee, vec![lit_u64(0), lit_u64(1)])));
        make_fn(&mut p, vec![], caller_body);
        let err = CallArityMatchesSignature.check(&p).unwrap_err();
        let err = &err[0];
        assert!(err.detail.contains("expects 1 args, got 2"));
    }

    #[test]
    fn render_gate_rejects_call_argument_type_mismatch() {
        let (mut p, _mid) = empty_module();
        let callee = make_fn(&mut p, vec![Type::UInt(32)], just(unit()));
        let mut caller_body = just(unit());
        caller_body.stmts.push(Stmt::Eval(Expr::Call {
            fun: callee,
            type_args: Vec::new(),
            args: vec![Expr::Unit],
        }));
        make_fn(&mut p, vec![], caller_body);

        let errors = crate::ir::invariants::verify_at(Stage::Render, &p).unwrap_err();
        assert!(errors.iter().any(|error| {
            error.invariant == "call-types-match-signature"
                && error.detail.contains("expects UInt(32), got Unit")
        }));
    }

    #[test]
    fn call_type_gate_rejects_generic_arity_mismatch() {
        let (mut p, _mid) = empty_module();
        let callee = make_fn(&mut p, vec![Type::TypeParam(0)], just(unit()));
        p.functions
            .get_mut(&callee)
            .expect("callee")
            .signature
            .type_params = vec!["T".to_owned()];
        let mut caller_body = just(unit());
        caller_body.stmts.push(Stmt::Eval(Expr::Call {
            fun: callee,
            type_args: Vec::new(),
            args: vec![lit_u64(7)],
        }));
        make_fn(&mut p, vec![], caller_body);

        let errors = CallTypesMatchSignature.check(&p).unwrap_err();
        assert!(errors[0].detail.contains("expects 1 type args, got 0"));
    }

    #[test]
    fn call_type_gate_accepts_instantiated_generic_argument() {
        let (mut p, _mid) = empty_module();
        let callee = make_fn(&mut p, vec![Type::TypeParam(0)], just(unit()));
        p.functions
            .get_mut(&callee)
            .expect("callee")
            .signature
            .type_params = vec!["T".to_owned()];
        let mut caller_body = just(unit());
        caller_body.stmts.push(Stmt::Eval(Expr::Call {
            fun: callee,
            type_args: vec![Type::UInt(64)],
            args: vec![lit_u64(7)],
        }));
        make_fn(&mut p, vec![], caller_body);

        assert!(CallTypesMatchSignature.check(&p).is_ok());
    }

    #[test]
    fn call_type_gate_accepts_transparent_singleton_tuple_parameter() {
        let (mut p, _mid) = empty_module();
        let callee = make_fn(
            &mut p,
            vec![Type::Tuple(vec![Type::UInt(64)])],
            just(unit()),
        );
        let mut caller_body = just(unit());
        caller_body.stmts.push(Stmt::Eval(Expr::Call {
            fun: callee,
            type_args: Vec::new(),
            args: vec![lit_u64(7)],
        }));
        make_fn(&mut p, vec![], caller_body);

        assert!(CallTypesMatchSignature.check(&p).is_ok());
    }

    #[test]
    fn baseline_well_formedness_catches_unbound_var() {
        let (mut p, _mid) = empty_module();
        // Body references "missing" with no binder.
        make_fn(&mut p, vec![], just(var("missing")));
        let err = BaselineWellFormedness.check(&p).unwrap_err();
        let err = &err[0];
        assert_eq!(err.invariant, "baseline-well-formedness");
        assert!(err.detail.contains("UnboundVariable"));
    }

    #[test]
    fn baseline_well_formedness_passes_on_clean_program() {
        let (mut p, _mid) = empty_module();
        make_fn(&mut p, vec![], just(unit()));
        assert!(BaselineWellFormedness.check(&p).is_ok());
    }

    #[test]
    fn function_module_registered_passes_on_well_formed() {
        let (mut p, _mid) = empty_module();
        make_fn(&mut p, vec![], just(unit()));
        assert!(FunctionModuleRegistered.check(&p).is_ok());
    }

    #[test]
    fn function_module_registered_catches_unregistered_module() {
        let mut p = Program::default();
        // Add a function whose module id (0) was never registered.
        p.functions.insert(
            0,
            Function {
                module: 0,
                name: "f".to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: Type::Unit,
                },
                body: just(unit()),
                kind: FunctionKind::Source,
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
            },
        );
        let err = FunctionModuleRegistered.check(&p).unwrap_err();
        let err = &err[0];
        assert_eq!(err.invariant, "function-module-registered");
        assert!(err.detail.contains("not in program.modules"));
    }

    #[test]
    fn referenced_struct_id_resolves_passes_on_well_formed() {
        let (mut p, _mid) = empty_module();
        make_fn(&mut p, vec![], just(unit()));
        assert!(ReferencedStructIdResolves.check(&p).is_ok());
    }

    #[test]
    fn referenced_struct_id_resolves_catches_dangling_in_signature() {
        let (mut p, _mid) = empty_module();
        // Param type references struct id 7 with no struct entry.
        make_fn(
            &mut p,
            vec![Type::Struct {
                struct_id: 7,
                type_args: Vec::new(),
            }],
            just(unit()),
        );
        let err = ReferencedStructIdResolves.check(&p).unwrap_err();
        let err = &err[0];
        assert_eq!(err.invariant, "referenced-struct-id-resolves");
        assert!(err.detail.contains("struct id 7"));
    }

    #[test]
    fn referenced_struct_id_resolves_catches_dangling_in_struct_field() {
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
        // Outer struct (id 0) has a field of struct id 1 (not registered).
        p.structs.insert(
            0,
            crate::ir::Struct {
                module_id: 0,
                name: "Outer".to_string(),
                qualified_name: "Outer".to_string(),
                type_params: Vec::new(),
                fields: vec![crate::ir::Field {
                    name: "inner".to_string(),
                    field_type: Type::Struct {
                        struct_id: 1,
                        type_args: Vec::new(),
                    },
                }],
                variants: None,
                is_native: false,
            },
        );
        let err = ReferencedStructIdResolves.check(&p).unwrap_err();
        let err = &err[0];
        assert!(err.detail.contains("struct id 1"));
    }

    // -----------------------------------------------------------------
    // Tier 1: FieldIndexInRange
    // -----------------------------------------------------------------

    fn add_struct_with_n_fields(p: &mut Program, sid: usize, n: usize) {
        let fields = (0..n)
            .map(|i| crate::ir::Field {
                name: format!("f{i}"),
                field_type: Type::UInt(64),
            })
            .collect();
        p.structs.insert(
            sid,
            crate::ir::Struct {
                module_id: 0,
                name: format!("S{sid}"),
                qualified_name: format!("S{sid}"),
                type_params: Vec::new(),
                fields,
                variants: None,
                is_native: false,
            },
        );
    }

    #[test]
    fn field_index_in_range_passes_on_valid_index() {
        let (mut p, _mid) = empty_module();
        add_struct_with_n_fields(&mut p, 0, 3);
        // f0 body: read p0.f1 (field_index 1 of 3-field struct -- valid)
        let mut body = just(unit());
        body.stmts.push(Stmt::Let {
            pattern: vec![Some("x".into())],
            value: Expr::Field {
                struct_id: 0,
                field_index: 1,
                base: Box::new(var("p0")),
            },
        });
        body.tail = crate::ir::BlockTail::Value(Expr::Var("x".into()));
        make_fn(
            &mut p,
            vec![Type::Struct {
                struct_id: 0,
                type_args: Vec::new(),
            }],
            body,
        );
        assert!(FieldIndexInRange.check(&p).is_ok());
    }

    #[test]
    fn field_index_in_range_catches_out_of_range_field() {
        let (mut p, _mid) = empty_module();
        add_struct_with_n_fields(&mut p, 0, 2);
        // Body reads p0.f5 -- out of range (only 2 fields)
        let mut body = just(unit());
        body.stmts.push(Stmt::Let {
            pattern: vec![Some("x".into())],
            value: Expr::Field {
                struct_id: 0,
                field_index: 5,
                base: Box::new(var("p0")),
            },
        });
        body.tail = crate::ir::BlockTail::Value(Expr::Var("x".into()));
        make_fn(
            &mut p,
            vec![Type::Struct {
                struct_id: 0,
                type_args: Vec::new(),
            }],
            body,
        );
        let errs = FieldIndexInRange.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert_eq!(errs[0].invariant, "field-index-in-range");
        assert!(errs[0].detail.contains("field_index 5 >= 2"));
    }

    // -----------------------------------------------------------------
    // Tier 1: VariantTagsResolveUniquely
    // -----------------------------------------------------------------

    fn add_enum_with_n_variants(p: &mut Program, sid: usize, n: usize) {
        let variants = (0..n)
            .map(|i| crate::ir::Variant {
                name: format!("V{i}"),
                tag: i,
                fields: Vec::new(),
            })
            .collect();
        p.structs.insert(
            sid,
            crate::ir::Struct {
                module_id: 0,
                name: format!("E{sid}"),
                qualified_name: format!("E{sid}"),
                type_params: Vec::new(),
                fields: Vec::new(),
                variants: Some(variants),
                is_native: false,
            },
        );
    }

    #[test]
    fn variant_tags_resolve_on_dense_tag() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 3);
        // Pack { variant: Some(2), .. } with 3-variant enum is valid.
        let body = just(Expr::Pack {
            struct_id: 0,
            type_args: Vec::new(),
            variant: Some(2),
            fields: Vec::new(),
        });
        make_fn(&mut p, vec![], body);
        assert!(VariantTagsResolveUniquely.check(&p).is_ok());
    }

    #[test]
    fn variant_tags_resolve_on_non_dense_tag() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 1);
        p.structs.get_mut(&0).unwrap().variants.as_mut().unwrap()[0].tag = 9;
        let body = just(Expr::Pack {
            struct_id: 0,
            type_args: Vec::new(),
            variant: Some(9),
            fields: Vec::new(),
        });
        make_fn(&mut p, vec![], body);

        assert!(VariantTagsResolveUniquely.check(&p).is_ok());
    }

    #[test]
    fn variant_tags_reject_unknown_pack_tag() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 2);
        // Pack with an unknown tag.
        let body = just(Expr::Pack {
            struct_id: 0,
            type_args: Vec::new(),
            variant: Some(5),
            fields: Vec::new(),
        });
        make_fn(&mut p, vec![], body);
        let errs = VariantTagsResolveUniquely.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0]
            .detail
            .contains("variant tag 5 does not resolve; known tags: [0, 1]"));
    }

    #[test]
    fn variant_tags_reject_unknown_variant_field_tag() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 1);
        let enum_type = Type::Struct {
            struct_id: 0,
            type_args: Vec::new(),
        };
        let body = just(Expr::Borrow {
            step: crate::ir::path::PathStep::VariantField {
                struct_id: 0,
                variant: 5,
                field_index: 0,
            },
            base: Box::new(var("p0")),
        });
        make_fn(&mut p, vec![enum_type], body);

        let errors = VariantTagsResolveUniquely.check(&p).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(errors[0].detail.contains("VariantField step"));
        assert!(errors[0].detail.contains("variant tag 5 does not resolve"));
    }

    #[test]
    fn variant_tags_reject_missing_enum_pack_tag() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 1);
        let body = just(Expr::Pack {
            struct_id: 0,
            type_args: Vec::new(),
            variant: None,
            fields: Vec::new(),
        });
        make_fn(&mut p, vec![], body);

        let errors = VariantTagsResolveUniquely.check(&p).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(errors[0].detail.contains("missing a variant tag"));
    }

    #[test]
    fn variant_tags_reject_duplicates() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 2);
        p.structs.get_mut(&0).unwrap().variants.as_mut().unwrap()[1].tag = 0;

        let errs = VariantTagsResolveUniquely.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("duplicate variant tag 0"));
    }

    #[test]
    fn variant_tags_reject_variant_on_plain_struct() {
        let (mut p, _mid) = empty_module();
        add_struct_with_n_fields(&mut p, 0, 2);
        // Plain struct (no variants) used with variant: Some(0) -- bug.
        let body = just(Expr::Pack {
            struct_id: 0,
            type_args: Vec::new(),
            variant: Some(0),
            fields: vec![unit(), unit()], // arity check elsewhere
        });
        make_fn(&mut p, vec![], body);
        let errs = VariantTagsResolveUniquely.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("no variants"));
    }

    // -----------------------------------------------------------------
    // Tier 1: StructFieldsXorVariants
    // -----------------------------------------------------------------

    #[test]
    fn struct_fields_xor_variants_passes_on_plain_struct() {
        let (mut p, _mid) = empty_module();
        add_struct_with_n_fields(&mut p, 0, 2);
        assert!(StructFieldsXorVariants.check(&p).is_ok());
    }

    #[test]
    fn struct_fields_xor_variants_passes_on_enum() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 3);
        assert!(StructFieldsXorVariants.check(&p).is_ok());
    }

    #[test]
    fn struct_fields_xor_variants_catches_both_set() {
        let (mut p, _mid) = empty_module();
        // Struct with BOTH non-empty fields AND Some(variants) is a bug.
        p.structs.insert(
            0,
            crate::ir::Struct {
                module_id: 0,
                name: "Broken".to_string(),
                qualified_name: "Broken".to_string(),
                type_params: Vec::new(),
                fields: vec![crate::ir::Field {
                    name: "f".to_string(),
                    field_type: Type::UInt(64),
                }],
                variants: Some(vec![crate::ir::Variant {
                    name: "V".to_string(),
                    tag: 0,
                    fields: Vec::new(),
                }]),
                is_native: false,
            },
        );
        let errs = StructFieldsXorVariants.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("non-empty fields"));
    }

    // -----------------------------------------------------------------
    // Tier 2: FunctionKindReferencesResolve
    // -----------------------------------------------------------------

    #[test]
    fn function_kind_references_resolve_passes_when_targets_exist() {
        let (mut p, _mid) = empty_module();
        // f0: target function
        make_fn(&mut p, vec![], just(unit()));
        // f1: Spec companion targeting f0 -- valid
        let fid = p.functions.len();
        p.functions.insert(
            fid,
            Function {
                module: 0,
                name: "f1".to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: Type::Unit,
                },
                body: just(unit()),
                kind: FunctionKind::Spec {
                    kind: crate::ir::SpecKind::Aborts,
                    target: 0,
                },
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
            },
        );
        assert!(FunctionKindReferencesResolve.check(&p).is_ok());
    }

    #[test]
    fn function_kind_references_resolve_catches_dangling_spec_target() {
        let (mut p, _mid) = empty_module();
        // f0: Spec companion targeting nonexistent FunId 99
        let fid = p.functions.len();
        p.functions.insert(
            fid,
            Function {
                module: 0,
                name: "f0".to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: Type::Unit,
                },
                body: just(unit()),
                kind: FunctionKind::Spec {
                    kind: crate::ir::SpecKind::Aborts,
                    target: 99,
                },
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
            },
        );
        let errs = FunctionKindReferencesResolve.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("Spec.target = 99"));
    }

    #[test]
    fn function_kind_references_resolve_catches_dangling_loop_parent() {
        let (mut p, _mid) = empty_module();
        let fid = p.functions.len();
        p.functions.insert(
            fid,
            Function {
                module: 0,
                name: "while_0".to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: Type::Unit,
                },
                body: just(unit()),
                kind: FunctionKind::LoopBody {
                    parent: 99,
                    slot: 0,
                },
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
            },
        );
        let errs = FunctionKindReferencesResolve.check(&p).unwrap_err();
        assert!(errs[0].detail.contains("LoopBody.parent = 99"));
    }

    // -----------------------------------------------------------------
    // Tier 2: BorrowEdgeHyperNonDegenerate
    // -----------------------------------------------------------------

    fn fn_with_writeback(p: &mut Program, edge: crate::ir::BorrowEdge) -> crate::ir::FunId {
        let id = p.functions.len();
        let mut body = just(unit());
        body.stmts.push(Stmt::Let {
            pattern: vec![Some("child".into())],
            value: lit_u64(0),
        });
        body.stmts.push(Stmt::Eval(Expr::WriteBack {
            node: crate::ir::BorrowNode::LocalRoot("x".into()),
            edge,
            child: "child".into(),
            world: None,
        }));
        p.functions.insert(
            id,
            Function {
                module: 0,
                name: format!("f{id}"),
                signature: Signature {
                    type_params: Vec::new(),
                    params: vec![Param {
                        name: "x".to_string(),
                        var: "x".into(),
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
    fn borrow_edge_hyper_non_degenerate_passes_on_two_inner() {
        let (mut p, _mid) = empty_module();
        fn_with_writeback(
            &mut p,
            crate::ir::BorrowEdge::Hyper(vec![
                crate::ir::BorrowEdge::Direct,
                crate::ir::BorrowEdge::VecIndex,
            ]),
        );
        assert!(BorrowEdgeHyperNonDegenerate.check(&p).is_ok());
    }

    #[test]
    fn borrow_edge_hyper_non_degenerate_catches_empty_hyper() {
        let (mut p, _mid) = empty_module();
        fn_with_writeback(&mut p, crate::ir::BorrowEdge::Hyper(Vec::new()));
        let errs = BorrowEdgeHyperNonDegenerate.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("Hyper has 0 inner edges"));
    }

    #[test]
    fn borrow_edge_hyper_non_degenerate_catches_singleton_hyper() {
        let (mut p, _mid) = empty_module();
        fn_with_writeback(
            &mut p,
            crate::ir::BorrowEdge::Hyper(vec![crate::ir::BorrowEdge::Direct]),
        );
        let errs = BorrowEdgeHyperNonDegenerate.check(&p).unwrap_err();
        assert!(errs[0].detail.contains("Hyper has 1 inner edges"));
    }

    // -----------------------------------------------------------------
    // Tier 2: MatchArmTagsCoverEnumExactly
    // -----------------------------------------------------------------

    #[test]
    fn match_arm_tags_reject_empty_cases() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 2);
        let body = just(Expr::Match {
            struct_id: 0,
            selector: Box::new(unit()),
            cases: Vec::new(),
        });
        make_fn(&mut p, vec![], body);
        let errs = MatchArmTagsCoverEnumExactly.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("missing [0, 1]"));
    }

    #[test]
    fn match_arm_tags_reject_incomplete_nonempty_cases() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 2);
        let body = just(Expr::Match {
            struct_id: 0,
            selector: Box::new(unit()),
            cases: vec![crate::ir::MatchArm {
                variant: 0,
                bindings: Vec::new(),
                body: Box::new(just(unit())),
            }],
        });
        make_fn(&mut p, vec![], body);
        let errors = MatchArmTagsCoverEnumExactly.check(&p).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(errors[0].detail.contains("missing [1]"));
    }

    #[test]
    fn match_arm_tags_reject_duplicate_cases() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 2);
        let body = just(Expr::Match {
            struct_id: 0,
            selector: Box::new(unit()),
            cases: vec![
                crate::ir::MatchArm {
                    variant: 0,
                    bindings: Vec::new(),
                    body: Box::new(just(unit())),
                },
                crate::ir::MatchArm {
                    variant: 0,
                    bindings: Vec::new(),
                    body: Box::new(just(unit())),
                },
            ],
        });
        make_fn(&mut p, vec![], body);

        let errors = MatchArmTagsCoverEnumExactly.check(&p).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(errors[0].detail.contains("missing [1]"));
        assert!(errors[0].detail.contains("duplicate [0]"));
    }

    #[test]
    fn match_arm_tags_accept_exact_sparse_coverage() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 2);
        let variants = p.structs.get_mut(&0).unwrap().variants.as_mut().unwrap();
        variants[0].tag = 3;
        variants[1].tag = 9;
        let body = just(Expr::Match {
            struct_id: 0,
            selector: Box::new(unit()),
            cases: vec![
                crate::ir::MatchArm {
                    variant: 9,
                    bindings: Vec::new(),
                    body: Box::new(just(unit())),
                },
                crate::ir::MatchArm {
                    variant: 3,
                    bindings: Vec::new(),
                    body: Box::new(just(unit())),
                },
            ],
        });
        make_fn(&mut p, vec![], body);

        assert!(MatchArmTagsCoverEnumExactly.check(&p).is_ok());
    }

    // -----------------------------------------------------------------
    // Tier 2: FunIdDisjointBetweenFunctionsAndNatives
    // -----------------------------------------------------------------

    #[test]
    fn funid_disjoint_passes_when_disjoint() {
        let (mut p, _mid) = empty_module();
        make_fn(&mut p, vec![], just(unit())); // fid 0 in functions
        p.natives.decls.insert(
            1,
            crate::ir::NativeDecl {
                module: 0,
                name: "native_fn".to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: Type::Unit,
                },
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
                is_framework: true,
                spec_target: None,
                user_native: None,
            },
        );
        assert!(FunIdDisjointBetweenFunctionsAndNatives.check(&p).is_ok());
    }

    #[test]
    fn funid_disjoint_catches_shared_fid() {
        let (mut p, _mid) = empty_module();
        make_fn(&mut p, vec![], just(unit())); // fid 0 in functions
        p.natives.decls.insert(
            0, // same FunId!
            crate::ir::NativeDecl {
                module: 0,
                name: "n".to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: Type::Unit,
                },
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
                is_framework: true,
                spec_target: None,
                user_native: None,
            },
        );
        let errs = FunIdDisjointBetweenFunctionsAndNatives
            .check(&p)
            .unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("appears in both"));
    }

    // -----------------------------------------------------------------
    // Tier 2: NativeDeclNameNonEmpty
    // -----------------------------------------------------------------

    #[test]
    fn native_decl_name_non_empty_passes_when_named() {
        let (mut p, _mid) = empty_module();
        p.natives.decls.insert(
            0,
            crate::ir::NativeDecl {
                module: 0,
                name: "ok".to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: Type::Unit,
                },
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
                is_framework: true,
                spec_target: None,
                user_native: None,
            },
        );
        assert!(NativeDeclNameNonEmpty.check(&p).is_ok());
    }

    #[test]
    fn native_decl_name_non_empty_catches_empty_string() {
        let (mut p, _mid) = empty_module();
        p.natives.decls.insert(
            0,
            crate::ir::NativeDecl {
                module: 0,
                name: String::new(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: Type::Unit,
                },
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
                is_framework: true,
                spec_target: None,
                user_native: None,
            },
        );
        let errs = NativeDeclNameNonEmpty.check(&p).unwrap_err();
        assert!(errs[0].detail.contains("empty name"));
    }

    // -----------------------------------------------------------------
    // Tier 2: NoDuplicateModuleNameWithinPackage
    // -----------------------------------------------------------------

    #[test]
    fn no_duplicate_module_name_passes_on_unique() {
        let mut p = Program::default();
        p.modules.insert(
            0,
            Module {
                name: "m1".to_string(),
                package_name: "pkg".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        p.modules.insert(
            1,
            Module {
                name: "m2".to_string(),
                package_name: "pkg".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        assert!(NoDuplicateModuleNameWithinPackage.check(&p).is_ok());
    }

    #[test]
    fn no_duplicate_module_name_catches_collision() {
        let mut p = Program::default();
        p.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "pkg".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        p.modules.insert(
            1,
            Module {
                name: "m".to_string(),
                package_name: "pkg".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        let errs = NoDuplicateModuleNameWithinPackage.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("has 2 ModIds"));
    }

    #[test]
    fn no_duplicate_module_name_allows_same_name_in_different_packages() {
        // `state` in Pyth vs `state` in Wormhole -- both legit.
        let mut p = Program::default();
        p.modules.insert(
            0,
            Module {
                name: "state".to_string(),
                package_name: "Pyth".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        p.modules.insert(
            1,
            Module {
                name: "state".to_string(),
                package_name: "Wormhole".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        assert!(NoDuplicateModuleNameWithinPackage.check(&p).is_ok());
    }

    // -----------------------------------------------------------------
    // Tier 3: IfWhileCondsAreBool
    // -----------------------------------------------------------------

    #[test]
    fn if_while_conds_are_bool_passes_on_bool_cond() {
        let (mut p, _mid) = empty_module();
        // f0 body: if (true) {} else {} where (true) is lit_bool
        let body = just(Expr::If {
            cond: Box::new(lit_bool(true)),
            then_branch: Box::new(just(unit())),
            else_branch: Box::new(just(unit())),
        });
        make_fn(&mut p, vec![], body);
        assert!(IfWhileCondsAreBool.check(&p).is_ok());
    }

    #[test]
    fn condition_value_compatibility_accepts_reference_until_render_form() {
        let (mut p, _mid) = empty_module();
        let body = just(Expr::If {
            cond: Box::new(var("p0")),
            then_branch: Box::new(just(unit())),
            else_branch: Box::new(just(unit())),
        });
        make_fn(&mut p, vec![Type::Reference(Box::new(Type::Bool))], body);
        assert!(IfWhileCondValuesAreBool.check(&p).is_ok());
        assert!(IfWhileCondsAreBool.check(&p).is_err());
        assert_eq!(IfWhileCondValuesAreBool.established_by(), Stage::Baseline);
        assert_eq!(IfWhileCondsAreBool.established_by(), Stage::Render);
    }

    #[test]
    fn if_while_conds_are_bool_catches_int_cond() {
        let (mut p, _mid) = empty_module();
        // cond is a u64 literal -- type-incorrect.
        let body = just(Expr::If {
            cond: Box::new(lit_u64(0)),
            then_branch: Box::new(just(unit())),
            else_branch: Box::new(just(unit())),
        });
        make_fn(&mut p, vec![], body);
        let errs = IfWhileCondsAreBool.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("type"));
        assert!(errs[0].detail.contains("expected Bool"));
    }

    // -----------------------------------------------------------------
    // Tier 3: BinOpOperandTypesAgree
    // -----------------------------------------------------------------

    #[test]
    fn binop_operand_types_agree_passes_on_matching() {
        use crate::ir::ops::BinOp;
        let (mut p, _mid) = empty_module();
        let body = just(Expr::BinOp {
            op: BinOp::Add,
            lhs: Box::new(lit_u64(1)),
            rhs: Box::new(lit_u64(2)),
        });
        make_fn(&mut p, vec![], body);
        assert!(BinOpOperandTypesAgree.check(&p).is_ok());
    }

    #[test]
    fn binop_value_compatibility_accepts_reference_until_render_form() {
        use crate::ir::ops::BinOp;
        let (mut p, _mid) = empty_module();
        let body = just(Expr::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(var("p0")),
            rhs: Box::new(var("p1")),
        });
        make_fn(
            &mut p,
            vec![Type::Reference(Box::new(Type::UInt(64))), Type::UInt(64)],
            body,
        );
        assert!(BinOpOperandValueTypesAgree.check(&p).is_ok());
        assert!(BinOpOperandTypesAgree.check(&p).is_err());
        assert_eq!(
            BinOpOperandValueTypesAgree.established_by(),
            Stage::Baseline
        );
        assert_eq!(BinOpOperandTypesAgree.established_by(), Stage::Render);
    }

    #[test]
    fn binop_render_form_rejects_two_matching_reference_operands() {
        use crate::ir::ops::BinOp;
        let (mut p, _mid) = empty_module();
        let body = just(Expr::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(var("p0")),
            rhs: Box::new(var("p1")),
        });
        make_fn(
            &mut p,
            vec![
                Type::Reference(Box::new(Type::UInt(64))),
                Type::Reference(Box::new(Type::UInt(64))),
            ],
            body,
        );
        assert!(BinOpOperandValueTypesAgree.check(&p).is_ok());
        assert!(BinOpOperandTypesAgree.check(&p).is_err());
    }

    #[test]
    fn binop_operand_types_agree_catches_width_mismatch() {
        use crate::ir::ops::BinOp;
        let (mut p, _mid) = empty_module();
        // lit_u8 vs lit_u64 -- different widths.
        let body = just(Expr::BinOp {
            op: BinOp::Add,
            lhs: Box::new(lit_u8(1)),
            rhs: Box::new(lit_u64(2)),
        });
        make_fn(&mut p, vec![], body);
        let errs = BinOpOperandTypesAgree.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("UInt(8)"));
        assert!(errs[0].detail.contains("UInt(64)"));
    }

    #[test]
    fn binop_operand_types_agree_allows_shift_width_mismatch() {
        use crate::ir::ops::BinOp;
        let (mut p, _mid) = empty_module();
        // u64 << u8 is legal (shift amount can differ from operand).
        let body = just(Expr::BinOp {
            op: BinOp::Shl,
            lhs: Box::new(lit_u64(1)),
            rhs: Box::new(lit_u8(3)),
        });
        make_fn(&mut p, vec![], body);
        assert!(BinOpOperandTypesAgree.check(&p).is_ok());
    }

    // -----------------------------------------------------------------
    // Tier 3: PackFieldTypesMatchStructDefinition
    // -----------------------------------------------------------------

    #[test]
    fn pack_field_types_match_passes_on_correct_types() {
        let (mut p, _mid) = empty_module();
        add_struct_with_n_fields(&mut p, 0, 2); // 2 u64 fields per add_struct_with_n_fields helper
        let body = just(Expr::Pack {
            struct_id: 0,
            type_args: Vec::new(),
            variant: None,
            fields: vec![lit_u64(1), lit_u64(2)],
        });
        make_fn(&mut p, vec![], body);
        assert!(PackFieldTypesMatchStructDefinition.check(&p).is_ok());
    }

    #[test]
    fn pack_field_types_ignore_mutable_ref_root_provenance() {
        let (mut p, _mid) = empty_module();
        add_struct_with_n_fields(&mut p, 0, 1);
        let value_type = Type::Tuple(vec![
            Type::MutableRef {
                inner: Box::new(Type::UInt(64)),
                root: Box::new(Type::Bool),
            },
            Type::MutableRef {
                inner: Box::new(Type::Bool),
                root: Box::new(Type::Bool),
            },
        ]);
        p.structs.get_mut(&0).unwrap().fields[0].field_type = Type::Tuple(vec![
            Type::MutableRef {
                inner: Box::new(Type::UInt(64)),
                root: Box::new(Type::UInt(64)),
            },
            Type::MutableRef {
                inner: Box::new(Type::Bool),
                root: Box::new(Type::Bool),
            },
        ]);
        let body = just(Expr::Pack {
            struct_id: 0,
            type_args: Vec::new(),
            variant: None,
            fields: vec![var("p0")],
        });
        make_fn(&mut p, vec![value_type], body);

        assert!(PackFieldValueTypesMatchStructDefinition.check(&p).is_ok());
        assert!(PackFieldTypesMatchStructDefinition.check(&p).is_ok());
    }

    #[test]
    fn pack_field_types_still_reject_different_mutable_ref_inner_type() {
        let (mut p, _mid) = empty_module();
        add_struct_with_n_fields(&mut p, 0, 1);
        p.structs.get_mut(&0).unwrap().fields[0].field_type = Type::MutableRef {
            inner: Box::new(Type::UInt(64)),
            root: Box::new(Type::UInt(64)),
        };
        let body = just(Expr::Pack {
            struct_id: 0,
            type_args: Vec::new(),
            variant: None,
            fields: vec![var("p0")],
        });
        make_fn(
            &mut p,
            vec![Type::MutableRef {
                inner: Box::new(Type::Bool),
                root: Box::new(Type::UInt(64)),
            }],
            body,
        );

        assert!(PackFieldValueTypesMatchStructDefinition.check(&p).is_err());
        assert!(PackFieldTypesMatchStructDefinition.check(&p).is_err());
    }

    #[test]
    fn mutable_ref_root_erasure_recurses_through_value_type_containers() {
        let actual_ref = Type::MutableRef {
            inner: Box::new(Type::UInt(64)),
            root: Box::new(Type::Bool),
        };
        let expected_ref = Type::MutableRef {
            inner: Box::new(Type::UInt(64)),
            root: Box::new(Type::UInt(8)),
        };
        let actual = Type::Struct {
            struct_id: 7,
            type_args: vec![Type::Vector(Box::new(Type::Reference(Box::new(
                actual_ref,
            ))))],
        };
        let expected = Type::Struct {
            struct_id: 7,
            type_args: vec![Type::Vector(Box::new(Type::Reference(Box::new(
                expected_ref,
            ))))],
        };

        assert!(same_value_type_ignoring_mutable_roots(&actual, &expected));
        assert!(!same_value_type_ignoring_mutable_roots(
            &actual,
            &Type::Struct {
                struct_id: 8,
                type_args: vec![expected],
            }
        ));
    }

    #[test]
    fn pack_value_compatibility_accepts_reference_until_render_form() {
        let (mut p, _mid) = empty_module();
        add_struct_with_n_fields(&mut p, 0, 1);
        let body = just(Expr::Pack {
            struct_id: 0,
            type_args: Vec::new(),
            variant: None,
            fields: vec![var("p0")],
        });
        make_fn(
            &mut p,
            vec![Type::Reference(Box::new(Type::UInt(64)))],
            body,
        );
        assert!(PackFieldValueTypesMatchStructDefinition.check(&p).is_ok());
        assert!(PackFieldTypesMatchStructDefinition.check(&p).is_err());
        assert_eq!(
            PackFieldValueTypesMatchStructDefinition.established_by(),
            Stage::Baseline
        );
        assert_eq!(
            PackFieldTypesMatchStructDefinition.established_by(),
            Stage::Render
        );
    }

    #[test]
    fn pack_value_compatibility_preserves_declared_reference_fields() {
        let (mut p, _mid) = empty_module();
        add_struct_with_n_fields(&mut p, 0, 1);
        p.structs.get_mut(&0).unwrap().fields[0].field_type =
            Type::Reference(Box::new(Type::UInt(64)));
        let body = just(Expr::Pack {
            struct_id: 0,
            type_args: Vec::new(),
            variant: None,
            fields: vec![var("p0")],
        });
        make_fn(
            &mut p,
            vec![Type::Reference(Box::new(Type::UInt(64)))],
            body,
        );
        assert!(PackFieldValueTypesMatchStructDefinition.check(&p).is_ok());
        assert!(PackFieldTypesMatchStructDefinition.check(&p).is_ok());
    }

    #[test]
    fn pack_field_types_match_catches_wrong_type_at_slot() {
        let (mut p, _mid) = empty_module();
        add_struct_with_n_fields(&mut p, 0, 2); // both fields are UInt(64)
                                                // Pass lit_u8 in slot 0 -- wrong width.
        let body = just(Expr::Pack {
            struct_id: 0,
            type_args: Vec::new(),
            variant: None,
            fields: vec![lit_u8(1), lit_u64(2)],
        });
        make_fn(&mut p, vec![], body);
        let errs = PackFieldTypesMatchStructDefinition.check(&p).unwrap_err();
        assert_eq!(errs.len(), 1);
        assert!(errs[0].detail.contains("expected UInt(64), got UInt(8)"));
    }

    #[test]
    fn rendered_branch_value_types_reject_incompatible_if_arms() {
        let (mut p, _mid) = empty_module();
        let body = just(Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(just(Expr::Tuple(vec![
                lit_u64(1),
                Expr::Const(crate::ir::Const::Bool(true)),
            ]))),
            else_branch: Box::new(just(lit_u64(2))),
        });
        make_fn(&mut p, Vec::new(), body);

        let errors = RenderedBranchValueTypesCompatible.check(&p).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(errors[0]
            .detail
            .contains("If value arms emit incompatible types"));
    }

    #[test]
    fn rendered_branch_value_types_reject_incompatible_match_arms() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 2);
        let enum_type = Type::Struct {
            struct_id: 0,
            type_args: Vec::new(),
        };
        let body = just(Expr::Match {
            struct_id: 0,
            selector: Box::new(var("p0")),
            cases: vec![
                crate::ir::MatchArm {
                    variant: 0,
                    bindings: Vec::new(),
                    body: Box::new(just(Expr::Tuple(vec![
                        lit_u64(1),
                        Expr::Const(crate::ir::Const::Bool(true)),
                    ]))),
                },
                crate::ir::MatchArm {
                    variant: 1,
                    bindings: Vec::new(),
                    body: Box::new(just(lit_u64(2))),
                },
            ],
        });
        make_fn(&mut p, vec![enum_type], body);

        let errors = RenderedBranchValueTypesCompatible.check(&p).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(errors[0]
            .detail
            .contains("Match value arms emit incompatible types"));
    }

    #[test]
    fn rendered_branch_value_types_allow_per_slot_mutation_coercion() {
        let (mut p, _mid) = empty_module();
        let mutation = Type::MutableRef {
            inner: Box::new(Type::UInt(64)),
            root: Box::new(Type::UInt(64)),
        };
        let body = just(Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(just(Expr::Tuple(vec![
                var("p0"),
                Expr::Const(crate::ir::Const::Bool(true)),
            ]))),
            else_branch: Box::new(just(Expr::Tuple(vec![
                var("p1"),
                Expr::Const(crate::ir::Const::Bool(false)),
            ]))),
        });
        make_fn(&mut p, vec![mutation, Type::UInt(64)], body);

        assert!(RenderedBranchValueTypesCompatible.check(&p).is_ok());
    }

    #[test]
    fn rendered_branch_value_types_ignore_eval_branch_results() {
        let (mut p, _mid) = empty_module();
        let mut body = just(Expr::Unit);
        body.stmts.push(Stmt::Eval(Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(just(lit_u64(1))),
            else_branch: Box::new(just(Expr::Unit)),
        }));
        make_fn(&mut p, Vec::new(), body);

        assert!(RenderedBranchValueTypesCompatible.check(&p).is_ok());
    }

    #[test]
    fn rendered_branch_value_types_reject_unknown_value_arm() {
        let (mut p, _mid) = empty_module();
        let body = just(Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(just(lit_u64(1))),
            else_branch: Box::new(just(Expr::ToBool(Box::new(Expr::Const(
                crate::ir::Const::Bool(false),
            ))))),
        });
        make_fn(&mut p, Vec::new(), body);

        let errors = RenderedBranchValueTypesCompatible.check(&p).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(errors[0].detail.contains("emitted type is unknown"));
    }

    #[test]
    fn rendered_branch_value_types_allow_scalar_match_coercion() {
        let (mut p, _mid) = empty_module();
        add_enum_with_n_variants(&mut p, 0, 2);
        let enum_type = Type::Struct {
            struct_id: 0,
            type_args: Vec::new(),
        };
        let mutation = Type::MutableRef {
            inner: Box::new(Type::UInt(64)),
            root: Box::new(Type::UInt(64)),
        };
        let body = just(Expr::Match {
            struct_id: 0,
            selector: Box::new(var("p0")),
            cases: vec![
                crate::ir::MatchArm {
                    variant: 0,
                    bindings: Vec::new(),
                    body: Box::new(just(var("p1"))),
                },
                crate::ir::MatchArm {
                    variant: 1,
                    bindings: Vec::new(),
                    body: Box::new(just(var("p2"))),
                },
            ],
        });
        make_fn(&mut p, vec![enum_type, mutation, Type::UInt(64)], body);

        assert!(RenderedBranchValueTypesCompatible.check(&p).is_ok());
    }

    #[test]
    fn rendered_branch_value_types_reject_tuple_var_slot_coercion() {
        let (mut p, _mid) = empty_module();
        let mutation = Type::MutableRef {
            inner: Box::new(Type::UInt(64)),
            root: Box::new(Type::UInt(64)),
        };
        let body = just(Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(just(var("p0"))),
            else_branch: Box::new(just(var("p1"))),
        });
        make_fn(
            &mut p,
            vec![
                Type::Tuple(vec![mutation, Type::Bool]),
                Type::Tuple(vec![Type::UInt(64), Type::Bool]),
            ],
            body,
        );

        let errors = RenderedBranchValueTypesCompatible.check(&p).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(errors[0]
            .detail
            .contains("coercion the renderer cannot emit"));
    }

    #[test]
    fn rendered_branch_value_types_use_native_call_effective_bindings() {
        let (mut p, _mid) = empty_module();
        let mutation = Type::MutableRef {
            inner: Box::new(Type::UInt(64)),
            root: Box::new(Type::UInt(64)),
        };
        let native_return = Type::Tuple(vec![mutation.clone(), Type::Bool]);
        let native_id = 99;
        p.natives.decls.insert(
            native_id,
            crate::ir::NativeDecl {
                module: 0,
                name: "native_pair".to_string(),
                signature: Signature {
                    type_params: Vec::new(),
                    params: Vec::new(),
                    return_type: native_return.clone(),
                },
                effects: crate::ir::Effects::PURE,
                explicit_pure: false,
                is_framework: true,
                spec_target: None,
                user_native: None,
            },
        );
        let mut body = just(Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(just(var("native_result"))),
            else_branch: Box::new(just(var("p0"))),
        });
        body.stmts.push(Stmt::Let {
            pattern: vec![Some("native_result".into())],
            value: Expr::Call {
                fun: native_id,
                type_args: Vec::new(),
                args: Vec::new(),
            },
        });
        make_fn(&mut p, vec![native_return], body);

        let errors = RenderedBranchValueTypesCompatible.check(&p).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(errors[0]
            .detail
            .contains("coercion the renderer cannot emit"));
    }

    #[test]
    fn rendered_branch_value_types_propagate_nested_terminal_arms() {
        let (mut p, _mid) = empty_module();
        let abort = || Block {
            stmts: Vec::new(),
            tail: BlockTail::Abort {
                code: Box::new(lit_u64(7)),
            },
        };
        let body = just(Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(just(Expr::If {
                cond: Box::new(Expr::Const(crate::ir::Const::Bool(false))),
                then_branch: Box::new(abort()),
                else_branch: Box::new(abort()),
            })),
            else_branch: Box::new(just(lit_u64(1))),
        });
        make_fn(&mut p, Vec::new(), body);

        assert!(RenderedBranchValueTypesCompatible.check(&p).is_ok());
    }

    #[test]
    fn rendered_branch_value_types_ignore_unrendered_abort_code() {
        let (mut p, _mid) = empty_module();
        let body = Block {
            stmts: Vec::new(),
            tail: BlockTail::Abort {
                code: Box::new(Expr::If {
                    cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
                    then_branch: Box::new(just(lit_u64(1))),
                    else_branch: Box::new(just(Expr::Unit)),
                }),
            },
        };
        make_fn(&mut p, Vec::new(), body);

        assert!(RenderedBranchValueTypesCompatible.check(&p).is_ok());
    }

    #[test]
    fn rendered_branch_value_types_ignore_erased_inner_statements() {
        let (mut p, _mid) = empty_module();
        let incompatible = || Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(just(lit_u64(1))),
            else_branch: Box::new(just(Expr::Unit)),
        };
        let inner = Block {
            stmts: vec![
                Stmt::Eval(Expr::Tuple(vec![incompatible()])),
                Stmt::Let {
                    pattern: vec![None],
                    value: Expr::Tuple(vec![incompatible()]),
                },
            ],
            tail: BlockTail::Value(lit_u64(2)),
        };
        let body = just(Expr::If {
            cond: Box::new(Expr::Const(crate::ir::Const::Bool(true))),
            then_branch: Box::new(inner),
            else_branch: Box::new(just(lit_u64(3))),
        });
        make_fn(&mut p, Vec::new(), body);

        assert!(RenderedBranchValueTypesCompatible.check(&p).is_ok());
    }

    // -----------------------------------------------------------------
    // Tier 3: IrTypeInferenceSucceeds (umbrella)
    // -----------------------------------------------------------------

    #[test]
    fn ir_type_inference_succeeds_passes_on_clean_program() {
        let (mut p, _mid) = empty_module();
        make_fn(&mut p, vec![], just(lit_u64(0)));
        assert!(IrTypeInferenceSucceeds.check(&p).is_ok());
    }

    #[test]
    fn ir_type_inference_succeeds_catches_field_out_of_range() {
        let (mut p, _mid) = empty_module();
        add_struct_with_n_fields(&mut p, 0, 2);
        // Make a function whose body does a Pack and then a Field(5)
        let mut body = just(unit());
        body.stmts.push(Stmt::Let {
            pattern: vec![Some("s".into())],
            value: Expr::Pack {
                struct_id: 0,
                type_args: Vec::new(),
                variant: None,
                fields: vec![lit_u64(1), lit_u64(2)],
            },
        });
        body.tail = crate::ir::BlockTail::Value(Expr::Field {
            struct_id: 0,
            field_index: 5, // out of range for a 2-field struct
            base: Box::new(var("s")),
        });
        make_fn(&mut p, vec![], body);
        let errs = IrTypeInferenceSucceeds.check(&p).unwrap_err();
        // FieldOutOfRange in type_of.
        assert!(errs.iter().any(|e| e.detail.contains("FieldOutOfRange")));
    }

    #[test]
    fn ir_type_inference_succeeds_catches_unbound_var() {
        let (mut p, _mid) = empty_module();
        make_fn(&mut p, vec![], just(var("missing")));
        let errs = IrTypeInferenceSucceeds.check(&p).unwrap_err();
        assert!(errs
            .iter()
            .any(|e| e.detail.contains("UnboundVar") && e.detail.contains("missing")));
    }

    #[test]
    fn ir_type_inference_succeeds_catches_unknown_function() {
        let (mut p, _mid) = empty_module();
        make_fn(&mut p, vec![], just(call(999, vec![])));
        let errs = IrTypeInferenceSucceeds.check(&p).unwrap_err();
        assert!(errs
            .iter()
            .any(|e| e.detail.contains("UnknownFunction(999)")));
    }

    #[test]
    fn ir_type_inference_succeeds_catches_unknown_struct() {
        let (mut p, _mid) = empty_module();
        let missing_struct = Type::Struct {
            struct_id: 999,
            type_args: vec![],
        };
        let body = just(Expr::Field {
            struct_id: 999,
            field_index: 0,
            base: Box::new(var("p0")),
        });
        make_fn(&mut p, vec![missing_struct], body);
        let errs = IrTypeInferenceSucceeds.check(&p).unwrap_err();
        assert!(errs.iter().any(|e| e.detail.contains("UnknownStruct(999)")));
    }

    #[test]
    fn ir_type_inference_succeeds_reports_typed_binder_failure() {
        let (mut p, _mid) = empty_module();
        let body = block(
            vec![Stmt::Let {
                pattern: vec![Some("a".into()), Some("b".into())],
                value: lit_u64(0),
            }],
            tail_value(unit()),
        );
        make_fn(&mut p, vec![], body);
        let errs = IrTypeInferenceSucceeds.check(&p).unwrap_err();
        assert!(errs.iter().any(|e| {
            e.detail.contains("MalformedAccess")
                && e.detail.contains("multi-pattern Let expects Tuple")
        }));
    }

    #[test]
    fn verify_at_render_runs_baseline_invariants() {
        // Smoke test: violating BaselineWellFormedness shows up via
        // the registry's verify_at at Render-time.
        use crate::ir::invariants::verify_at;
        let (mut p, _mid) = empty_module();
        make_fn(&mut p, vec![], just(var("missing")));
        let res = verify_at(Stage::Render, &p);
        assert!(res.is_err());
        let violations = res.unwrap_err();
        assert!(violations
            .iter()
            .any(|v| v.invariant == "baseline-well-formedness"));
    }
}
