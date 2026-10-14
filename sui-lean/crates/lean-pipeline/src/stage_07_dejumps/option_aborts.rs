//! Synthetic native structs for the `.aborts` variant's return type.
//!
//! Stage 7 (rewrite) materialises `.aborts` companions returning
//! `Option<MoveAbortCode>`. Neither type exists in the new pipeline's
//! IR by default; this module registers both as synthetic native
//! structs (same pattern as `stage_04_effects::world::ensure_world_struct`).
//!
//! Once registered, both types flow through every existing IR walker
//! (`type_of`, `free_vars`, validator, etc.) as ordinary
//! `Type::Struct { struct_id, type_args }` references — no IR walker
//! updates are needed.
//!
//! ## `MoveAbortCode`
//!
//! Plain struct, one field: `code : u64`. Renderer maps the
//! qualified name `Prover::abort_code::MoveAbortCode` to Lean's
//! `Prelude.MoveAbort.MoveAbort` (the existing `{ source, code }`
//! struct in `lemmas/Prelude/MoveAbort.lean`). Slice 1 ignores the
//! `source` field at the IR level — every constructed
//! `MoveAbortCode` carries just the u64 `code`; the renderer fills
//! in `source := MoveAbort.AbortSource.userAssert` as a placeholder.
//!
//! ## `Option<T>`
//!
//! Enum with two variants: `None` (no fields) and `Some` (one field
//! `value : T`). Renderer maps the qualified name
//! `Prover::option::Option` to Lean's built-in `Option`.
//!
//! ## Idempotency
//!
//! `ensure_aborts_types(program)` returns existing struct ids on
//! second invocation, never duplicating.

use crate::ir::expr::Expr;
use crate::ir::ty::Const;
use crate::ir::{
    AbortPayloadMode, Field, ModId, Module, ObservedErrorKind, Program, Struct, StructId, Type,
    Variant,
};

/// Qualified name of the synthetic `MoveAbortCode` struct.
/// Lives in `Prover::abort` to avoid name clashes with any user module
/// named `abort_code` and to give the renderer a non-keyword Lean
/// namespace.
pub const ABORT_CODE_QUALIFIED_NAME: &str = "Prover::abort::AbortCode";
pub const ABORT_CODE_PACKAGE_NAME: &str = "Prover";
pub const ABORT_CODE_MODULE_NAME: &str = "abort";

/// Qualified name of the synthetic abort-result wrapper. Semantically
/// `Option<AbortCode>`, but named `AbortResult` to avoid clashing
/// with `MoveStdlib::option::Option` (which also mangles to
/// `MoveOption.MoveOption` at the Lean level, producing duplicate-
/// definition errors when both are imported into the same scope).
pub const OPTION_QUALIFIED_NAME: &str = "Prover::abort::AbortResult";
pub const OPTION_PACKAGE_NAME: &str = "Prover";
pub const OPTION_MODULE_NAME: &str = "abort";

pub const RETURN_FLOW_QUALIFIED_NAME: &str = "Prover::abort::ReturnFlow";
pub const RETURN_FLOW_CONTINUE_TAG: usize = 0;
pub const RETURN_FLOW_RETURNED_TAG: usize = 1;

pub fn ensure_return_flow_struct(program: &mut Program) -> StructId {
    if let Some(id) = program.struct_id_by_qualified_name(RETURN_FLOW_QUALIFIED_NAME) {
        return id;
    }
    let module_id = ensure_module(program, OPTION_PACKAGE_NAME, OPTION_MODULE_NAME);
    let struct_id = program.next_struct_id();
    program.structs.insert(
        struct_id,
        Struct {
            module_id,
            name: "ReturnFlow".to_string(),
            qualified_name: RETURN_FLOW_QUALIFIED_NAME.to_string(),
            type_params: vec!["T".to_string(), "R".to_string()],
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "continue".into(),
                    tag: RETURN_FLOW_CONTINUE_TAG,
                    fields: vec![Field {
                        name: "value".into(),
                        field_type: Type::TypeParam(0),
                    }],
                },
                Variant {
                    name: "returned".into(),
                    tag: RETURN_FLOW_RETURNED_TAG,
                    fields: vec![Field {
                        name: "value".into(),
                        field_type: Type::TypeParam(1),
                    }],
                },
            ]),
            is_native: false,
        },
    );
    struct_id
}

pub fn is_abort_result_type(ty: &Type, option_id: StructId, abort_code_id: StructId) -> bool {
    matches!(
        ty,
        Type::Struct { struct_id, type_args }
            if *struct_id == option_id
                && matches!(
                    type_args.as_slice(),
                    [Type::Struct { struct_id, type_args }]
                        if *struct_id == abort_code_id && type_args.is_empty()
                )
    )
}

/// Tag of the `NoAbort` variant.
pub const OPTION_NONE_TAG: usize = 0;
/// Tag of the `Aborted(code)` variant.
pub const OPTION_SOME_TAG: usize = 1;

/// Synthetic abort code used for `prover::asserts(p)` injections.
/// The actual u64 value is opaque -- the prover only cares about
/// `Some` vs `None`.
const ASSERT_ABORT_CODE: u64 = 0;

/// Identifiers for the two synthetic structs. Returned by
/// `ensure_aborts_types` and reused at every constructor / Match
/// site in phase 1's walker.
#[derive(Debug, Clone, Copy)]
pub struct AbortsTypeIds {
    pub abort_code: StructId,
    pub option: StructId,
    pub payload_mode: AbortPayloadMode,
    pub origin_tag: u64,
}

impl AbortsTypeIds {
    /// `Type::Struct` for `MoveAbortCode`.
    pub fn abort_code_type(&self) -> Type {
        Type::Struct {
            struct_id: self.abort_code,
            type_args: Vec::new(),
        }
    }

    /// `Type::Struct` for `Option<T>` instantiated with `T`.
    pub fn option_type(&self, inner: Type) -> Type {
        Type::Struct {
            struct_id: self.option,
            type_args: vec![inner],
        }
    }

    /// `Type::Struct` for `Option<MoveAbortCode>` — the canonical
    /// `.aborts` return type.
    pub fn option_abort_code_type(&self) -> Type {
        self.option_type(self.abort_code_type())
    }

    /// Build `None : Option<MoveAbortCode>`.
    pub fn make_none(&self) -> Expr {
        Expr::Pack {
            struct_id: self.option,
            type_args: vec![self.abort_code_type()],
            variant: Some(OPTION_NONE_TAG),
            fields: Vec::new(),
        }
    }

    /// Build `Some(<code>) : Option<MoveAbortCode>` from a `code: u64`
    /// expression.
    pub fn make_some(&self, code: Expr) -> Expr {
        self.make_some_at(code, self.origin_tag)
    }

    pub fn make_some_at(&self, code: Expr, origin_tag: u64) -> Expr {
        self.make_error_at(code, origin_tag, ObservedErrorKind::Abort)
    }

    pub fn make_error_at(
        &self,
        code: Expr,
        origin_tag: u64,
        error_kind: ObservedErrorKind,
    ) -> Expr {
        // Wrap the raw u64 in a `MoveAbortCode { code }` first, then in
        // `Some(...)`.
        let mut fields = vec![code];
        if self.payload_mode == AbortPayloadMode::ObservedTest {
            fields.push(Expr::Const(Const::UInt {
                bits: 64,
                value: ethnum::U256::from(origin_tag),
            }));
            fields.push(Expr::Const(Const::UInt {
                bits: 64,
                value: ethnum::U256::from(error_kind.tag()),
            }));
        }
        let abort_code_value = Expr::Pack {
            struct_id: self.abort_code,
            type_args: Vec::new(),
            variant: None,
            fields,
        };
        Expr::Pack {
            struct_id: self.option,
            type_args: vec![self.abort_code_type()],
            variant: Some(OPTION_SOME_TAG),
            fields: vec![abort_code_value],
        }
    }

    /// Build `Some(MoveAbortCode { code: <ASSERT_ABORT_CODE> })`. Used
    /// to construct the early-exit value injected by `prover::asserts`
    /// guards.
    pub fn assert_abort_some(&self) -> Expr {
        self.assert_abort_some_at(self.origin_tag)
    }

    pub fn assert_abort_some_at(&self, origin_tag: u64) -> Expr {
        use ethnum::U256;
        self.make_some_at(
            Expr::Const(Const::UInt {
                bits: 64,
                value: U256::from(ASSERT_ABORT_CODE),
            }),
            origin_tag,
        )
    }

    pub fn with_origin_tag(self, origin_tag: u64) -> Self {
        Self { origin_tag, ..self }
    }
}

/// Get-or-register the synthetic `MoveAbortCode` and `Option<T>`
/// structs. Idempotent: a second call on a `Program` that already
/// has the structs returns the same `StructId`s.
pub fn ensure_aborts_types(program: &mut Program) -> AbortsTypeIds {
    let payload_mode = program.abort_provenance.mode;
    ensure_aborts_types_with_mode(program, payload_mode)
}

pub fn ensure_aborts_types_with_mode(
    program: &mut Program,
    payload_mode: AbortPayloadMode,
) -> AbortsTypeIds {
    AbortsTypeIds {
        abort_code: ensure_abort_code_struct(program, payload_mode),
        option: ensure_option_struct(program),
        payload_mode,
        origin_tag: 0,
    }
}

fn ensure_abort_code_struct(program: &mut Program, payload_mode: AbortPayloadMode) -> StructId {
    if let Some(id) = program.struct_id_by_qualified_name(ABORT_CODE_QUALIFIED_NAME) {
        let fields = abort_code_fields(payload_mode);
        let mode_changed = program
            .structs
            .get(&id)
            .is_some_and(|abort_code| abort_code.fields != fields);
        if mode_changed {
            if let Some(abort_code) = program.structs.get_mut(&id) {
                abort_code.fields = fields;
            }
            normalize_abort_code_packs(program, id, payload_mode);
        }
        return id;
    }
    let module_id = ensure_module(program, ABORT_CODE_PACKAGE_NAME, ABORT_CODE_MODULE_NAME);
    let struct_id = program.next_struct_id();
    program.structs.insert(
        struct_id,
        Struct {
            module_id,
            name: "AbortCode".to_string(),
            qualified_name: ABORT_CODE_QUALIFIED_NAME.to_string(),
            type_params: Vec::new(),
            fields: abort_code_fields(payload_mode),
            variants: None,
            // is_native: false — let the renderer emit the actual
            // structure definition. Trivial wrapper around a u64.
            is_native: false,
        },
    );
    struct_id
}

fn abort_code_fields(payload_mode: AbortPayloadMode) -> Vec<Field> {
    vec![Field {
        name: "code".into(),
        field_type: Type::UInt(64),
    }]
    .into_iter()
    .chain(
        (payload_mode == AbortPayloadMode::ObservedTest).then_some(Field {
            name: "origin_tag".into(),
            field_type: Type::UInt(64),
        }),
    )
    .chain(
        (payload_mode == AbortPayloadMode::ObservedTest).then_some(Field {
            name: "error_kind".into(),
            field_type: Type::UInt(64),
        }),
    )
    .collect()
}

fn normalize_abort_code_packs(
    program: &mut Program,
    abort_code: StructId,
    payload_mode: AbortPayloadMode,
) {
    struct Normalizer {
        abort_code: StructId,
        payload_mode: AbortPayloadMode,
    }

    impl crate::ir::visit::MutVisitor for Normalizer {
        fn visit_expr_mut(&mut self, expr: &mut Expr) {
            if let Expr::Pack {
                struct_id,
                variant: None,
                fields,
                ..
            } = expr
            {
                if *struct_id == self.abort_code {
                    match self.payload_mode {
                        AbortPayloadMode::Proof => fields.truncate(1),
                        AbortPayloadMode::ObservedTest => {
                            fields.truncate(3);
                            if fields.len() == 1 {
                                fields.push(Expr::Const(Const::UInt {
                                    bits: 64,
                                    value: ethnum::U256::from(crate::ir::UNKNOWN_ABORT_ORIGIN_TAG),
                                }));
                            }
                            if fields.len() == 2 {
                                fields.push(Expr::Const(Const::UInt {
                                    bits: 64,
                                    value: ethnum::U256::from(ObservedErrorKind::Unknown.tag()),
                                }));
                            }
                        }
                    }
                }
            }
            crate::ir::visit::walk_expr_mut_default(self, expr);
        }
    }

    let mut normalizer = Normalizer {
        abort_code,
        payload_mode,
    };
    program.for_each_body_mut(|_, body| {
        crate::ir::visit::MutVisitor::visit_block_mut(&mut normalizer, body)
    });
}

fn ensure_option_struct(program: &mut Program) -> StructId {
    if let Some(id) = program.struct_id_by_qualified_name(OPTION_QUALIFIED_NAME) {
        return id;
    }
    let module_id = ensure_module(program, OPTION_PACKAGE_NAME, OPTION_MODULE_NAME);
    let struct_id = program.next_struct_id();
    program.structs.insert(
        struct_id,
        Struct {
            module_id,
            name: "AbortResult".to_string(),
            qualified_name: OPTION_QUALIFIED_NAME.to_string(),
            type_params: vec!["T".to_string()],
            fields: Vec::new(),
            variants: Some(vec![
                Variant {
                    name: "NoAbort".into(),
                    tag: OPTION_NONE_TAG,
                    fields: Vec::new(),
                },
                Variant {
                    name: "Aborted".into(),
                    tag: OPTION_SOME_TAG,
                    fields: vec![Field {
                        name: "code".into(),
                        // Inside the struct definition we refer to the
                        // type parameter `T` (index 0). At each usage
                        // site (Pack / Match), the type_args supply
                        // the concrete instantiation; `type_of`'s
                        // substitution machinery handles the rest.
                        field_type: Type::TypeParam(0),
                    }],
                },
            ]),
            // is_native: false — let the renderer emit the actual
            // enum definition. The shape matches Lean's built-in
            // `Option` exactly (one constructor with no fields,
            // one with one type-parameterised field).
            is_native: false,
        },
    );
    struct_id
}

fn ensure_module(program: &mut Program, package: &str, name: &str) -> ModId {
    if let Some(id) = program.module_id_by_name(package, name) {
        return id;
    }
    let module_id = program.next_module_id();
    program.modules.insert(
        module_id,
        Module {
            name: name.to_string(),
            package_name: package.to_string(),
            address: String::new(),
            required_imports: Vec::new(),
            is_native: true,
        },
    );
    module_id
}
