//! Renderer support for the typed `World` prelude.
//!
//! Per-package AnyEvent / AnyObject generation and the helpers
//! needed to lower `Type::Struct(world_id)` references and effectful
//! Calls to `Prover.World.*` calls. See
//! `plans/lean-pipeline/stage-04-effects.md` and the sibling
//! `mutation` module.

use std::collections::BTreeSet;

use crate::ir::{
    visit::{walk_block_default, walk_expr_default, Visitor},
    Block, Expr, Program, Type,
};

/// One `AnyEvent` or `AnyObject` constructor entry.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AnyVariant {
    /// `k_<mangled>` -- the Lean constructor name.
    pub ctor: String,
    /// The Lean type rendered for this constructor's payload.
    pub payload_lean_ty: String,
}

/// Classification of an Impure native by what kind of payload its
/// first type argument carries. Used to partition collected type
/// arguments into AnyEvent (for `event::emit`) vs AnyObject (for
/// transfer / freeze / share / receive / object::delete).
///
/// The mapping is keyed on the function's `name` (which the
/// renderer / function_lift sets from the Move qualified name). For
/// unrecognised Impure natives the type-arg is collected into
/// AnyObject conservatively -- they are rare in practice and the
/// per-package inductives stay correct (extra constructors do not
/// break anything).
fn native_payload_kind(name: &str) -> Option<NativeKind> {
    let tail = name.rsplit("::").next().unwrap_or(name);
    let tail = tail.rsplit('.').next().unwrap_or(tail);
    match tail {
        "emit" => Some(NativeKind::Event),
        "transfer"
        | "public_transfer"
        | "share_object"
        | "public_share_object"
        | "freeze_object"
        | "public_freeze_object"
        | "receive"
        | "public_receive" => Some(NativeKind::Object),
        "delete" => Some(NativeKind::Object),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeKind {
    Event,
    Object,
}

/// Collect the per-package `AnyEvent` and `AnyObject` variant sets.
pub fn collect_any_event_object(program: &Program) -> (BTreeSet<AnyVariant>, BTreeSet<AnyVariant>) {
    let mut collector = NativePayloadCollector {
        program,
        events: Vec::new(),
        objects: Vec::new(),
    };
    for func in program.functions.values() {
        collector.visit_block(&func.body);
    }
    let events: BTreeSet<AnyVariant> = collector
        .events
        .into_iter()
        .map(|ty| AnyVariant {
            ctor: any_ctor_name(&ty, program),
            payload_lean_ty: any_payload_ty(&ty, program),
        })
        .collect();
    let objects: BTreeSet<AnyVariant> = collector
        .objects
        .into_iter()
        .map(|ty| AnyVariant {
            ctor: any_ctor_name(&ty, program),
            payload_lean_ty: any_payload_ty(&ty, program),
        })
        .collect();
    (events, objects)
}

struct NativePayloadCollector<'a> {
    program: &'a Program,
    events: Vec<Type>,
    objects: Vec<Type>,
}

impl<'a> Visitor for NativePayloadCollector<'a> {
    fn visit_block(&mut self, b: &Block) {
        walk_block_default(self, b);
    }

    fn visit_expr(&mut self, e: &Expr) {
        if let Expr::Call { fun, type_args, .. } = e {
            if let Some(callee) = self.program.natives.decls.get(fun) {
                // Gate on `effects.mutation == GlobalMut` --
                // semantically precise: this captures exactly the
                // natives that mutate global state.
                if callee.effects.mutation == crate::ir::MutLevel::GlobalMut {
                    if let Some(kind) = native_payload_kind(&callee.name) {
                        if let Some(first_ta) = type_args.first() {
                            match kind {
                                NativeKind::Event => self.events.push(first_ta.clone()),
                                NativeKind::Object => self.objects.push(first_ta.clone()),
                            }
                        }
                    }
                }
            }
        }
        walk_expr_default(self, e);
    }
}

/// Emit per-package `AnyEvent.lean` content.
pub fn render_any_event_file(variants: &BTreeSet<AnyVariant>) -> String {
    render_any_inductive("AnyEvent", variants)
}

/// Emit per-package `AnyObject.lean` content.
pub fn render_any_object_file(variants: &BTreeSet<AnyVariant>) -> String {
    render_any_inductive("AnyObject", variants)
}

fn render_any_inductive(name: &str, variants: &BTreeSet<AnyVariant>) -> String {
    // Per-call payload variants are collected by
    // `collect_any_event_object` from each Impure-native call site
    // in the package. They can contain references to Move type
    // parameters (`TypeParam(N)` -> `tvN`) and bare struct IDs
    // (`S<id>`), neither of which is in scope at the package level
    // -- type params belong to the enclosing function; struct IDs
    // need to be resolved to qualified Lean names with imports.
    //
    // Doing that resolution properly is a non-trivial design step
    // (per-function variants vs. monomorphisation vs. type-poly
    // inductive). Until that lands, we emit a single placeholder
    // constructor so lake can typecheck the generated package. The
    // variants are tracked in the comment block for future use --
    // they still drive `collect_any_event_object`, just not the
    // emitted inductive shape.
    let mut out = String::new();
    out.push_str(
        "-- Generated per package by the lean-pipeline renderer.
",
    );
    out.push_str(
        "-- See plans/lean-pipeline/stage-04-effects.md.
",
    );
    out.push_str(
        "--
",
    );
    out.push_str(
        "-- The per-call payload variants collected from this
",
    );
    out.push_str(
        "-- package's Impure-native call sites are listed below
",
    );
    out.push_str(
        "-- as documentation. Until per-function / monomorphised
",
    );
    out.push_str(
        "-- variants land in `render::world`, the inductive emits
",
    );
    out.push_str(
        "-- a single placeholder constructor so lake can typecheck.

",
    );
    if variants.is_empty() {
        out.push_str(
            "-- (no effectful calls in this package)
",
        );
    } else {
        for v in variants {
            out.push_str(&format!(
                "-- variant: {} : {}
",
                v.ctor, v.payload_lean_ty
            ));
        }
    }
    out.push_str(
        "
",
    );
    out.push_str(&format!(
        "inductive {} where
",
        name
    ));
    out.push_str(
        "  | unit
",
    );
    out.push_str(
        "  deriving Inhabited
",
    );
    out
}

/// Emit the shared `Generated/World.lean` at the output root. The
/// file pulls the program-global `AnyEvent` / `AnyObject` inductives
/// into scope (themselves emitted in the same shared `Generated/`
/// lean_lib) and binds the `World` abbreviation that every Impure
/// function signature references.
///
/// One shared file instead of per-package copies: avoids the
/// `AnyEvent.ctorIdx` / `AnyObject.ctorIdx` cross-package collisions
/// that the per-package variant produced (same shape as the
/// `AnyKey.ctorIdx` collision -- see `render_program_to_dir`).
pub fn render_shared_world_file() -> String {
    let mut out = String::new();
    out.push_str(
        "-- Generated by the lean-pipeline renderer.
",
    );
    out.push_str(
        "-- See plans/lean-pipeline/stage-04-effects.md.
",
    );
    out.push_str(
        "--
",
    );
    out.push_str(
        "-- Pulls the program-global AnyEvent / AnyObject inductives into
",
    );
    out.push_str(
        "-- scope and binds the abbreviation `World` used by every
",
    );
    out.push_str(
        "-- Impure function's signature.

",
    );
    out.push_str(
        "import Prelude.World
",
    );
    out.push_str(
        "import Generated.AnyEvent
",
    );
    out.push_str(
        "import Generated.AnyObject
",
    );
    out.push_str(
        "import Generated.TyCodeInterp
",
    );
    out.push_str(
        "import Generated.ObjTypeInterp
",
    );
    out.push_str(
        "import Generated.BagUInterp
",
    );
    out.push_str(
        "import Sui.BagNatives

",
    );
    out.push_str(
        "abbrev World := Prover.World.World AnyEvent (Bag.Entry _root_.ObjType) (Bag.Entry _root_.TyCode) (Bag.Entry _root_.BagU)
",
    );
    out
}

/// Mangle a Move `Type` into an `AnyEvent` / `AnyObject` constructor
/// suffix. Same scheme as `AnyKey` mangling (see `mutation.rs`).
pub fn any_ctor_name(ty: &Type, program: &Program) -> String {
    let mut s = String::from("k");
    append_mangle(&mut s, ty, program);
    s
}

fn append_mangle(out: &mut String, ty: &Type, program: &Program) {
    match ty {
        Type::Unit => out.push_str("_unit"),
        Type::Bool => out.push_str("_bool"),
        Type::Prop => out.push_str("_prop"),
        Type::UInt(n) => out.push_str(&format!("_u{}", n)),
        Type::Address => out.push_str("_address"),
        Type::Vector(inner) => {
            out.push_str("_Vec");
            append_mangle(out, inner, program);
        }
        Type::Tuple(elems) => {
            out.push_str("_Tuple");
            for e in elems {
                append_mangle(out, e, program);
            }
        }
        Type::Struct {
            struct_id,
            type_args,
        } => {
            out.push_str("_S_");
            out.push_str(&crate::render::struct_idx::struct_tag_ident(
                *struct_id, program,
            ));
            for ta in type_args {
                append_mangle(out, ta, program);
            }
        }
        Type::Reference(inner) => {
            out.push_str("_ref");
            append_mangle(out, inner, program);
        }
        Type::MutableRef { inner, .. } => {
            out.push_str("_mutref");
            append_mangle(out, inner, program);
        }
        Type::TypeParam(n) => out.push_str(&format!("_T{}", n)),
    }
}

/// Render the Lean type of an AnyEvent / AnyObject constructor
/// payload.
pub fn any_payload_ty(ty: &Type, program: &Program) -> String {
    match ty {
        Type::Unit => "Unit".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::Prop => "Prop".to_string(),
        Type::UInt(n) => format!("BoundedNat (2^{})", n),
        Type::Address => "Address".to_string(),
        Type::Vector(inner) => format!("(List {})", any_payload_ty(inner, program)),
        Type::Tuple(elems) => {
            if elems.is_empty() {
                "Unit".to_string()
            } else {
                let parts: Vec<String> = elems.iter().map(|e| any_payload_ty(e, program)).collect();
                format!("({})", parts.join(" × "))
            }
        }
        Type::Struct {
            struct_id,
            type_args,
        } => {
            let mut s = format!(
                "S_{}",
                crate::render::struct_idx::struct_tag_ident(*struct_id, program)
            );
            for ta in type_args {
                s.push(' ');
                s.push_str(&any_payload_ty(ta, program));
            }
            s
        }
        Type::Reference(inner) | Type::MutableRef { inner, .. } => any_payload_ty(inner, program),
        Type::TypeParam(n) => format!("tv{}", n),
    }
}
