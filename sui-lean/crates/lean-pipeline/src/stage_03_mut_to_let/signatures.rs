//! Transform 4: augment signature.return_type for every non-native
//! function with `&mut` params.
//!
//! Parameter types are unchanged -- only the return type is rewritten
//! per [`common::augment_return_type`]. See the design doc for the rules.

use crate::ir::{Program, Type};

use super::common::{augment_return_type, mut_param_info_sig, MutParam};
use super::Stage3Error;

/// Augment the return type of every function (native or not) that has
/// any `&mut` parameters.
///
/// Idempotent: a signature whose return type already matches the
/// augmented shape is left untouched. Detection looks at the trailing
/// `muts.len()` slots of the current return type and checks whether
/// they match the `&mut` param types.
///
/// Natives are augmented too: their IR signature is the single source
/// of truth for `signature.return_type` consumers (stage 10's TypeOf,
/// the renderer, etc.). The hand-written Lean natives file still
/// strips `MutableRef` wrappers on returned values; the renderer
/// handles that strip explicitly at call sites for natives only.
pub fn augment_signatures(program: &mut Program) -> Result<(), Stage3Error> {
    for func in program.functions.values_mut() {
        let muts = mut_param_info_sig(&func.signature);
        if muts.is_empty() {
            continue;
        }
        if already_augmented(&func.signature.return_type, &muts) {
            continue;
        }
        let orig = std::mem::replace(&mut func.signature.return_type, Type::Unit);
        func.signature.return_type = augment_return_type(orig, &muts);
    }
    // Also augment NativeDecl signatures with mut params (callers
    // expect the augmented Tuple return shape regardless of whether
    // the callee is translated or native; the hand-written Lean
    // natives strip MutableRef wrappers at the call-site, handled by
    // the renderer).
    for decl in program.natives.decls.values_mut() {
        // `.aborts` native predicates read their `&mut` params but
        // never write back, so the hand-written Lean def returns a
        // bare `Bool` (e.g. `vector::pop_back.aborts ... : Bool`).
        // The writeback return augmentation that the value-returning
        // base native gets would make it `(Bool, &mut T)`; the
        // stage-7 `.aborts` companion binds that call to a single
        // var and uses it as an `if`/`while` cond, so the augmented
        // Tuple return trips `if-while-conds-are-bool`. These natives
        // are only ever called from stage-7-generated companions
        // (never by `augment_call_sites` above, which rewrites
        // translated bodies only), so leaving the return un-augmented
        // is consistent with every call site.
        if crate::ir::names::is_aborts_name(&decl.name) {
            continue;
        }
        let muts = mut_param_info_sig(&decl.signature);
        if muts.is_empty() {
            continue;
        }
        if already_augmented(&decl.signature.return_type, &muts) {
            continue;
        }
        let orig = std::mem::replace(&mut decl.signature.return_type, Type::Unit);
        decl.signature.return_type = augment_return_type(orig, &muts);
    }
    Ok(())
}

/// True iff `current` is already in the augmented shape per the
/// `&mut` params -- the trailing `muts.len()` elements of a Tuple
/// match the mut types in declaration order.
///
/// Per the always-Tuple invariant in
/// [`common::augment_return_type`], an augmented return type is
/// **always** a Tuple. Non-Tuple types are unambiguously NOT yet
/// augmented.
fn already_augmented(current: &Type, muts: &[MutParam]) -> bool {
    match current {
        Type::Tuple(items) if items.len() >= muts.len() => {
            let head_count = items.len() - muts.len();
            items[head_count..]
                .iter()
                .zip(muts.iter())
                .all(|(t, m)| t == &m.mut_ref_type)
        }
        _ => false,
    }
}
