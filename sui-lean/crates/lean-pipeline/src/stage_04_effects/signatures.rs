//! Transform B: augment signatures of every function (native or not)
//! that participates in world-threading.
//!
//! For each `Function` for which `is_world_callee` is true (GlobalMut
//! natives like `transfer::transfer`, plus every translated function in
//! `needs_world`):
//! - Append a `world: World` parameter to `signature.params`.
//! - Augment `signature.return_type` to include `World` as the last
//!   tuple slot.
//!
//! Natives are augmented too: their IR signature is the single source
//! of truth for `signature.return_type` consumers (stage 10's TypeOf,
//! the renderer, etc.). The hand-written `Prover.World.*` Lean
//! prelude already declares the same augmented shape, so the IR and
//! the rendered side stay in sync without per-callee compensation.

use crate::ir::{ModId, MutLevel, Param, Program, StructId, Type};

use std::collections::BTreeSet;

use crate::ir::FunId;

use super::common::{
    augment_return_type_with_world, is_world_callee, return_already_world_augmented, world_varid,
    WORLD_VAR,
};
use super::world::world_type;
use super::Stage4Error;

/// Augment signatures for every World callee (GlobalMut native or
/// translated function in `needs_world`).
///
/// Idempotent: signatures that already carry `world: World` + a
/// trailing `World` return slot are skipped.
pub fn augment_signatures(
    program: &mut Program,
    world_id: StructId,
    needs_world: &BTreeSet<FunId>,
) -> Result<(), Stage4Error> {
    let world_ty = world_type(world_id);
    for (fid, func) in program.functions.iter_mut() {
        let cref = crate::ir::CalleeRef::Translated(&*func);
        if !is_world_callee(cref, *fid, needs_world) {
            continue;
        }
        augment_signature_inplace(
            &mut func.signature.params,
            &mut func.signature.return_type,
            world_id,
            &world_ty,
        );
    }
    // The `.aborts` predicate of a world-threaded native reads world
    // (e.g. `borrow.aborts` checks key presence) but never mutates it,
    // so the hand-written `Prover.World.*` Lean def takes a trailing
    // `world` parameter and returns a bare `Bool` -- world appears in
    // the params but NOT the return. Its `effects.mutation` is
    // `NoMut`, so `is_world_callee` (which gates on `GlobalMut`) skips
    // it; without compensation the call sites that stage 7 splices
    // (cloned from the world-threaded impl call) carry a `world` arg
    // the callee signature doesn't declare -> a call-arity mismatch.
    //
    // Target an `.aborts` native iff a `GlobalMut` base native shares
    // its module + name (minus the `.aborts` suffix) AND matching
    // param types. The param-type match disambiguates the unified
    // container-df natives (`borrow<K,V>((), T0)` -> world) from the
    // vestigial per-container stubs (`borrow<K,V>(&UID, T0)`,
    // `table::borrow(&Table, T0)`, ...) that the df rewrite routes
    // away from and that must stay world-free. Computed up-front over
    // the pre-augmentation signatures so a base augmented earlier in
    // the loop below can't perturb the match.
    let aborts_world_targets: BTreeSet<FunId> = {
        let world_bases: Vec<(ModId, &str, &[Param])> = program
            .natives
            .decls
            .iter()
            .filter(|(_, d)| d.effects.mutation == MutLevel::GlobalMut)
            .map(|(_, d)| (d.module, d.name.as_str(), d.signature.params.as_slice()))
            .collect();
        program
            .natives
            .decls
            .iter()
            .filter_map(|(fid, d)| {
                let base = d.name.strip_suffix(".aborts")?;
                let matches = world_bases.iter().any(|(bmod, bname, bparams)| {
                    *bmod == d.module
                        && *bname == base
                        && param_types_match(&d.signature.params, bparams)
                });
                matches.then_some(*fid)
            })
            .collect()
    };

    // Impure natives get the same IR-level augment (IR is the single
    // source of truth consumed by stage 10's TypeOf, the renderer,
    // etc. -- the hand-written `Prover.World.*` Lean prelude already
    // declares the same shape). Their `.aborts` predicates get the
    // world PARAM only (see above).
    for (fid, decl) in program.natives.decls.iter_mut() {
        let cref = crate::ir::CalleeRef::Native(&*decl);
        if is_world_callee(cref, *fid, needs_world) {
            augment_signature_inplace(
                &mut decl.signature.params,
                &mut decl.signature.return_type,
                world_id,
                &world_ty,
            );
        } else if aborts_world_targets.contains(fid) {
            augment_params_with_world_only(&mut decl.signature.params, world_id, &world_ty);
        }
    }
    Ok(())
}

/// Two param lists carry the same types positionally (names/vars
/// ignored). Used to match an `.aborts` native to its base native.
fn param_types_match(a: &[Param], b: &[Param]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(p, q)| p.ty == q.ty)
}

/// Append a `world: World` parameter without touching the return type
/// -- the read-only shape used by `.aborts` predicates. Idempotent.
fn augment_params_with_world_only(params: &mut Vec<Param>, world_id: StructId, world_ty: &Type) {
    let param_done = params
        .iter()
        .any(|p| matches!(&p.ty, Type::Struct { struct_id, .. } if *struct_id == world_id));
    if !param_done {
        params.push(Param {
            name: WORLD_VAR.to_string(),
            var: world_varid(),
            ty: world_ty.clone(),
        });
    }
}

fn augment_signature_inplace(
    params: &mut Vec<Param>,
    return_type: &mut Type,
    world_id: StructId,
    world_ty: &Type,
) {
    let param_done = params
        .iter()
        .any(|p| matches!(&p.ty, Type::Struct { struct_id, .. } if *struct_id == world_id));
    let return_done = return_already_world_augmented(return_type, world_id);
    if param_done && return_done {
        return;
    }
    if !param_done {
        params.push(Param {
            name: WORLD_VAR.to_string(),
            var: world_varid(),
            ty: world_ty.clone(),
        });
    }
    if !return_done {
        let orig = std::mem::replace(return_type, Type::Unit);
        *return_type = augment_return_type_with_world(orig, world_ty);
    }
}
