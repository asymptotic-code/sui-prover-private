//! Per-function lifter -- top-level glue.
//!
//! Takes a stage-1 [`BytecodeCfg`], the upstream [`FunctionTarget`],
//! and a [`ProgramBuilder`]. Produces an IR [`Function`] (signature
//! + body) and inserts it under a freshly allocated [`FunId`].
//!
//! Composes the per-bytecode translator
//! ([`super::translate_op`]), the per-Region structurer
//! ([`super::lift_region`]), the type translator
//! ([`super::types::translate_type`]), and the borrow-state tracker
//! ([`super::borrow_state::BorrowState`]).
//!
//! ## Pipeline ownership
//!
//! - Pre-pass A (native filter): callers are expected to pass only
//!   non-native targets here. The native-module check
//!   ([`super::natives`]) lives at the per-module dispatch layer.
//! - Pre-pass C (effects classification): runs over the dependency
//!   graph after all functions are lifted. The initial
//!   [`crate::ir::Effects::CONSERVATIVE`] keeps the IR valid in the
//!   meantime.
//! - Spec extraction (`.requires` / `.ensures` / `.asserts`
//!   companions): stage 7's job; stage 2 lifts `prover::*` calls as
//!   ordinary `Expr::Call` nodes inside the spec function body.
//! - Mutable-reference erasure happens downstream. This lifter keeps
//!   borrows and write-backs explicit in the IR.

use move_stackless_bytecode::function_target::FunctionTarget;

use crate::ir::{FunId, Function, FunctionKind, Param, ProgramBuilder, Signature, Type};
use crate::stage_01_bytecode_cfg::BytecodeCfg;

use super::lift_region::lift_region;
use super::translate_op::temp_name;
use super::types::translate_type;
use super::Stage2Error;

/// Lift a stage-1 [`BytecodeCfg`] for a single function into IR.
///
/// Allocates a fresh [`FunId`] in `prog`, builds a [`Function`] with
/// the translated signature + body, inserts it, and returns the id.
///
/// On failure, no partial Function is inserted (the FunId is still
/// allocated, but `prog.program().functions` won't have an entry for
/// it -- callers that retry must use a fresh `prog`).
pub fn lift_function(
    cfg: BytecodeCfg,
    target: &FunctionTarget,
    prog: &mut ProgramBuilder,
) -> Result<FunId, Stage2Error> {
    let signature = lift_signature(&target.func_env, prog)?;
    let module_id = prog.module_id(target.func_env.module_env.get_id());
    let name = target
        .func_env
        .get_name()
        .display(target.global_env().symbol_pool())
        .to_string();
    let func_qid = move_model::model::QualifiedId {
        module_id: target.func_env.module_env.get_id(),
        id: target.func_env.get_id(),
    };
    let fid = prog.function_id(func_qid);

    // Spec-only ghost variables this function threads (transitive), read
    // from the upstream SpecGlobalVariableInfo annotation. Stored on the
    // Program for the stage-4 ghost-threading pass; never in World/TyCode.
    let ghost_vars = read_ghost_vars(target, prog)?;
    if !ghost_vars.is_empty() && std::env::var("GHOST_DBG").is_ok() {
        eprintln!("[ghost] {name} -> {ghost_vars:?}");
    }

    // Post step 5: `program.functions` contains translated functions
    // only. Natives are registered as `NativeDecl` entries by
    // `module_lift` and never reach `lift_function`. The pipeline
    // driver (phase 2 in pipeline.rs) filters natives out; this
    // assert makes the contract explicit.
    debug_assert!(
        !target.func_env.is_native(),
        "lift_function called on a native function -- pipeline driver should have skipped it",
    );
    let code = target.get_bytecode();
    // `borrow_mut_kv` is the per-function (K, V) registry that
    // matches a `borrow_mut` callsite's dest temp to its WriteBack
    // edge. Hoisted from `lift_basic_range`'s old per-basic-block
    // scope so that a borrow_mut in one block remains visible to its
    // WriteBack in a later block -- an `assert!` between them
    // creates a CFG split that previously dropped the kv map and
    // collapsed the lifted `MapKey { K, V }` edge to a Unit/Unit
    // placeholder (and then to `Direct` via `normalize_borrow_edge`).
    let mut borrow_mut_kv: std::collections::BTreeMap<
        crate::ir::VarId,
        Vec<(crate::ir::Type, crate::ir::Type)>,
    > = std::collections::BTreeMap::new();
    let mut body = lift_region(&cfg.root, code, target, prog, &mut borrow_mut_kv)?;
    // Canonicalize terminating-arm `If` / `Match` into Value-tail
    // position. `lift_region` emits all `If` / `Match` uniformly as
    // `Stmt::Eval(...) + Value(Unit)` tail; this pass hoists the
    // expression into the surrounding block's `tail` slot when every
    // arm has a non-`Value(Unit)` tail. See
    // `canonicalize_terminators.rs` for rationale + the example walk-
    // through for `move_stl::skip_list_u128::rand_level`.
    super::canonicalize_terminators::canonicalize(&mut body);

    let mut func = Function {
        module: module_id,
        name,
        signature,
        body,
        kind: FunctionKind::Source,
        // Initial intrinsic-only classification. The body walker
        // emits independent evidence for the abort and mutation
        // axes; the DetBit axis stays Det at this stage and only
        // flips to NonDet through the fixpoint when a `random::*`
        // native shows up as a transitive callee. The
        // post-translation `classify_effects` pass propagates the
        // result across the call graph.
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: false,
    };
    func.effects = super::effects::intrinsic_effects(&func);
    // `#[ext(pure)]` overrides the intrinsic-walked effects. See
    // `module_lift.rs` for the rationale. Set both the effects and
    // the explicit_pure flag so `classify_effects` later refuses
    // to demote it via the callee-fixpoint meet.
    if super::natives::has_ext_pure(&target.func_env) {
        func.effects = crate::ir::Effects::PURE;
        func.explicit_pure = true;
    }
    prog.insert_function(fid, func);
    if !ghost_vars.is_empty() {
        prog.program_mut().ghost_vars.insert(fid, ghost_vars);
    }
    Ok(fid)
}

/// Read the spec-only ghost variables this function threads, from the
/// upstream `SpecGlobalVariableInfo` annotation (transitive across
/// callees). Returns the `(K, V)` IR-type pairs in the annotation's
/// upstream-`Type`-sorted order so caller/callee agree positionally.
/// Empty when the function touches no ghost or the annotation is absent.
fn read_ghost_vars(
    target: &FunctionTarget,
    prog: &mut ProgramBuilder,
) -> Result<Vec<(crate::ir::Type, crate::ir::Type)>, Stage2Error> {
    use move_stackless_bytecode::spec_global_variable_analysis::SpecGlobalVariableInfo;
    let Some(info) = target.data.annotations.get::<SpecGlobalVariableInfo>() else {
        return Ok(Vec::new());
    };
    let mut out = Vec::new();
    for var in info.all_vars() {
        // Each ghost var is a `[K, V]` type instantiation.
        if var.len() != 2 {
            continue;
        }
        let k = translate_type(&var[0], prog)?;
        let v = translate_type(&var[1], prog)?;
        out.push((k, v));
    }
    Ok(out)
}

/// Insert a body-less stub Function for a target whose stage 1 / stage 2
/// lift failed in permissive mode. Without this, the `FunId` allocated
/// by an earlier call to `prog.function_id(...)` (or by name resolution
/// inside `module_lift`) would have no corresponding entry in
/// `program.functions`, and every Call site referencing it would trip
/// the validator's `UnknownFunctionId` check at render time.
///
/// The stub has the correctly-lifted signature (so arity at call sites
/// type-checks) and a body of `BlockTail::Abort { code: Const::U64(0) }`,
/// which the renderer emits as `sorry`. Returns `Ok(fid)` on success.
/// If even signature lifting fails (e.g. type translation hits an
/// unsupported shape), the function remains unregistered and the caller
/// surfaces both the original body-lift error and this fallback error.
pub(super) fn lift_function_stub(
    target: &FunctionTarget,
    prog: &mut ProgramBuilder,
) -> Result<FunId, Stage2Error> {
    use crate::ir::{Block, BlockTail, Const, Expr};
    let signature = lift_signature(&target.func_env, prog)?;
    let module_id = prog.module_id(target.func_env.module_env.get_id());
    let name = target
        .func_env
        .get_name()
        .display(target.global_env().symbol_pool())
        .to_string();
    let func_qid = move_model::model::QualifiedId {
        module_id: target.func_env.module_env.get_id(),
        id: target.func_env.get_id(),
    };
    let fid = prog.function_id(func_qid);
    let body = Block {
        stmts: Vec::new(),
        tail: BlockTail::Abort {
            code: Box::new(Expr::Const(Const::UInt {
                bits: 64,
                value: ethnum::U256::from(0u64),
            })),
        },
    };
    let func = Function {
        module: module_id,
        name,
        signature,
        body,
        kind: FunctionKind::Source,
        // Treat the stub as worst-case Effects::CONSERVATIVE so
        // callers continue to receive world threading even though
        // the body is an Abort (which `intrinsic_effects` would
        // otherwise classify as Partial / NoMut). Reusing
        // `explicit_pure: true` -- meant for user-annotated
        // `#[ext(pure)]` -- as the "trust this effects field, don't
        // re-derive" flag is slightly overloaded, but it's the only
        // existing knob that pins effects through the
        // classify_effects fixpoint.
        effects: crate::ir::Effects::CONSERVATIVE,
        explicit_pure: true,
    };
    prog.insert_function(fid, func);
    Ok(fid)
}

/// Lift a Move function's signature into IR. Accepts a
/// `FunctionEnv` directly so both [`super::module_lift`] (which only
/// has the env) and the body lifter (which has a `FunctionTarget`)
/// can share the helper.
///
/// Convention: parameter slot `i` is bound to temp `$ti` at function
/// entry, matching what the body's `Var($tN)` refs expect.
pub(super) fn lift_signature(
    func_env: &move_model::model::FunctionEnv,
    prog: &mut ProgramBuilder,
) -> Result<Signature, Stage2Error> {
    let pool = func_env.module_env.env.symbol_pool();

    let type_params = func_env
        .get_type_parameters()
        .iter()
        .map(|tp| pool.string(tp.0).to_string())
        .collect();

    let params = func_env
        .get_parameters()
        .iter()
        .enumerate()
        .map(|(i, p)| {
            Ok::<_, Stage2Error>(Param {
                name: pool.string(p.0).to_string(),
                var: temp_name(i),
                ty: translate_type(&p.1, prog)?,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Move return-type lifting: 0 returns -> Unit, 1 -> the type, N -> Tuple.
    let return_type = match func_env.get_return_types().as_slice() {
        [] => Type::Unit,
        [t] => translate_type(t, prog)?,
        ts => {
            let elems = ts
                .iter()
                .map(|t| translate_type(t, prog))
                .collect::<Result<Vec<_>, _>>()?;
            Type::Tuple(elems)
        }
    };

    let sig = Signature {
        type_params,
        params,
        return_type,
    };

    // No dynamic_field / dynamic_object_field native-signature rewrite:
    // the new pipeline skips upstream's `DynamicFieldAnalysisProcessor`
    // (see `build_lean_pipeline`) and models dynamic fields directly in
    // `World` keyed by UID, so df call sites keep their natural source
    // signature (`&[mut] UID` first param, `[K, V]` type-args). See
    // `plans/lean-pipeline/dynamic-fields-in-world.md`. (An earlier
    // approach synthesised a trailing parent type-param and rewrote the
    // first param to it; abandoned with the World model.)

    Ok(sig)
}

#[cfg(test)]
mod tests {
    //! End-to-end tests need a real `FunctionTarget`, which requires a
    //! Move source file and a model build. Until the integration
    //! harness lands, the testable surface here is the helpers.
    //!
    //! `lift_signature` doesn't expose a fixture-friendly hook
    //! either (it reads through `FunctionTarget`), so we defer its
    //! direct testing.
    use super::*;

    #[test]
    fn temp_name_convention_matches_param_slot() {
        // Smoke: param slot N -> `$tN`. The signature lifter relies
        // on this convention so the body's Var($tN) refs resolve.
        assert_eq!(&*temp_name(0), "$t0");
        assert_eq!(&*temp_name(1), "$t1");
    }
}
