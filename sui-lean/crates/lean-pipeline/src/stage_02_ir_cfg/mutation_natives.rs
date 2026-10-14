//! Synthetic native for `Mutation.uninit`, used to lower upstream's
//! `Operation::Uninit` marker.
//!
//! Upstream's `livevar_analysis::transform_code` emits
//! `Bytecode::Call(_, [], Operation::Uninit, [temp_index], None)` at
//! function entry for every non-parameter mutable-reference temp that
//! is *conditionally* defined in the body (e.g. `let v = if c then
//! borrow_a else borrow_b`). The marker is a hint to upstream's
//! borrow-state machinery -- the Boogie backend lowers it to
//! `assume $t{i}->l == $Uninitialized();`, which is a constraint on
//! the reference's location field, not a definition.
//!
//! Stage 5 SSA, by contrast, expects every use to be reachable from a
//! single definition. Without a Let-bound def for the Uninit temp,
//! the conditional writebacks downstream trip `UnboundReference`.
//!
//! The Lean fix mirrors Boogie's structurally: emit a sentinel
//! `Mutation T` value at the entry point. The sentinel's `loc` is
//! distinct from any real borrow target, so the runtime `isParent`
//! dispatch the renderer already wires for `WriteBack` chains
//! returns `false` along paths where the sentinel survives. On paths
//! that overwrite the temp with a real borrow chain, the writeback
//! operates on the overwritten value as usual.
//!
//! See `Prover.Mutation.Mutation.uninit` in
//! `lemmas/Prelude/Mutation.lean` for the Lean-side definition.

use crate::ir::{FunId, Module, Param, ProgramBuilder, Signature, SyntheticNativeOpts, Type};

const PRELUDE_MODULE_LABEL: &str = "Prelude";
pub const MUTATION_UNINIT_LABEL: &str = "Mutation.uninit";

/// Register the `Mutation.uninit` native + the prelude module that
/// hosts it. Idempotent. Returns the allocated [`FunId`].
///
/// (The former co-registrant, the ghost-model's
/// `register_typed_map_natives`, was deleted in step-2C; this is
/// now the only Prelude-module registrar.)
pub fn register(prog: &mut ProgramBuilder) -> FunId {
    let prelude_mod = prog.synthetic_module_id(PRELUDE_MODULE_LABEL);
    if !prog.program().modules.contains_key(&prelude_mod)
        || prog.program().modules[&prelude_mod].name.is_empty()
    {
        prog.insert_module(
            prelude_mod,
            Module {
                name: PRELUDE_MODULE_LABEL.to_string(),
                package_name: PRELUDE_MODULE_LABEL.to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: true,
            },
        );
    }

    let t = Type::TypeParam(0);
    let signature = Signature {
        type_params: vec!["T".to_string()],
        params: vec![Param {
            name: "i".to_string(),
            var: "$t0".into(),
            ty: Type::UInt(64),
        }],
        return_type: Type::MutableRef {
            inner: Box::new(t.clone()),
            root: Box::new(t),
        },
    };
    prog.insert_synthetic_native(
        MUTATION_UNINIT_LABEL,
        signature,
        SyntheticNativeOpts {
            module: prelude_mod,
            effects: crate::ir::Effects::PURE,
            explicit_pure: false,
            spec_target: None,
        },
    )
}

/// Convenience: returns the [`FunId`] (allocating + registering on
/// first call). Subsequent calls hit the fast-path.
pub fn fid(prog: &mut ProgramBuilder) -> FunId {
    register(prog)
}
