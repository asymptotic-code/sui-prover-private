//! World-backed dynamic-field native registration.
//!
//! Every `dynamic_field::*` / `dynamic_object_field::*` operation
//! routes through the World call model: plain native calls with
//! `GlobalMut` effects whose signatures stage 4 augments with the
//! threaded `world` (see `dynamic_field_rewrite::route_df_to_world`
//! and `plans/lean-pipeline/container-df-unification.md`).
//!
//! This module registers those synthetic natives. The former
//! ghost-`TypedMap` model (per-(K, V) `dynamic_fields[_N]` struct
//! augmentation + Pack inflation + call rewriting) was deleted in
//! step-2 slice C -- it produced zero generated code across the
//! entire client corpus once routing covered every op.

use crate::ir::{Param, ProgramBuilder, Signature, Type};

use super::Stage2Error;

fn param(name: &str, var: &str, ty: Type) -> Param {
    Param {
        name: name.to_string(),
        var: var.into(),
        ty,
    }
}

/// Find the `Sui::dynamic_field` module id, if present.
fn find_dynamic_field_module(prog: &ProgramBuilder) -> Option<crate::ir::ModId> {
    prog.program().module_id_by_name("Sui", "dynamic_field")
}

/// Register the World-backed df natives. They live in the
/// `Sui::dynamic_field` module so the renderer emits
/// `_root_.Dynamic_field.<name>` (the Lean defs are in
/// `lemmas/natives/Sui/Dynamic_fieldNatives.lean`).
///
/// Effects are `GlobalMut` so stage 4 threads `world` through every
/// caller; base signatures OMIT the `world` slot (stage 4's
/// call-augmentation appends it: `borrow -> (V, world)`,
/// `set -> world`, `remove -> (V, world)`,
/// `has -> (Bool, world)`). The `uid` param is the parent's
/// `Object.UID`; its IR type is `Unit` (opaque) since the renderer
/// emits the UID argument positionally and the Lean def fixes the
/// real `Object.UID` type. Borrow/has operations are marked read-only;
/// add/set/remove operations conservatively mark World as written.
/// Idempotent.
pub(super) fn register_store_natives(prog: &mut ProgramBuilder) -> Result<(), Stage2Error> {
    use crate::ir::{AbortBit, DetBit, Effects, MutLevel, SyntheticNativeOpts};
    let Some(df_mod) = find_dynamic_field_module(prog) else {
        return Ok(());
    };
    let read_only = Effects {
        aborts: AbortBit::Partial,
        det: DetBit::Det,
        mutation: MutLevel::GlobalMut,
        world_writes: false,
    };
    let writing = Effects {
        world_writes: true,
        ..read_only
    };
    let k = Type::TypeParam(0);
    let v = Type::TypeParam(1);
    let uid = || param("uid", "$t0", Type::Unit);
    let opts = |effects| SyntheticNativeOpts {
        module: df_mod,
        effects,
        explicit_pure: true,
        spec_target: None,
    };
    // borrow(uid, k) -> V
    let borrow_fid = prog.insert_synthetic_native(
        "borrow",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![uid(), param("k", "$t1", k.clone())],
            return_type: v.clone(),
        },
        opts(read_only),
    );
    // borrow.aborts(uid, k) -> Bool. The `.aborts` companion that
    // stage 7 splices when a df borrow's parent key is absent
    // (EFieldDoesNotExist). `spec_target` back-references borrow so
    // stage 7's aborts_map wires it; the hand-written Lean body
    // (Dynamic_fieldNatives.lean) does the missing-key check against World.
    // PURE + native: stage 4 leaves its signature alone, and the spliced
    // call reuses borrow's world-threaded args.
    prog.insert_synthetic_native(
        "borrow.aborts",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![uid(), param("k", "$t1", k.clone())],
            return_type: Type::Bool,
        },
        SyntheticNativeOpts {
            module: df_mod,
            effects: Effects::PURE,
            explicit_pure: true,
            spec_target: Some(borrow_fid),
        },
    );
    // set(uid, k, v) -> () -- the synthetic upsert primitive (Move's df
    // API has no set; add aborts-if-present, so writebacks need this).
    // Deliberately NO aborts companion: writebacks must be total.
    prog.insert_synthetic_native(
        "set",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![
                uid(),
                param("k", "$t1", k.clone()),
                param("v", "$t2", v.clone()),
            ],
            return_type: Type::Unit,
        },
        opts(writing),
    );
    // add(uid, k, v) -> () -- source-level `dynamic_field::add` routes
    // here (same Lean semantics as set) so its EFieldAlreadyExists
    // abort-iff-PRESENT composes via the spec_target'd companion below,
    // while the writeback `set` stays total.
    let add_fid = prog.insert_synthetic_native(
        "add",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![
                uid(),
                param("k", "$t1", k.clone()),
                param("v", "$t2", v.clone()),
            ],
            return_type: Type::Unit,
        },
        opts(writing),
    );
    prog.insert_synthetic_native(
        "add.aborts",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![
                uid(),
                param("k", "$t1", k.clone()),
                param("v", "$t2", v.clone()),
            ],
            return_type: Type::Bool,
        },
        SyntheticNativeOpts {
            module: df_mod,
            effects: Effects::PURE,
            explicit_pure: true,
            spec_target: Some(add_fid),
        },
    );
    let remove_fid = prog.insert_synthetic_native(
        "remove",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![uid(), param("k", "$t1", k.clone())],
            return_type: v.clone(),
        },
        opts(writing),
    );
    // remove.aborts(uid, k) -> Bool. Move's `remove` aborts on a
    // missing key (EFieldDoesNotExist) exactly like `borrow`; the Lean
    // body shares borrow.aborts's presence predicate. Same
    // PURE/spec_target wiring as borrow.aborts above.
    prog.insert_synthetic_native(
        "remove.aborts",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![uid(), param("k", "$t1", k.clone())],
            return_type: Type::Bool,
        },
        SyntheticNativeOpts {
            module: df_mod,
            effects: Effects::PURE,
            explicit_pure: true,
            spec_target: Some(remove_fid),
        },
    );
    // store_remove_if_exists(uid, k) -> V. Never aborts (no companion
    // registered, deliberately); the V result is only sound where the
    // caller discards it -- the route arm asserts that shape.
    prog.insert_synthetic_native(
        "store_remove_if_exists",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![uid(), param("k", "$t1", k.clone())],
            return_type: v.clone(),
        },
        opts(writing),
    );
    // has(uid, k) -> Bool
    prog.insert_synthetic_native(
        "has",
        Signature {
            type_params: vec!["K".to_string()],
            params: vec![uid(), param("k", "$t1", k.clone())],
            return_type: Type::Bool,
        },
        opts(read_only),
    );
    // Bag-valued df natives (df VALUE is a Bag/ObjectBag). Same IR
    // signatures as their store_* counterparts so the rewrite pass only
    // swaps the callee fid; the Lean natives store the bag's entry list
    // in `World.df_bag_entries` (no `HasCode U Bag`). See
    // `dynamic_field_rewrite` + `lemmas/natives/Sui/Dynamic_fieldNatives`.
    // store_bag_borrow(uid, k) -> V (Bag value type)
    prog.insert_synthetic_native(
        "store_bag_borrow",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![uid(), param("k", "$t1", k.clone())],
            return_type: v.clone(),
        },
        opts(read_only),
    );
    // store_bag_set(uid, k, v) -> ()
    prog.insert_synthetic_native(
        "store_bag_set",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![
                uid(),
                param("k", "$t1", k.clone()),
                param("v", "$t2", v.clone()),
            ],
            return_type: Type::Unit,
        },
        opts(writing),
    );
    // store_bag_add(uid, k, v) -> () -- source-level bag-valued
    // `dynamic_field::add<K, Bag>` / `dynamic_object_field::add<K, ObjectBag>`
    // routes here (same World action as store_bag_set) so its type-agnostic
    // EFieldAlreadyExists abort composes via the spec_target'd companion
    // below, while the bag writeback `store_bag_set` stays total. Mirrors the
    // plain-df `add`/`set` split. Move's df key collision is TYPE-AGNOSTIC, so
    // the companion checks BOTH stores (bag-side + plain df_entries).
    let bag_add_fid = prog.insert_synthetic_native(
        "store_bag_add",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![
                uid(),
                param("k", "$t1", k.clone()),
                param("v", "$t2", v.clone()),
            ],
            return_type: Type::Unit,
        },
        opts(writing),
    );
    prog.insert_synthetic_native(
        "store_bag_add.aborts",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![
                uid(),
                param("k", "$t1", k.clone()),
                param("v", "$t2", v.clone()),
            ],
            return_type: Type::Bool,
        },
        SyntheticNativeOpts {
            module: df_mod,
            effects: Effects::PURE,
            explicit_pure: true,
            spec_target: Some(bag_add_fid),
        },
    );
    // store_bag_remove(uid, k) -> V (Bag value type)
    prog.insert_synthetic_native(
        "store_bag_remove",
        Signature {
            type_params: vec!["K".to_string(), "V".to_string()],
            params: vec![uid(), param("k", "$t1", k.clone())],
            return_type: v.clone(),
        },
        opts(writing),
    );
    // store_bag_has(uid, k) -> Bool
    prog.insert_synthetic_native(
        "store_bag_has",
        Signature {
            type_params: vec!["K".to_string()],
            params: vec![uid(), param("k", "$t1", k.clone())],
            return_type: Type::Bool,
        },
        opts(read_only),
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Module;

    #[test]
    fn dynamic_field_world_write_effects_match_operation_semantics() {
        let mut program = ProgramBuilder::new();
        let module = program.synthetic_module_id("test.dynamic_field");
        program.insert_module(
            module,
            Module {
                name: "dynamic_field".to_string(),
                package_name: "Sui".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: true,
            },
        );

        register_store_natives(&mut program).expect("register dynamic-field natives");
        let effect = |name: &str| {
            program
                .program()
                .natives
                .decls
                .values()
                .find(|decl| decl.name == name)
                .unwrap_or_else(|| panic!("missing synthetic native {name}"))
                .effects
        };

        for name in ["borrow", "has", "store_bag_borrow", "store_bag_has"] {
            assert!(!effect(name).world_writes, "{name} must be read-only");
        }
        for name in [
            "add",
            "set",
            "remove",
            "store_remove_if_exists",
            "store_bag_set",
            "store_bag_add",
            "store_bag_remove",
        ] {
            assert!(effect(name).world_writes, "{name} must write World");
        }
    }
}
