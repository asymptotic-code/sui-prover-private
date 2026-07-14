// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! World threading (unified-backend design Phase 1): lower per-case state
//! mechanisms onto one threaded `World` value.
//!
//! Two phases, bracketing `thread_mutables` (mirroring the two-phase
//! bracketing of `dynamic_field_rewriting`, which this pass REPLACES in
//! world-mode):
//!
//! ## Phase A — `lower_state_ops_pre_threading` (pre-threading)
//!
//! Registers the synthetic native `World` module/struct + the typed-view
//! natives (`getDf`/`setDf`/`eraseDf`/`hasDf`/`putOwned`/`putShared`/
//! `putFrozen`/`emitEvent`, rendered against the wrappers emitted into
//! `Generated/World.lean`), then rewrites every state op into a call on the
//! `__world` variable:
//!
//! * `dynamic_field::add`      → `let __world := World.setDf K V __world uid k v`
//! * `dynamic_field::remove`   → typed read (`MatchOption` over `World.getDf`,
//!   `none` ⇒ `Abort 1` / EFieldDoesNotExist) + `let __world := World.eraseDf …`
//! * `dynamic_field::borrow`   → `MatchOption` over `World.getDf` (honest
//!   abort-on-missing; the derived `.aborts` face picks the `none ⇒ some`
//!   branch up automatically via `inject_arithmetic_aborts`'s walk)
//! * `dynamic_field::borrow_mut` → `MutableBorrow { val_expr: <borrow shape>,
//!   reconstruct_expr: World.setDf K V __world uid k __v, state_type: World }`
//!   — the exact bracketing contract `rewrite_df_borrow_mut_pre_threading`
//!   has with `thread_mutables` today, with `__world` as the reconstructed
//!   parent (see `mutable_threading::extract_parent_var`'s `__world` arm)
//! * `dynamic_field::exists_`  → `World.hasDf K __world uid k`
//! * `dynamic_field::exists_with_type` → typed `getDf` isSome match
//! * `transfer::{public_,}transfer{,_impl}` → `let __world := World.putOwned …`
//!   (likewise share/freeze → `putShared`/`putFrozen`)
//! * `event::emit` → `let __world := World.emitEvent …`
//!
//! Functions whose body gained a `__world` reference get the trailing
//! `__world : World` parameter HERE (before `thread_mutables`), so the
//! borrow_mut writeback machinery sees `__world` in scope and rebinds it
//! like any parent struct var.
//!
//! ## Phase B — `thread_world` (post-threading, ghost_threading's slot)
//!
//! The interprocedural half, a single-marker clone of `ghost_threading`:
//! callee→caller fixpoint over `IRNode::calls()` from the Phase-A seed;
//! trailing `__world : World` param on every threaded function; value faces
//! (everything except `.aborts`/`.requires`/`.ensures`/Prop returns) gain the
//! trailing return slot (`augmented_return`) and have tails wrapped; call
//! sites to threaded value-face callees destructure and rebind `__world`.
//! World-native calls need nothing here: Phase A already threads `__world`
//! through them by value-position (`let __world := World.setDf … __world …`).
//!
//! ## Inertness
//!
//! Both entry points return on their first line unless the client declared
//! `world_mode` in a `def <Module>.module_options` hook (scanned from
//! `sources/lean/**` into `LeanTerminationDecls::module_options`). With the
//! gate off the output is byte-identical.

use crate::data::functions::{Function, FunctionID, FunctionSignature, Parameter};
use crate::data::ir::{Const, IRNode};
use crate::data::structure::{Struct, StructID};
use crate::data::types::{TempId, Type};
use crate::data::{Module, Program};
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

pub const WORLD_VAR: &str = "__world";
/// Marker qualified name for the synthetic World struct; the type renderer
/// special-cases it to the per-project `Generated/World.lean` abbrev.
pub const WORLD_STRUCT_QN: &str = "prover_world::World";
/// `sui::dynamic_field::EFieldDoesNotExist`.
const E_FIELD_DOES_NOT_EXIST: u64 = 1;

/// IDs of the synthetic World module/struct and typed-view natives. Stored on
/// `Program` so the renderer (type special-case, `Generated/World.lean`
/// emission, `import Generated.World` injection, DF-universe collection) can
/// consume them without recomputing.
#[derive(Debug, Clone)]
pub struct WorldFunctions {
    pub module_id: usize,
    pub struct_id: StructID,
    pub get_df: FunctionID,
    pub set_df: FunctionID,
    pub erase_df: FunctionID,
    pub has_df: FunctionID,
    pub has_df_typed: FunctionID,
    /// Bag-valued df views (`getDfBag`/`setDfBag`/`hasDfBag`/`eraseDfBag`). A
    /// `Bag`/`ObjectBag` value cannot be a `DfU` universe member (a bag can't
    /// live in its own universe), so it is stored structurally in the
    /// `DfVal.bag` arm rather than through the `HasCode`-constrained typed
    /// views. These render to the per-project `Generated/World.lean` wrappers
    /// that reconstruct the `Bag` from its stored parts.
    pub get_df_bag: FunctionID,
    pub set_df_bag: FunctionID,
    pub has_df_bag: FunctionID,
    pub erase_df_bag: FunctionID,
    /// `Mutable α World → S → Mutable α (S × World)` — the world-branch lift
    /// for heterogeneous mutable phis (M1).
    pub mut_lift_world: FunctionID,
    /// `Mutable α S → World → Mutable α (S × World)` — the struct-branch lift.
    pub mut_lift_state: FunctionID,
    /// `(A × B) → A` / `(A × B) → B` — single-line tuple projections used by
    /// the bundle substitution for destructured callee results (implicit type
    /// args; emitted with empty `type_args`).
    pub pfst: FunctionID,
    pub psnd: FunctionID,
    pub put_owned: FunctionID,
    pub put_shared: FunctionID,
    pub put_frozen: FunctionID,
    pub emit_event: FunctionID,
    /// Transfer-marker reads (the World-resident replacement for the retired
    /// transfer spec-ghost slots): `transferExists : World → Bool`,
    /// `lastTransfer : World → Address`.
    pub transfer_exists: FunctionID,
    pub last_transfer: FunctionID,
    /// `memberUid T obj : Object.UID` — generic `key`-object UID projection
    /// via `Universe.uidNat`. HasCode-constrained on `T` so a generic transfer
    /// keys its object into the World store.
    pub member_uid: FunctionID,
    /// test_scenario inventory reads (owner-indexed World object-store views).
    pub ids_for_address: FunctionID,
    pub most_recent_id_for_address: FunctionID,
    pub was_taken_from_address: FunctionID,
    pub take_from_address_by_id: FunctionID,
    /// test_scenario shared-object custody (shared-indexed, type-filtered
    /// World object-store views).
    pub most_recent_id_shared: FunctionID,
    pub was_taken_shared: FunctionID,
    pub take_shared_by_id: FunctionID,
    /// `test_scenario::end_transaction`: reads and resets the per-tx
    /// user-event counter `World.emit` bumps.
    pub take_tx_user_events: FunctionID,
}

impl WorldFunctions {
    pub fn all_ids(&self) -> [FunctionID; 24] {
        [
            self.get_df,
            self.set_df,
            self.erase_df,
            self.has_df,
            self.has_df_typed,
            self.get_df_bag,
            self.set_df_bag,
            self.has_df_bag,
            self.erase_df_bag,
            self.put_owned,
            self.put_shared,
            self.put_frozen,
            self.emit_event,
            self.transfer_exists,
            self.last_transfer,
            self.member_uid,
            self.ids_for_address,
            self.most_recent_id_for_address,
            self.was_taken_from_address,
            self.take_from_address_by_id,
            self.most_recent_id_shared,
            self.was_taken_shared,
            self.take_shared_by_id,
            self.take_tx_user_events,
        ]
    }

    pub fn world_type(&self) -> Type {
        Type::Struct {
            struct_id: self.struct_id,
            type_args: vec![],
        }
    }
}

/// The per-package `world_mode` gate: any scanned `def <Module>.module_options`
/// hook that lists `"world_mode"`.
pub fn world_mode_enabled(program: &Program) -> bool {
    program
        .lean_termination_decls
        .module_options
        .values()
        .any(|opts| opts.contains("world_mode"))
}

fn world_var() -> TempId {
    Rc::from(WORLD_VAR)
}

// ============================================================================
// Phase A — lowering
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StateOp {
    DfAdd,
    DfRemove,
    DfBorrow,
    DfBorrowMut,
    DfExists,
    DfExistsWithType,
    TransferOwned,
    TransferShared,
    TransferFrozen,
    EventEmit,
    IdsForAddress,
    MostRecentIdForAddress,
    WasTakenFromAddress,
    TakeFromAddressById,
    MostRecentIdShared,
    WasTakenShared,
    TakeSharedById,
    BorrowUid,
    ObjectId,
    EndTransaction,
}

fn collect_state_ops(program: &Program) -> HashMap<FunctionID, StateOp> {
    let mut ops = HashMap::new();
    for (fid, func) in program.functions.iter() {
        let module = program.modules.get(&func.module_id);
        let op = match (module.name.as_str(), func.name.as_str()) {
            ("dynamic_field", "add") => StateOp::DfAdd,
            ("dynamic_field", "remove") => StateOp::DfRemove,
            ("dynamic_field", "borrow") => StateOp::DfBorrow,
            ("dynamic_field", "borrow_mut") => StateOp::DfBorrowMut,
            ("dynamic_field", "exists_") => StateOp::DfExists,
            ("dynamic_field", "exists_with_type") => StateOp::DfExistsWithType,
            ("transfer", "transfer") | ("transfer", "public_transfer") => StateOp::TransferOwned,
            ("transfer", "transfer_impl") => StateOp::TransferOwned,
            ("transfer", "share_object")
            | ("transfer", "public_share_object")
            | ("transfer", "share_object_impl") => StateOp::TransferShared,
            ("transfer", "freeze_object")
            | ("transfer", "public_freeze_object")
            | ("transfer", "freeze_object_impl") => StateOp::TransferFrozen,
            ("event", "emit") => StateOp::EventEmit,
            ("test_scenario", "ids_for_address") => StateOp::IdsForAddress,
            ("test_scenario", "most_recent_id_for_address") => StateOp::MostRecentIdForAddress,
            ("test_scenario", "was_taken_from_address") => StateOp::WasTakenFromAddress,
            ("test_scenario", "take_from_address_by_id") => StateOp::TakeFromAddressById,
            ("test_scenario", "most_recent_id_shared") => StateOp::MostRecentIdShared,
            ("test_scenario", "was_taken_shared") => StateOp::WasTakenShared,
            ("test_scenario", "take_shared_by_id") => StateOp::TakeSharedById,
            ("test_scenario", "end_transaction") => StateOp::EndTransaction,
            ("object", "borrow_uid") => StateOp::BorrowUid,
            ("object", "id") | ("object", "borrow_id") => StateOp::ObjectId,
            _ => continue,
        };
        ops.insert(fid, op);
    }
    ops
}

fn register_world(program: &mut Program) -> WorldFunctions {
    let module_id = program.modules.items.keys().copied().max().unwrap_or(0) + 2000;
    program.modules.items.insert(
        module_id,
        Module {
            name: "world".to_string(),
            package_name: "Prelude".to_string(),
            required_imports: vec![],
            is_native: true,
        },
    );

    let struct_id = program.structs.items.keys().copied().max().unwrap_or(0) + 2000;
    program.structs.items.insert(
        struct_id,
        Struct {
            module_id,
            name: "World".to_string(),
            qualified_name: WORLD_STRUCT_QN.to_string(),
            type_params: vec![],
            fields: vec![],
            mutual_group_id: None,
            variants: None,
        },
    );

    let world_ty = Type::Struct {
        struct_id,
        type_args: vec![],
    };

    let mut make = |name: &str, type_params: Vec<&str>, return_type: Type| -> FunctionID {
        program.functions.add(Function {
            module_id,
            name: name.to_string(),
            signature: FunctionSignature {
                type_params: type_params.into_iter().map(|s| s.to_string()).collect(),
                parameters: vec![],
                proof_params: Vec::new(),
                return_type,
            },
            body: IRNode::default(),
            theorem: None,
            is_native: true,
            mutual_group_id: None,
            test_expectation: None,
            is_uninterpreted: false,
        })
    };

    let get_df = make(
        "getDf",
        vec!["K", "V"],
        Type::Option(Box::new(Type::TypeParameter(1))),
    );
    let set_df = make("setDf", vec!["K", "V"], world_ty.clone());
    let erase_df = make("eraseDf", vec!["K", "V"], world_ty.clone());
    let has_df = make("hasDf", vec!["K"], Type::Bool);
    let has_df_typed = make("hasDfTyped", vec!["K", "V"], Type::Bool);
    // Bag-valued df views: the value type is the (monomorphic in the world
    // model) `bag::Bag` struct, so its type is fixed here rather than carried
    // as a `V` type param. The `Bag` value is stored structurally (no
    // `HasCode` on the value), so these take only the key type param `K`.
    let bag_value_ty = program
        .structs
        .iter()
        .find(|(_, s)| s.qualified_name == "bag::Bag")
        .map(|(id, _)| Type::Struct {
            struct_id: *id,
            type_args: vec![],
        });
    let get_df_bag = make(
        "getDfBag",
        vec!["K"],
        Type::Option(Box::new(bag_value_ty.clone().unwrap_or(Type::Bool))),
    );
    let set_df_bag = make("setDfBag", vec!["K"], world_ty.clone());
    let has_df_bag = make("hasDfBag", vec!["K"], Type::Bool);
    let erase_df_bag = make("eraseDfBag", vec!["K"], world_ty.clone());
    let pair_mutref = Type::MutableReference(
        Box::new(Type::TypeParameter(0)),
        Box::new(Type::Tuple(vec![Type::TypeParameter(1), world_ty.clone()])),
    );
    let mut_lift_world = make("mutLiftWorld", vec!["A", "S"], pair_mutref.clone());
    let mut_lift_state = make("mutLiftState", vec!["A", "S"], pair_mutref);
    let pfst = make("pfst", vec![], Type::TypeParameter(0));
    let psnd = make("psnd", vec![], Type::TypeParameter(1));
    let put_owned = make("putOwned", vec!["T"], world_ty.clone());
    let put_shared = make("putShared", vec!["T"], world_ty.clone());
    let put_frozen = make("putFrozen", vec!["T"], world_ty.clone());
    let emit_event = make("emitEvent", vec!["T"], world_ty.clone());
    let transfer_exists = make("transferExists", vec![], Type::Bool);
    let last_transfer = make("lastTransfer", vec![], Type::Address);
    // `memberUid T obj : Object.UID` — the object-UID of a GENERIC `key`
    // object, via the `Universe.uidNat` projection (so world-mode can key a
    // `transfer::*` / `return_*` over a bare `T: key` without structural field
    // projection). Return type is the `sui::object::UID` struct; falls back to
    // `world_ty` if the program has no UID struct (never happens in world-mode,
    // which always pulls in `sui::object`).
    let uid_return_ty = program
        .structs
        .iter()
        .find(|(_, s)| s.name == "UID")
        .map(|(id, _)| Type::Struct {
            struct_id: *id,
            type_args: vec![],
        })
        .unwrap_or_else(|| world_ty.clone());
    let member_uid = make("memberUid", vec!["T"], uid_return_ty);

    // test_scenario inventory reads. Return types mirror the Move natives so
    // rewritten call sites stay well-typed: `ids_for_address` → `vector<ID>`,
    // `most_recent_id_for_address` → `Option<ID>` (MoveOption), `was_taken_*`
    // → bool, `take_from_address_by_id` → the object `T` (world threaded out
    // separately, like a mutref result).
    let id_ty = program
        .structs
        .iter()
        .find(|(_, s)| s.name == "ID")
        .map(|(id, _)| Type::Struct {
            struct_id: *id,
            type_args: vec![],
        })
        .unwrap_or(Type::Address);
    let option_id_ty = program
        .structs
        .iter()
        .find(|(_, s)| s.name == "MoveOption")
        .map(|(id, _)| Type::Struct {
            struct_id: *id,
            type_args: vec![id_ty.clone()],
        })
        .unwrap_or_else(|| Type::Option(Box::new(id_ty.clone())));
    let ids_for_address = make("idsForAddress", vec!["T"], Type::Vector(Box::new(id_ty)));
    let most_recent_id_for_address =
        make("mostRecentIdForAddress", vec!["T"], option_id_ty.clone());
    let was_taken_from_address = make("wasTakenFromAddress", vec![], Type::Bool);
    let take_from_address_by_id = make(
        "takeFromAddressById",
        vec!["T"],
        Type::Tuple(vec![Type::TypeParameter(0), world_ty.clone()]),
    );

    // Shared-object custody (type-filtered — distinct shared singletons of
    // different types coexist in one scenario).
    let most_recent_id_shared = make("mostRecentIdShared", vec!["T"], option_id_ty);
    let was_taken_shared = make("wasTakenShared", vec![], Type::Bool);
    let take_shared_by_id = make(
        "takeSharedById",
        vec!["T"],
        Type::Tuple(vec![Type::TypeParameter(0), world_ty.clone()]),
    );

    // `test_scenario::end_transaction`: read + reset the per-tx user-event
    // counter (`World.emit` bumps it; per-tx semantics require the reset).
    let take_tx_user_events = make(
        "takeTxUserEvents",
        vec![],
        Type::Tuple(vec![Type::UInt(64), world_ty.clone()]),
    );

    WorldFunctions {
        module_id,
        struct_id,
        get_df,
        set_df,
        erase_df,
        has_df,
        has_df_typed,
        get_df_bag,
        set_df_bag,
        has_df_bag,
        erase_df_bag,
        mut_lift_world,
        mut_lift_state,
        pfst,
        psnd,
        put_owned,
        put_shared,
        put_frozen,
        emit_event,
        transfer_exists,
        last_transfer,
        member_uid,
        ids_for_address,
        most_recent_id_for_address,
        was_taken_from_address,
        take_from_address_by_id,
        most_recent_id_shared,
        was_taken_shared,
        take_shared_by_id,
        take_tx_user_events,
    }
}

pub fn lower_state_ops_pre_threading(program: &mut Program) {
    if !world_mode_enabled(program) {
        return;
    }
    let ops = collect_state_ops(program);
    let world = register_world(program);
    let world_ty = world.world_type();
    let uid_struct_id: Option<StructID> = program
        .structs
        .iter()
        .find(|(_, s)| s.qualified_name == "object::UID")
        .map(|(id, _)| *id);
    let bag_struct_id: Option<StructID> = program
        .structs
        .iter()
        .find(|(_, s)| s.qualified_name == "bag::Bag")
        .map(|(id, _)| *id);

    let fn_ids: Vec<FunctionID> = program.functions.iter_ids().collect();
    for fid in fn_ids {
        let func = program.functions.get(&fid);
        if func.is_native || func.module_id == world.module_id {
            continue;
        }
        // Never lower inside the state-op modules themselves (their bodies
        // stay as unreachable low-level-native stubs in world-mode), nor
        // inside their spec companions (`transfer_spec` & co. — generic spec
        // wrappers over the same natives). Bag/ObjectBag are VALUE-CARRIED
        // (their ops are hand-written in `BagNatives.lean` /
        // `Object_bagNatives.lean` over the in-value storage list — the
        // Phase-0 model); lowering their generated bodies would thread
        // `__world` onto calls that render to those un-threaded natives.
        let module_name = program.modules.get(&func.module_id).name.clone();
        let module_base = module_name
            .trim_end_matches("_specs")
            .trim_end_matches("_spec");
        if matches!(
            module_base,
            "dynamic_field" | "transfer" | "event" | "bag" | "object_bag"
        ) {
            continue;
        }
        let func = program.functions.get_mut(fid);
        let body = std::mem::take(&mut func.body);
        // Seed the UID bindings from parameters: the IR translator's
        // BorrowField-then-call substitution passes the PARENT slot directly
        // to df ops (`peek(c, k)` calls `borrow` with `Var(c)`), so a param
        // whose type is a UID-headed struct resolves to `c.id`, and a plain
        // `UID` param resolves to itself.
        let mut seed: HashMap<TempId, (IRNode, Option<StructID>)> = HashMap::new();
        {
            let func = program.functions.get(&fid);
            for p in &func.signature.parameters {
                let name: TempId = Rc::from(p.name.as_str());
                match peel_refs(&p.param_type) {
                    Type::Struct { struct_id, .. } => {
                        if is_uid_struct(program, *struct_id) {
                            seed.insert(name.clone(), (IRNode::Var(name), None));
                        } else if struct_has_uid_head(program, *struct_id) {
                            seed.insert(
                                name.clone(),
                                (
                                    IRNode::Field {
                                        struct_id: *struct_id,
                                        field_index: 0,
                                        base: Box::new(IRNode::Var(name)),
                                    },
                                    Some(*struct_id),
                                ),
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
        let lower_object_ids = {
            let m = program.modules.get(&program.functions.get(&fid).module_id);
            // Only `object` itself needs the exclusion: its own generic
            // `id`/`borrow_uid` bodies lowering to `memberUid` would make
            // that low-level framework file import `Generated.World`, which
            // transitively imports `object` back (an import cycle). Every
            // other Sui/MoveStdlib module (notably `test_scenario`, whose
            // `.aborts` bodies call `object::id`/`borrow_uid` on a generic
            // `T` to build inventory-check uids) already needs the real
            // uid -- excluding the whole package left those calls on the
            // hollow `default`-returning native stub instead of
            // `World.memberUid`, breaking `was_taken_shared`/
            // `was_taken_from_address` checks for every generic-`T` test
            // using `take_shared`/`take_from_sender` + return.
            m.name != "object"
        };
        let mut ctx = LowerCtx {
            ops: &ops,
            world: &world,
            fn_name: program.functions.get(&fid).name.clone(),
            lower_object_ids,
            uid_struct_id,
            bag_struct_id,
            uses_world: false,
            bindings: seed,
            parent_bindings: HashMap::new(),
        };
        let body = lower_node(body, &mut ctx, program);
        let func = program.functions.get_mut(fid);
        func.body = body;
        if ctx.uses_world {
            // `__world`'s type flows from the parameter (the registry is
            // rebuilt from `signature.parameters` via `param_registry`).
            func.signature.parameters.push(Parameter {
                name: WORLD_VAR.to_string(),
                param_type: world_ty.clone(),
                ssa_value: world_var(),
            });
        }
    }

    program.world_functions = Some(world);
}

/// Resolvable UID sources for the first argument of a df op: the arg is a
/// (borrowed) `UID` value — a direct `parent.id` field read, a
/// `MutableBorrow` of one, or a variable bound to either.
struct LowerCtx<'a> {
    ops: &'a HashMap<FunctionID, StateOp>,
    world: &'a WorldFunctions,
    /// Enclosing function name (error messages only).
    fn_name: String,
    /// Whether object-id projections (`object::id` / `borrow_uid`) may be
    /// lowered in the enclosing module. False inside the Sui/MoveStdlib
    /// framework: lowering there (notably `object::id`'s own generic body →
    /// `memberUid`) would make low-level framework files import
    /// `Generated.World`, which transitively imports them back — an import
    /// cycle. User-package call sites are concrete-struct projections (no new
    /// import) or already import Generated.World.
    lower_object_ids: bool,
    /// `object::UID`'s struct id (its field 0 is the inner `ID`).
    uid_struct_id: Option<StructID>,
    /// `bag::Bag`'s struct id: df ops whose VALUE type is this struct route to
    /// the structural bag views (`getDfBag`/...) instead of the `HasCode`-typed
    /// ones, because a bag cannot be a member of its own universe.
    bag_struct_id: Option<StructID>,
    uses_world: bool,
    /// var → (uid value expression, parent struct id when known)
    bindings: HashMap<TempId, (IRNode, Option<StructID>)>,
    /// var → parent struct value expression (for vars bound to whole-struct
    /// borrows passed into UID accessors)
    parent_bindings: HashMap<TempId, IRNode>,
}

fn resolve_uid_expr(arg: &IRNode, ctx: &LowerCtx, program: &Program) -> (IRNode, Option<StructID>) {
    match arg {
        IRNode::Field {
            struct_id,
            field_index: 0,
            ..
        } => (arg.clone(), Some(*struct_id)),
        IRNode::MutableBorrow { val_expr, .. } => match val_expr.as_ref() {
            IRNode::Field {
                struct_id,
                field_index: 0,
                ..
            } => ((**val_expr).clone(), Some(*struct_id)),
            other => (other.clone(), None),
        },
        IRNode::ReadRef(inner) => resolve_uid_expr(inner, ctx, program),
        IRNode::Var(name) => match ctx.bindings.get(name) {
            Some((expr, sid)) => (expr.clone(), *sid),
            None => (IRNode::Var(name.clone()), None),
        },
        // Cross-module UID access goes through a field accessor
        // (`public fun uid_mut(c: &mut Crate): &mut UID { &mut c.id }`);
        // inline it to the underlying `parent.id` field read.
        IRNode::Call { function, args, .. } => {
            if let Some(sid) = uid_accessor(program.functions.get(function)) {
                let parent = strip_borrow(&args[0], ctx);
                return (
                    IRNode::Field {
                        struct_id: sid,
                        field_index: 0,
                        base: Box::new(parent),
                    },
                    Some(sid),
                );
            }
            panic!(
                "world_mode: cannot resolve dynamic-field parent UID expression: call to `{}`",
                program.functions.get(function).name
            );
        }
        other => panic!(
            "world_mode: cannot resolve dynamic-field parent UID expression: {:?}",
            other
        ),
    }
}

/// A UID accessor: single-param function whose body reads field 0 of the
/// param (directly or through a `MutableBorrow`). Returns the struct id.
fn uid_accessor(func: &Function) -> Option<StructID> {
    if func.signature.parameters.len() != 1 {
        return None;
    }
    let self_ssa = &func.signature.parameters[0].ssa_value;
    let field_of_self = |node: &IRNode| -> Option<StructID> {
        if let IRNode::Field {
            struct_id,
            field_index: 0,
            base,
        } = node
        {
            if matches!(base.as_ref(), IRNode::Var(name) if name == self_ssa) {
                return Some(*struct_id);
            }
        }
        None
    };
    match &func.body {
        IRNode::MutableBorrow { val_expr, .. } => field_of_self(val_expr),
        other => field_of_self(other),
    }
}

/// Strip reference wrappers off an accessor argument to reach the parent
/// struct value expression.
fn strip_borrow(arg: &IRNode, ctx: &LowerCtx) -> IRNode {
    match arg {
        IRNode::MutableBorrow { val_expr, .. } => (**val_expr).clone(),
        IRNode::ReadRef(inner) => strip_borrow(inner, ctx),
        IRNode::Var(name) => match ctx.parent_bindings.get(name) {
            Some(expr) => expr.clone(),
            None => IRNode::Var(name.clone()),
        },
        other => other.clone(),
    }
}

/// A type with no `TypeParameter` anywhere.
fn type_is_concrete(ty: &Type) -> bool {
    match ty {
        Type::TypeParameter(_) => false,
        Type::Vector(i) | Type::Reference(i) | Type::Option(i) => type_is_concrete(i),
        Type::MutableReference(i, s) => type_is_concrete(i) && type_is_concrete(s),
        Type::Tuple(ts) => ts.iter().all(type_is_concrete),
        Type::Struct { type_args, .. } => type_args.iter().all(type_is_concrete),
        _ => true,
    }
}

/// Since Phase 5, state ops with GENERIC type args lower too: the enclosing
/// function gains `[HasCode TyCode T]` instance binders (recorded by
/// `compute_hascode_params`, emitted by the renderer), which is what lets the
/// Sui framework's generic container/transfer wrappers (Table & co.) lower to
/// World views. Each op type arg must have a derivable `HasCode` instance:
/// a bare type parameter, a fully concrete type, or a WRAPPING struct
/// `F<..>` whose every type-arg is itself HasCode-derivable (the universe
/// renderer emits the parametric instance `[HasCode U T] → HasCode U (F T)`
/// for each such wrapping shape). A composite that is NOT a struct wrapping
/// — e.g. `vector<T>` — has no derivable instance and is a hard error (no
/// silent slot-mode fallback in world-mode).
fn op_type_arg_has_code(ty: &Type) -> bool {
    match ty {
        Type::TypeParameter(_) => true,
        _ if type_is_concrete(ty) => true,
        Type::Struct { type_args, .. } => type_args.iter().all(op_type_arg_has_code),
        _ => false,
    }
}

fn check_op_type_arg(ty: &Type, fn_name: &str) {
    if op_type_arg_has_code(ty) {
        return;
    }
    panic!(
        "world_mode: state op in `{}` has a composite generic type arg {:?} — \
         no HasCode instance is derivable for it (bare type parameters, \
         concrete types, and wrapping structs over them only)",
        fn_name, ty
    );
}

fn peel_refs(ty: &Type) -> &Type {
    match ty {
        Type::Reference(inner) => peel_refs(inner),
        Type::MutableReference(inner, _) => peel_refs(inner),
        other => other,
    }
}

fn is_uid_struct(program: &Program, sid: StructID) -> bool {
    program.structs.has(sid) && program.structs.get(&sid).qualified_name == "object::UID"
}

/// A `key`-ability object shape: first field is a `UID`.
fn struct_has_uid_head(program: &Program, sid: StructID) -> bool {
    if !program.structs.has(sid) {
        return false;
    }
    let s = program.structs.get(&sid);
    match s.fields.first() {
        Some(f) => match peel_refs(&f.field_type) {
            Type::Struct { struct_id, .. } => is_uid_struct(program, *struct_id),
            _ => false,
        },
        None => false,
    }
}

fn abort_missing_field() -> IRNode {
    IRNode::Abort {
        code: Some(Box::new(IRNode::Const(crate::data::ir::Const::UInt {
            bits: 64,
            value: ethnum::U256::from(E_FIELD_DOES_NOT_EXIST),
        }))),
    }
}

/// `match World.getDf K V __world uid k with | some __wdf => __wdf | none =>
/// abort EFieldDoesNotExist` — the honest typed read.
/// Whether a df op's VALUE type (the second `[K, V]` type arg) is the
/// `bag::Bag` struct — the trigger to route through the structural bag views.
fn value_is_bag(type_args: &[Type], bag_struct_id: Option<StructID>) -> bool {
    match (type_args.get(1), bag_struct_id) {
        (Some(Type::Struct { struct_id, .. }), Some(bag)) => *struct_id == bag,
        _ => false,
    }
}

fn typed_read(world: &WorldFunctions, type_args: Vec<Type>, uid: IRNode, key: IRNode) -> IRNode {
    bag_or_typed_read(world, type_args, uid, key, None)
}

/// `typed_read`, but routes to `getDfBag` (single `K` type arg, no `HasCode` on
/// the value) when the value type is a bag.
fn bag_or_typed_read(
    world: &WorldFunctions,
    type_args: Vec<Type>,
    uid: IRNode,
    key: IRNode,
    bag_struct_id: Option<StructID>,
) -> IRNode {
    let is_bag = value_is_bag(&type_args, bag_struct_id);
    let (function, type_args) = if is_bag {
        (world.get_df_bag, vec![type_args[0].clone()])
    } else {
        (world.get_df, type_args)
    };
    let binding: TempId = Rc::from("__wdf");
    IRNode::MatchOption {
        scrutinee: Box::new(IRNode::Call {
            function,
            type_args,
            args: vec![IRNode::Var(world_var()), uid, key],
        }),
        binding: binding.clone(),
        some_branch: Box::new(IRNode::Var(binding)),
        none_branch: Box::new(abort_missing_field()),
    }
}

/// Rebind sequence `let __world := <call>; <rest>`, preserving a non-trivial
/// original pattern as a unit binding.
fn world_rebind(call: IRNode, orig_pattern: Vec<TempId>, body: IRNode) -> IRNode {
    let inner = if orig_pattern.is_empty() || orig_pattern.iter().all(|p| &**p == "_") {
        body
    } else {
        IRNode::Let {
            pattern: orig_pattern,
            value: Box::new(IRNode::Tuple(vec![])),
            body: Box::new(body),
        }
    };
    IRNode::Let {
        pattern: vec![world_var()],
        value: Box::new(call),
        body: Box::new(inner),
    }
}

fn lower_node(node: IRNode, ctx: &mut LowerCtx, program: &Program) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // Track UID-shaped bindings so `Var` args resolve.
            if pattern.len() == 1 {
                match value.as_ref() {
                    IRNode::Field {
                        struct_id,
                        field_index: 0,
                        ..
                    } => {
                        ctx.bindings
                            .insert(pattern[0].clone(), ((*value).clone(), Some(*struct_id)));
                    }
                    IRNode::MutableBorrow { val_expr, .. } => {
                        if let IRNode::Field {
                            struct_id,
                            field_index: 0,
                            ..
                        } = val_expr.as_ref()
                        {
                            ctx.bindings.insert(
                                pattern[0].clone(),
                                ((**val_expr).clone(), Some(*struct_id)),
                            );
                        } else {
                            // Whole-struct borrow (feeds UID accessors).
                            ctx.parent_bindings
                                .insert(pattern[0].clone(), (**val_expr).clone());
                        }
                    }
                    IRNode::Var(other) => {
                        if let Some(entry) = ctx.bindings.get(other).cloned() {
                            ctx.bindings.insert(pattern[0].clone(), entry);
                        }
                        if let Some(entry) = ctx.parent_bindings.get(other).cloned() {
                            ctx.parent_bindings.insert(pattern[0].clone(), entry);
                        }
                    }
                    IRNode::Call { function, args, .. } => {
                        if let Some(sid) = uid_accessor(program.functions.get(function)) {
                            if !args.is_empty() {
                                let parent = strip_borrow(&args[0], ctx);
                                ctx.bindings.insert(
                                    pattern[0].clone(),
                                    (
                                        IRNode::Field {
                                            struct_id: sid,
                                            field_index: 0,
                                            base: Box::new(parent),
                                        },
                                        Some(sid),
                                    ),
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }

            if let IRNode::Call {
                function,
                type_args,
                args,
            } = value.as_ref()
            {
                if let Some(&op) = ctx.ops.get(function) {
                    let skip = matches!(op, StateOp::BorrowUid | StateOp::ObjectId)
                        && !ctx.lower_object_ids;
                    if !skip {
                        for t in type_args {
                            check_op_type_arg(t, &ctx.fn_name);
                        }
                        return lower_op_let(
                            op,
                            pattern,
                            type_args.clone(),
                            args.clone(),
                            *body,
                            ctx,
                            program,
                        );
                    }
                }
            }

            IRNode::Let {
                pattern,
                value: Box::new(lower_node(*value, ctx, program)),
                body: Box::new(lower_node(*body, ctx, program)),
            }
        }
        IRNode::Call {
            function,
            type_args,
            args,
        } => {
            if let Some(&op) = ctx.ops.get(&function) {
                for t in &type_args {
                    check_op_type_arg(t, &ctx.fn_name);
                }
                // Bare-call (sequencing/read) position: only the pure read
                // ops can be lowered in place; effectful ops must sit at a
                // Let so the `__world` rebind has a binding position.
                match op {
                    StateOp::DfExists => {
                        ctx.uses_world = true;
                        let (uid, _) = resolve_uid_expr(&args[0], ctx, program);
                        return IRNode::Call {
                            function: ctx.world.has_df,
                            type_args: vec![type_args[0].clone()],
                            args: vec![IRNode::Var(world_var()), uid, args[1].clone()],
                        };
                    }
                    StateOp::DfExistsWithType => {
                        ctx.uses_world = true;
                        let (uid, _) = resolve_uid_expr(&args[0], ctx, program);
                        return typed_is_some(ctx.world, &type_args, uid, args[1].clone());
                    }
                    StateOp::DfBorrow => {
                        ctx.uses_world = true;
                        let (uid, _) = resolve_uid_expr(&args[0], ctx, program);
                        return typed_read(ctx.world, type_args, uid, args[1].clone());
                    }
                    StateOp::BorrowUid | StateOp::ObjectId if ctx.lower_object_ids => {
                        let obj = lower_node(args[0].clone(), ctx, program);
                        return object_id_projection(op, &type_args, obj, ctx, program);
                    }
                    StateOp::BorrowUid | StateOp::ObjectId => {
                        return IRNode::Call {
                            function,
                            type_args,
                            args: args
                                .into_iter()
                                .map(|a| lower_node(a, ctx, program))
                                .collect(),
                        };
                    }
                    other => panic!(
                        "world_mode: state op {:?} at a non-Let position is unsupported",
                        other
                    ),
                }
            }
            IRNode::Call {
                function,
                type_args,
                args: args
                    .into_iter()
                    .map(|a| lower_node(a, ctx, program))
                    .collect(),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(lower_node(*cond, ctx, program)),
            then_branch: Box::new(lower_node(*then_branch, ctx, program)),
            else_branch: Box::new(lower_node(*else_branch, ctx, program)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee: Box::new(lower_node(*scrutinee, ctx, program)),
            cases: cases
                .into_iter()
                .map(|(tag, binds, body)| (tag, binds, lower_node(body, ctx, program)))
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => IRNode::MatchOption {
            scrutinee: Box::new(lower_node(*scrutinee, ctx, program)),
            binding,
            some_branch: Box::new(lower_node(*some_branch, ctx, program)),
            none_branch: Box::new(lower_node(*none_branch, ctx, program)),
        },
        other => other,
    }
}

/// `match World.getDf K V __world uid k with | some _ => true | none => false`
/// — the honest typed existence check for `exists_with_type`.
/// `exists_with_type` lowers to the `hasDfTyped` native (an `Option.isSome`
/// wrapper over the typed read), NOT to a `match` over `getDf`: a `match`
/// scrutinizing the typed read inside an `@[reducible]` def wedges Lean's
/// whnf during `Decidable` synthesis at CALL SITES (`let t := contains …;
/// if t then …` gets a stuck `Decidable (t = true)`), while the plain
/// applicative shape unfolds cleanly.
fn typed_is_some(world: &WorldFunctions, type_args: &[Type], uid: IRNode, key: IRNode) -> IRNode {
    IRNode::Call {
        function: world.has_df_typed,
        type_args: type_args.to_vec(),
        args: vec![IRNode::Var(world_var()), uid, key],
    }
}

/// `object::borrow_uid` / `object::id` — the VM natives the id-family
/// accessors bottom out in; the stubs return `default` (uid 0), so ALL object
/// ids alias 0 and id-keyed tables collapse to one row (staking_pool_mappings
/// routed withdrawals to the wrong validator). Project the UID from the
/// VALUE, exactly like the transfer keying: concrete `key` struct → its
/// field-0 UID; generic `T` → memberUid (`[HasCode TyCode T]`-threaded
/// `Universe.uidNat` projection). For `object::id`, project the inner `ID`
/// off the UID. Only in non-framework modules (`ctx.lower_object_ids`):
/// lowering inside Sui/MoveStdlib would import Generated.World from files it
/// transitively imports (cycle).
fn object_id_projection(
    op: StateOp,
    type_args: &[Type],
    obj: IRNode,
    ctx: &LowerCtx,
    program: &Program,
) -> IRNode {
    let obj_ty = type_args
        .first()
        .expect("object id projection must carry its object type arg");
    let uid = match obj_ty {
        Type::Struct { struct_id, .. } => {
            let s = program.structs.get(struct_id);
            assert!(
                !s.fields.is_empty(),
                "world_mode: object-id target struct {} has no UID field",
                s.name
            );
            IRNode::Field {
                struct_id: *struct_id,
                field_index: 0,
                base: Box::new(obj),
            }
        }
        _ => IRNode::Call {
            function: ctx.world.member_uid,
            type_args: vec![obj_ty.clone()],
            args: vec![obj],
        },
    };
    if op == StateOp::ObjectId {
        let uid_sid = ctx
            .uid_struct_id
            .expect("world_mode: object::id lowered but object::UID struct not found");
        IRNode::Field {
            struct_id: uid_sid,
            field_index: 0,
            base: Box::new(uid),
        }
    } else {
        uid
    }
}

#[allow(clippy::too_many_arguments)]
fn lower_op_let(
    op: StateOp,
    pattern: Vec<TempId>,
    type_args: Vec<Type>,
    args: Vec<IRNode>,
    body: IRNode,
    ctx: &mut LowerCtx,
    program: &Program,
) -> IRNode {
    // Pure id-projection reads — handled before the `uses_world` mark so they
    // don't force a `__world` param.
    if matches!(op, StateOp::BorrowUid | StateOp::ObjectId) {
        let obj = lower_node(args[0].clone(), ctx, program);
        let value = object_id_projection(op, &type_args, obj, ctx, program);
        return IRNode::Let {
            pattern,
            value: Box::new(value),
            body: Box::new(lower_node(body, ctx, program)),
        };
    }
    ctx.uses_world = true;
    match op {
        StateOp::DfAdd => {
            let (uid, _) = resolve_uid_expr(&args[0], ctx, program);
            assert!(args.len() >= 3, "dynamic_field::add needs 3 args");
            let is_bag = value_is_bag(&type_args, ctx.bag_struct_id);
            let (function, type_args) = if is_bag {
                (ctx.world.set_df_bag, vec![type_args[0].clone()])
            } else {
                (ctx.world.set_df, type_args)
            };
            let call = IRNode::Call {
                function,
                type_args,
                args: vec![
                    IRNode::Var(world_var()),
                    uid,
                    args[1].clone(),
                    args[2].clone(),
                ],
            };
            world_rebind(call, pattern, lower_node(body, ctx, program))
        }
        StateOp::DfRemove => {
            let (uid, _) = resolve_uid_expr(&args[0], ctx, program);
            assert!(args.len() >= 2, "dynamic_field::remove needs 2 args");
            let key = args[1].clone();
            // The value slot of the original pattern (remove returns V).
            assert!(
                pattern.len() <= 2,
                "world_mode: unexpected remove result pattern {:?}",
                pattern
            );
            let value_pat: Vec<TempId> = pattern.first().cloned().into_iter().collect();
            let is_bag = value_is_bag(&type_args, ctx.bag_struct_id);
            let read = bag_or_typed_read(
                ctx.world,
                type_args.clone(),
                uid.clone(),
                key.clone(),
                ctx.bag_struct_id,
            );
            let (erase_fn, erase_type_args) = if is_bag {
                (ctx.world.erase_df_bag, vec![type_args[0].clone()])
            } else {
                (ctx.world.erase_df, type_args)
            };
            let erase = IRNode::Call {
                function: erase_fn,
                type_args: erase_type_args,
                args: vec![IRNode::Var(world_var()), uid, key],
            };
            IRNode::Let {
                pattern: value_pat,
                value: Box::new(read),
                body: Box::new(IRNode::Let {
                    pattern: vec![world_var()],
                    value: Box::new(erase),
                    body: Box::new(lower_node(body, ctx, program)),
                }),
            }
        }
        StateOp::DfBorrow => {
            let (uid, _) = resolve_uid_expr(&args[0], ctx, program);
            let read = bag_or_typed_read(
                ctx.world,
                type_args,
                uid,
                args[1].clone(),
                ctx.bag_struct_id,
            );
            IRNode::Let {
                pattern,
                value: Box::new(read),
                body: Box::new(lower_node(body, ctx, program)),
            }
        }
        StateOp::DfBorrowMut => {
            let (uid, parent_sid) = resolve_uid_expr(&args[0], ctx, program);
            let key = args[1].clone();
            let is_bag = value_is_bag(&type_args, ctx.bag_struct_id);
            let read = bag_or_typed_read(
                ctx.world,
                type_args.clone(),
                uid.clone(),
                key.clone(),
                ctx.bag_struct_id,
            );
            let reconstruct_param: TempId = Rc::from("__v");
            let (set_fn, set_type_args) = if is_bag {
                (ctx.world.set_df_bag, vec![type_args[0].clone()])
            } else {
                (ctx.world.set_df, type_args)
            };
            let reconstruct = IRNode::Call {
                function: set_fn,
                type_args: set_type_args,
                args: vec![
                    IRNode::Var(world_var()),
                    uid,
                    key,
                    IRNode::Var(reconstruct_param.clone()),
                ],
            };
            let node_var = pattern
                .first()
                .cloned()
                .expect("dynamic_field::borrow_mut result must be bound");
            let mut_ret_var = pattern.get(1).cloned();
            // Strip the no-op UID reconstruction (`let parent := { parent
            // with id := __mut_ret }`) exactly like
            // `rewrite_df_borrow_mut_pre_threading` does.
            let stripped = match (&mut_ret_var, parent_sid) {
                (Some(mr), Some(sid)) => strip_uid_reconstruction(body, mr, sid),
                _ => body,
            };
            IRNode::Let {
                pattern: vec![node_var],
                value: Box::new(IRNode::MutableBorrow {
                    val_expr: Box::new(read),
                    reconstruct_param,
                    reconstruct_expr: Box::new(reconstruct),
                    state_type: ctx.world.world_type(),
                }),
                body: Box::new(lower_node(stripped, ctx, program)),
            }
        }
        StateOp::DfExists => {
            let (uid, _) = resolve_uid_expr(&args[0], ctx, program);
            let call = IRNode::Call {
                function: ctx.world.has_df,
                type_args: vec![type_args[0].clone()],
                args: vec![IRNode::Var(world_var()), uid, args[1].clone()],
            };
            IRNode::Let {
                pattern,
                value: Box::new(call),
                body: Box::new(lower_node(body, ctx, program)),
            }
        }
        StateOp::DfExistsWithType => {
            let (uid, _) = resolve_uid_expr(&args[0], ctx, program);
            let check = if value_is_bag(&type_args, ctx.bag_struct_id) {
                IRNode::Call {
                    function: ctx.world.has_df_bag,
                    type_args: vec![type_args[0].clone()],
                    args: vec![IRNode::Var(world_var()), uid, args[1].clone()],
                }
            } else {
                typed_is_some(ctx.world, &type_args, uid, args[1].clone())
            };
            IRNode::Let {
                pattern,
                value: Box::new(check),
                body: Box::new(lower_node(body, ctx, program)),
            }
        }
        StateOp::TransferOwned | StateOp::TransferShared | StateOp::TransferFrozen => {
            let obj = args[0].clone();
            let obj_ty = type_args
                .first()
                .expect("transfer op must carry its object type arg");
            // Concrete `key` struct → project its UID field structurally.
            // GENERIC object type (`transfer::*` / `test_scenario::return_*`
            // over a bare `T: key`) → route through `World.memberUid`, which
            // uses the `[HasCode TyCode T]`-threaded `Universe.uidNat`
            // projection. `compute_hascode_params` threads the instance binder
            // because `member_uid` is a World native.
            let uid = match obj_ty {
                Type::Struct { struct_id, .. } => {
                    let s = program.structs.get(struct_id);
                    assert!(
                        !s.fields.is_empty(),
                        "world_mode: transferred struct {} has no UID field",
                        s.name
                    );
                    IRNode::Field {
                        struct_id: *struct_id,
                        field_index: 0,
                        base: Box::new(obj.clone()),
                    }
                }
                _ => IRNode::Call {
                    function: ctx.world.member_uid,
                    type_args: vec![obj_ty.clone()],
                    args: vec![obj.clone()],
                },
            };
            let (function, mut call_args) = match op {
                StateOp::TransferOwned => {
                    assert!(args.len() >= 2, "transfer needs a recipient arg");
                    (
                        ctx.world.put_owned,
                        vec![IRNode::Var(world_var()), obj, args[1].clone()],
                    )
                }
                StateOp::TransferShared => {
                    (ctx.world.put_shared, vec![IRNode::Var(world_var()), obj])
                }
                _ => (ctx.world.put_frozen, vec![IRNode::Var(world_var()), obj]),
            };
            call_args.push(uid);
            let call = IRNode::Call {
                function,
                type_args,
                args: call_args,
            };
            world_rebind(call, pattern, lower_node(body, ctx, program))
        }
        StateOp::EventEmit => {
            let call = IRNode::Call {
                function: ctx.world.emit_event,
                type_args,
                args: vec![IRNode::Var(world_var()), args[0].clone()],
            };
            world_rebind(call, pattern, lower_node(body, ctx, program))
        }
        // test_scenario inventory READS (world unchanged): bind the result to
        // the original pattern and pass the threaded `__world` as first arg.
        // `ids_for_address T account` / `most_recent_id_for_address T account`.
        StateOp::IdsForAddress | StateOp::MostRecentIdForAddress => {
            let function = if op == StateOp::IdsForAddress {
                ctx.world.ids_for_address
            } else {
                ctx.world.most_recent_id_for_address
            };
            IRNode::Let {
                pattern,
                value: Box::new(IRNode::Call {
                    function,
                    type_args,
                    args: vec![IRNode::Var(world_var()), args[0].clone()],
                }),
                body: Box::new(lower_node(body, ctx, program)),
            }
        }
        // `was_taken_from_address account id` (no type arg, world unchanged).
        StateOp::WasTakenFromAddress => IRNode::Let {
            pattern,
            value: Box::new(IRNode::Call {
                function: ctx.world.was_taken_from_address,
                type_args: vec![],
                args: vec![IRNode::Var(world_var()), args[0].clone(), args[1].clone()],
            }),
            body: Box::new(lower_node(body, ctx, program)),
        },
        // `take_from_address_by_id T scenario account id` — removes the object
        // from the store (world CHANGES). The World view returns `(T × World)`;
        // destructure into the original result binding plus the rebound
        // `__world`. Only the `id` arg (index 2) is used.
        StateOp::TakeFromAddressById => {
            let result: TempId = pattern.first().cloned().unwrap_or_else(|| Rc::from("_"));
            let id_arg = args.get(2).cloned().unwrap_or_else(|| args[0].clone());
            IRNode::Let {
                pattern: vec![result, world_var()],
                value: Box::new(IRNode::Call {
                    function: ctx.world.take_from_address_by_id,
                    type_args,
                    args: vec![IRNode::Var(world_var()), id_arg],
                }),
                body: Box::new(lower_node(body, ctx, program)),
            }
        }
        // `most_recent_id_shared T` (nullary Move native; world unchanged).
        StateOp::MostRecentIdShared => IRNode::Let {
            pattern,
            value: Box::new(IRNode::Call {
                function: ctx.world.most_recent_id_shared,
                type_args,
                args: vec![IRNode::Var(world_var())],
            }),
            body: Box::new(lower_node(body, ctx, program)),
        },
        // `was_taken_shared id` (no type arg, world unchanged).
        StateOp::WasTakenShared => IRNode::Let {
            pattern,
            value: Box::new(IRNode::Call {
                function: ctx.world.was_taken_shared,
                type_args: vec![],
                args: vec![IRNode::Var(world_var()), args[0].clone()],
            }),
            body: Box::new(lower_node(body, ctx, program)),
        },
        StateOp::BorrowUid | StateOp::ObjectId => {
            unreachable!("object-id projections are handled before the uses_world mark")
        }
        // `take_shared_by_id T scenario id` — removes the object from the
        // store (world CHANGES); destructure `(T × World)`. Only the `id`
        // arg (index 1) is used.
        StateOp::TakeSharedById => {
            let result: TempId = pattern.first().cloned().unwrap_or_else(|| Rc::from("_"));
            let id_arg = args.get(1).cloned().unwrap_or_else(|| args[0].clone());
            IRNode::Let {
                pattern: vec![result, world_var()],
                value: Box::new(IRNode::Call {
                    function: ctx.world.take_shared_by_id,
                    type_args,
                    args: vec![IRNode::Var(world_var()), id_arg],
                }),
                body: Box::new(lower_node(body, ctx, program)),
            }
        }
        // `test_scenario::end_transaction` — reads and resets the per-tx
        // user-event counter (world CHANGES); pack the rest of
        // `TransactionEffects` from empty/default field values (the world
        // model does not track created/written/deleted/transferred/shared/
        // frozen object sets).
        StateOp::EndTransaction => {
            let count: TempId = Rc::from("__tx_events");
            let effects_sid = program
                .structs
                .iter()
                .find(|(_, s)| s.qualified_name == "test_scenario::TransactionEffects")
                .map(|(id, _)| *id)
                .expect("world_mode: test_scenario::TransactionEffects struct not found");
            let effects = program.structs.get(&effects_sid);
            let fields: Vec<IRNode> = effects
                .fields
                .iter()
                .map(|f| {
                    if f.name == "num_user_events" {
                        IRNode::Var(count.clone())
                    } else {
                        zero_value_for_effects_field(program, &f.field_type, &ctx.fn_name)
                    }
                })
                .collect();
            IRNode::Let {
                pattern: vec![count, world_var()],
                value: Box::new(IRNode::Call {
                    function: ctx.world.take_tx_user_events,
                    type_args: vec![],
                    args: vec![IRNode::Var(world_var())],
                }),
                body: Box::new(IRNode::Let {
                    pattern,
                    value: Box::new(IRNode::Pack {
                        struct_id: effects_sid,
                        type_args: vec![],
                        fields,
                        variant_index: None,
                    }),
                    body: Box::new(lower_node(body, ctx, program)),
                }),
            }
        }
    }
}

/// A zero/empty value for a `TransactionEffects` field other than
/// `num_user_events` — the world model doesn't track these sets, so every
/// `end_transaction` reports them empty. `assert!`s on anything unexpected
/// rather than silently defaulting (no-fallbacks rule).
fn zero_value_for_effects_field(program: &Program, ty: &Type, fn_name: &str) -> IRNode {
    match ty {
        Type::Vector(elem) => IRNode::Const(Const::Vector {
            elem_type: (**elem).clone(),
            elems: vec![],
        }),
        Type::Struct {
            struct_id,
            type_args,
        } if program.structs.get(struct_id).qualified_name == "vec_map::VecMap" => {
            let empty_fn = program
                .functions
                .iter()
                .find(|(_, f)| {
                    !f.is_native
                        && program.modules.get(&f.module_id).name == "vec_map"
                        && f.name == "empty"
                })
                .map(|(id, _)| id)
                .expect("world_mode: end_transaction needs vec_map::empty but it wasn't found");
            IRNode::Call {
                function: empty_fn,
                type_args: type_args.clone(),
                args: vec![],
            }
        }
        other => panic!(
            "world_mode: end_transaction's TransactionEffects has an unsupported field type {:?} in `{}` — \
             no zero-value construction is registered for it",
            other, fn_name
        ),
    }
}

/// Strip `let parent := { parent with id := mut_ret_var }` (the no-op UID
/// reconstruction left after replacing a `borrow_mut` call). Same logic as
/// `dynamic_field_rewriting::strip_uid_reconstruction`.
fn strip_uid_reconstruction(node: IRNode, mut_ret_var: &TempId, target_sid: StructID) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let is_uid_recon = matches!(
                value.as_ref(),
                IRNode::UpdateField { struct_id, field_index: 0, value: v, .. }
                    if *struct_id == target_sid
                        && matches!(v.as_ref(), IRNode::Var(name) if name == mut_ret_var)
            );
            if is_uid_recon {
                strip_uid_reconstruction(*body, mut_ret_var, target_sid)
            } else {
                IRNode::Let {
                    pattern,
                    value,
                    body: Box::new(strip_uid_reconstruction(*body, mut_ret_var, target_sid)),
                }
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(strip_uid_reconstruction(
                *then_branch,
                mut_ret_var,
                target_sid,
            )),
            else_branch: Box::new(strip_uid_reconstruction(
                *else_branch,
                mut_ret_var,
                target_sid,
            )),
        },
        other => other,
    }
}

// ============================================================================
// HasCode-requirement analysis (unified-backend design Phase 5).
// ============================================================================

/// Compute, for every function, the set of its type-parameter indices that
/// flow into a `World.*` typed-view op (directly or through calls to other
/// generic functions). The renderer emits `[HasCode TyCode <tp>]` instance
/// binders for them, which is what makes GENERIC state ops (the Sui
/// framework's Table/container wrappers) renderable in world-mode.
///
/// Runs late in finalize — after every derived face (`.aborts`, spec
/// companions, bundle segments) exists — because requirements are recomputed
/// from final bodies, not propagated through derivation. Inert unless
/// `world_mode` seeded `Program::world_functions`.
pub fn compute_hascode_params(program: &mut Program) {
    let Some(world) = program.world_functions.clone() else {
        return;
    };
    let native_ids: std::collections::BTreeSet<FunctionID> = world.all_ids().into_iter().collect();

    fn param_indices(ty: &Type, out: &mut std::collections::BTreeSet<u16>) {
        match ty {
            Type::TypeParameter(i) => {
                out.insert(*i);
            }
            Type::Vector(i) | Type::Reference(i) | Type::Option(i) => param_indices(i, out),
            Type::MutableReference(i, s) => {
                param_indices(i, out);
                param_indices(s, out);
            }
            Type::Tuple(ts) => ts.iter().for_each(|t| param_indices(t, out)),
            Type::Struct { type_args, .. } => type_args.iter().for_each(|t| param_indices(t, out)),
            _ => {}
        }
    }

    let fn_ids: Vec<FunctionID> = program.functions.iter_ids().collect();
    let mut req: BTreeMap<FunctionID, std::collections::BTreeSet<u16>> = BTreeMap::new();
    loop {
        let mut changed = false;
        for &fid in &fn_ids {
            let f = program.functions.get(&fid);
            if f.is_native || f.signature.type_params.is_empty() {
                continue;
            }
            let mut need = req.get(&fid).cloned().unwrap_or_default();
            let before = need.len();
            for node in f.body.iter() {
                let IRNode::Call {
                    function,
                    type_args,
                    ..
                } = node
                else {
                    continue;
                };
                if native_ids.contains(function) {
                    // Every World-native type arg is HasCode-constrained.
                    for t in type_args {
                        param_indices(t, &mut need);
                    }
                } else if let Some(callee_req) = req.get(function) {
                    for &i in callee_req {
                        if let Some(t) = type_args.get(i as usize) {
                            let mut idx = std::collections::BTreeSet::new();
                            param_indices(t, &mut idx);
                            // A bare param threads its own binder; a wrapping
                            // composite `F<T>` threads binders for its inner
                            // params (the parametric instance derives
                            // `HasCode (F T)` from `HasCode T`). A non-wrapping
                            // composite (e.g. `vector<T>`) has no instance.
                            if !idx.is_empty() {
                                assert!(
                                    op_type_arg_has_code(t),
                                    "world_mode: `{}` instantiates HasCode-constrained type \
                                     param #{} of `{}` with composite generic type {:?}",
                                    f.name,
                                    i,
                                    program.functions.get(function).name,
                                    t
                                );
                                need.extend(idx);
                            }
                        }
                    }
                }
            }
            if need.len() != before || (!need.is_empty() && !req.contains_key(&fid)) {
                req.insert(fid, need);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    req.retain(|_, s| !s.is_empty());
    program.fn_hascode_params = req;
}

/// Bag-universe (`BagU`) analog of [`compute_hascode_params`]. A `bag` /
/// `object_bag` op over a generic value type (`Bag.borrow (Balance T)`) needs
/// `[HasCode BagU (Balance T)]`, which the `Generated/BagUInterp` wrapper
/// instance reduces to `[HasCode BagU T]` in scope. Seed each function's need
/// from the type-params flowing into a bag op in its body, then propagate to
/// fixpoint up the call graph (a caller passing its own param to a
/// bag-constrained callee param inherits the need). The renderer emits a
/// `[HasCode BagU <tp>]` binder for each recorded index. This is the `BagU`
/// half of the DfU/BagU split — separate from the World/`TyCode` universe, so a
/// param may end up in both `fn_hascode_params` and `fn_bagu_params`.
pub fn compute_bagu_params(program: &mut Program) {
    let bag_module_ids: std::collections::BTreeSet<usize> = program
        .modules
        .iter()
        .filter(|(_, m)| {
            let base = m.name.trim_end_matches("_specs").trim_end_matches("_spec");
            matches!(base, "bag" | "object_bag")
        })
        .map(|(id, _)| *id)
        .collect();
    let type_name_module_ids: std::collections::BTreeSet<usize> = program
        .modules
        .iter()
        .filter(|(_, m)| {
            let base = m.name.trim_end_matches("_specs").trim_end_matches("_spec");
            base == "type_name"
        })
        .map(|(id, _)| *id)
        .collect();
    // Bag ops and the `type_name::get`-family both index the closed type
    // universe: a bag stores `(K, V)` heterogeneously, and `type_name::get<T>`
    // derives its FQN from `T`'s code (`Universe.typeName`). Both therefore need
    // `[HasCode BagU T]` on the type params they consume.
    let bag_ids: std::collections::BTreeSet<FunctionID> = program
        .functions
        .iter()
        .filter(|(_, f)| {
            bag_module_ids.contains(&f.module_id)
                || (type_name_module_ids.contains(&f.module_id)
                    && matches!(
                        f.name.as_str(),
                        "get" | "with_defining_ids" | "get_with_original_ids" | "with_original_ids"
                    ))
        })
        .map(|(id, _)| id)
        .collect();
    if bag_ids.is_empty() {
        return;
    }

    fn param_indices(ty: &Type, out: &mut std::collections::BTreeSet<u16>) {
        match ty {
            Type::TypeParameter(n) => {
                out.insert(*n);
            }
            Type::Vector(i) | Type::Reference(i) | Type::Option(i) => param_indices(i, out),
            Type::MutableReference(i, s) => {
                param_indices(i, out);
                param_indices(s, out);
            }
            Type::Tuple(ts) => ts.iter().for_each(|t| param_indices(t, out)),
            Type::Struct { type_args, .. } => type_args.iter().for_each(|t| param_indices(t, out)),
            _ => {}
        }
    }

    let fn_ids: Vec<FunctionID> = program.functions.iter_ids().collect();
    let mut req: BTreeMap<FunctionID, std::collections::BTreeSet<u16>> = BTreeMap::new();
    loop {
        let mut changed = false;
        for &fid in &fn_ids {
            let f = program.functions.get(&fid);
            if f.is_native || f.signature.type_params.is_empty() {
                continue;
            }
            let mut need = req.get(&fid).cloned().unwrap_or_default();
            let before = need.len();
            for node in f.body.iter() {
                let IRNode::Call {
                    function,
                    type_args,
                    ..
                } = node
                else {
                    continue;
                };
                if bag_ids.contains(function) {
                    for t in type_args {
                        param_indices(t, &mut need);
                    }
                } else if let Some(callee_req) = req.get(function) {
                    for &i in callee_req {
                        if let Some(t) = type_args.get(i as usize) {
                            param_indices(t, &mut need);
                        }
                    }
                }
            }
            if need.len() != before || (!need.is_empty() && !req.contains_key(&fid)) {
                req.insert(fid, need);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    req.retain(|_, s| !s.is_empty());
    program.fn_bagu_params = req;
}

// ============================================================================
// Transfer-ghost retirement (world-mode): lower `ghost::global/borrow_mut`
// reads on the transfer markers (`SpecTransferAddress{,Exists}` — the `(K,V)`
// pairs seeded on `transfer`-module natives) onto the World transfer-marker
// slots (`World.transferExists` / `World.lastTransfer`, stamped by `putOwned`).
//
// Runs in `Program::finalize` BEFORE `thread_ghosts`: after the rewrite, user
// functions carry no direct ghost ops on the transfer markers, and their
// transfer CALLS were already lowered onto `__world` by Phase A — so the
// ghost-threading caller cone shrinks to the `transfer`/`transfer_spec`
// modules themselves (skipped by Phase A, they keep the ghost mechanism), and
// the `__ghost_*` binders disappear from world-mode user spec faces entirely.
//
// Functions the rewrite touches gain the trailing `__world : World` param if
// Phase A did not already add one, which also seeds them for Phase B.
// ============================================================================

pub fn lower_transfer_ghosts(program: &mut Program) {
    let Some(world) = program.world_functions.clone() else {
        return;
    };
    if program.ghost_native_seed.is_empty() {
        return;
    }

    // Transfer markers: `(K, V)` pairs seeded on `transfer`-module natives.
    let mut markers: Vec<(Type, Type)> = Vec::new();
    for (fid, kvs) in &program.ghost_native_seed {
        let f = program.functions.get(fid);
        let module_name = program.modules.get(&f.module_id).name.clone();
        if module_name
            .trim_end_matches("_specs")
            .trim_end_matches("_spec")
            == "transfer"
        {
            for kv in kvs {
                if !markers.contains(kv) {
                    markers.push(kv.clone());
                }
            }
        }
    }
    if markers.is_empty() {
        return;
    }

    // Ghost read-op fids (`ghost::global` / `ghost::borrow_mut`).
    let mut read_fids: Vec<FunctionID> = Vec::new();
    for (fid, func) in program.functions.iter() {
        if program.modules.get(&func.module_id).name == "ghost"
            && matches!(func.name.as_str(), "global" | "borrow_mut")
        {
            read_fids.push(fid);
        }
    }

    let world_ty = world.world_type();
    let fn_ids: Vec<FunctionID> = program.functions.iter_ids().collect();
    for fid in fn_ids {
        let func = program.functions.get(&fid);
        if func.is_native || func.module_id == world.module_id {
            continue;
        }
        // Same skip family as Phase A: the state-op modules and their spec
        // companions keep the ghost mechanism (their bodies are never
        // world-lowered).
        let module_name = program.modules.get(&func.module_id).name.clone();
        let module_base = module_name
            .trim_end_matches("_specs")
            .trim_end_matches("_spec");
        if matches!(
            module_base,
            "dynamic_field" | "transfer" | "event" | "bag" | "object_bag" | "ghost"
        ) {
            continue;
        }
        let mut rewrote = false;
        let body = std::mem::take(&mut program.functions.get_mut(fid).body);
        let body = body.map(&mut |node| match node {
            IRNode::Call {
                function,
                type_args,
                args,
            } if read_fids.contains(&function)
                && type_args.len() == 2
                && markers.contains(&(type_args[0].clone(), type_args[1].clone())) =>
            {
                rewrote = true;
                let native = match &type_args[1] {
                    Type::Bool => world.transfer_exists,
                    Type::Address => world.last_transfer,
                    other => panic!(
                        "world_mode: transfer ghost marker has unsupported value type {:?}                          (only bool / address markers lower onto World transfer slots)",
                        other
                    ),
                };
                IRNode::Call {
                    function: native,
                    type_args: vec![],
                    args: vec![IRNode::Var(world_var())],
                }
            }
            other => other,
        });
        let func = program.functions.get_mut(fid);
        func.body = body;
        if rewrote && !has_world_param(func) {
            func.signature.parameters.push(Parameter {
                name: WORLD_VAR.to_string(),
                param_type: world_ty.clone(),
                ssa_value: world_var(),
            });
        }
    }
}

// ============================================================================
// Phase B — interprocedural threading (single-marker ghost_threading clone)
// ============================================================================

#[derive(Debug, Clone)]
struct CalleeInfo {
    /// Augmented-return face: a value face whose cone (transitively) WRITES
    /// the world. Read-only threaded functions (getDf/hasDf cones) thread
    /// `__world` as a parameter only and keep their original return type, so
    /// reads stay expression-shaped (spec predicates, quantifier callbacks,
    /// `&&` chains) — the M1 reader/writer split.
    value_face: bool,
    orig_ret_unit: bool,
}

fn is_value_face(name: &str, return_type: &Type) -> bool {
    !(name.contains(".aborts")
        || name.contains(".requires")
        || name.contains(".ensures")
        || *return_type == Type::Prop)
}

fn has_world_param(func: &Function) -> bool {
    func.signature
        .parameters
        .iter()
        .any(|p| p.name == WORLD_VAR)
}

/// Caller-side rewrite for PAIR-kinded Mutables: `let p := WriteBack{child}`
/// becomes `let (p, __world) := WriteBack{child, parent: __world}` (rendered
/// `Mutable.apply child`, destructured). `w` tracks pair-kinded Mutable vars.
/// Rewrite caller-side WriteBacks on PAIR-kinded Mutables (state `(S × World)`)
/// into `(parent, __world)` destructures of `Mutable.apply`. Runs once during
/// world threading and again at the END of finalize: the threading-time run
/// rewrites value-nested occurrences that later optimize passes can revert, so
/// the fixup must have the last word over the final body shape. Idempotent.
pub fn run_pair_writeback_fixup(program: &mut Program) {
    if program.pair_mut_fns.is_empty() {
        return;
    }
    let pairs = program.pair_mut_fns.clone();
    let ids: Vec<FunctionID> = program.functions.iter_ids().collect();
    for fid in &ids {
        if program.functions.get(fid).is_native {
            continue;
        }
        let body = std::mem::take(&mut program.functions.get_mut(*fid).body);
        let mut w = std::collections::BTreeSet::new();
        program.functions.get_mut(*fid).body = fix_pair_writebacks(body, &pairs, &mut w);
    }
}

fn fix_pair_writebacks(
    node: IRNode,
    pair_fns: &std::collections::BTreeSet<FunctionID>,
    w: &mut std::collections::BTreeSet<TempId>,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // The pair-writeback can sit in a VALUE-position nested Let chain
            // (this pass runs before `optimize_all` flattens value-nested Lets
            // onto the body spine), so recurse into the value subtree with the
            // same `w`. SSA names are unique, so tracking state carried across
            // the value/body boundary stays sound; post-flattening the
            // rewritten `(parent, __world)` destructure lands on the spine.
            let value = Box::new(fix_pair_writebacks(*value, pair_fns, w));
            match value.as_ref() {
                IRNode::Call { function, .. }
                    if !pattern.is_empty() && pair_fns.contains(function) =>
                {
                    w.insert(pattern[0].clone());
                }
                IRNode::WriteRef { reference, .. } if pattern.len() == 1 => {
                    if let IRNode::Var(x) = reference.as_ref() {
                        if w.contains(x) {
                            w.insert(pattern[0].clone());
                        }
                    }
                }
                IRNode::Var(x) if pattern.len() == 1 && w.contains(x) => {
                    w.insert(pattern[0].clone());
                }
                // Post-threading bodies destructure the pair-call result
                // through tuple projections (`let __world_orig_ret :=
                // __pair….1; let t_tN := ….1`), so follow `Field`-of-tracked
                // bindings too or the end-of-finalize re-run never reaches
                // the mutref temp.
                IRNode::Field { base, .. } if pattern.len() == 1 => {
                    if let IRNode::Var(x) = base.as_ref() {
                        if w.contains(x) {
                            w.insert(pattern[0].clone());
                        }
                    }
                }
                _ => {}
            }
            if let IRNode::WriteBack { child, .. } = value.as_ref() {
                if w.contains(child) {
                    let world: TempId = Rc::from(WORLD_VAR);
                    // An empty-pattern WriteBack rebinds its `parent` by
                    // convention (renders `let parent := …`), so the parent
                    // name — not `_` — must head the destructure or the
                    // parent's updated half of the pair is dropped.
                    let (child, orig_parent) =
                        if let IRNode::WriteBack { child, parent, .. } = *value {
                            (child, parent)
                        } else {
                            unreachable!()
                        };
                    let head: TempId = pattern.first().cloned().unwrap_or(orig_parent);
                    let new_value = IRNode::WriteBack {
                        child,
                        parent: world.clone(),
                        edge: crate::data::ir::WriteBackEdge::Direct,
                    };
                    return IRNode::Let {
                        pattern: vec![head, world],
                        value: Box::new(new_value),
                        body: Box::new(fix_pair_writebacks(*body, pair_fns, w)),
                    };
                }
            }
            IRNode::Let {
                pattern,
                value,
                body: Box::new(fix_pair_writebacks(*body, pair_fns, w)),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let mut w2 = w.clone();
            IRNode::If {
                cond,
                then_branch: Box::new(fix_pair_writebacks(*then_branch, pair_fns, w)),
                else_branch: Box::new(fix_pair_writebacks(*else_branch, pair_fns, &mut w2)),
            }
        }
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(t, b, body)| {
                    let mut w2 = w.clone();
                    (t, b, fix_pair_writebacks(body, pair_fns, &mut w2))
                })
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => {
            let mut w2 = w.clone();
            IRNode::MatchOption {
                scrutinee,
                binding,
                some_branch: Box::new(fix_pair_writebacks(*some_branch, pair_fns, w)),
                none_branch: Box::new(fix_pair_writebacks(*none_branch, pair_fns, &mut w2)),
            }
        }
        other => other,
    }
}

// ============================================================================
// Heterogeneous mutable phi unification (M1). A function that returns
// `&mut T` borrowed from BOTH a value-carried location (Mutable state `S`,
// e.g. the active_validators vector inside ValidatorSet) and a World-carried
// location (Mutable state `World`, e.g. a candidates-table entry) cannot type
// its phi. Unify at `Mutable T (S × World)`: each branch tail lifts its
// Mutable with the sibling state it leaves untouched
// (`World.mutLiftWorld m self` / `World.mutLiftState m __world`), the
// function's mutref return state becomes the pair, and caller WriteBacks on
// the returned Mutable destructure `Mutable.apply m : S × World` into
// `(parent, __world)`. Runs pre-Phase-B (the struct-branch lift references
// `__world`, which Phase B is guaranteed to append — mixed functions call
// world-stated callees).

#[derive(Debug, Clone, PartialEq)]
enum MutKind {
    World,
    Struct(Type),
    Pair(Type),
}

fn mutref_state_kind(state: &Type, world_ty: &Type) -> MutKind {
    if state == world_ty {
        MutKind::World
    } else if let Type::Tuple(v) = state {
        if v.len() == 2 && &v[1] == world_ty {
            MutKind::Pair(v[0].clone())
        } else {
            MutKind::Struct(state.clone())
        }
    } else {
        MutKind::Struct(state.clone())
    }
}

fn sig_mutref(ret: &Type) -> Option<(Type, Type)> {
    match ret {
        Type::MutableReference(inner, state) => Some((*inner.clone(), *state.clone())),
        Type::Tuple(v) => v.iter().find_map(sig_mutref),
        _ => None,
    }
}

fn replace_sig_mutref_state(ret: &Type, new_state: &Type) -> Type {
    match ret {
        Type::MutableReference(inner, _) => {
            Type::MutableReference(inner.clone(), Box::new(new_state.clone()))
        }
        Type::Tuple(v) => Type::Tuple(
            v.iter()
                .map(|t| replace_sig_mutref_state(t, new_state))
                .collect(),
        ),
        other => other.clone(),
    }
}

struct PhiCtx<'a> {
    world: &'a WorldFunctions,
    world_ty: &'a Type,
    fn_kinds: &'a HashMap<FunctionID, MutKind>,
    program: &'a Program,
    fn_name: &'a str,
}

fn track_kind(
    kinds: &mut HashMap<TempId, MutKind>,
    pattern: &[TempId],
    value: &IRNode,
    ctx: &PhiCtx,
) {
    let k = match value {
        IRNode::Call { function, .. } => ctx.fn_kinds.get(function).cloned(),
        IRNode::MutableBorrow { state_type, .. } => {
            Some(mutref_state_kind(state_type, ctx.world_ty))
        }
        IRNode::MutableCompose { outer, .. } => kinds.get(outer).cloned(),
        IRNode::WriteRef { reference, .. } => {
            if let IRNode::Var(x) = reference.as_ref() {
                kinds.get(x).cloned()
            } else {
                None
            }
        }
        IRNode::Var(x) => kinds.get(x).cloned(),
        _ => None,
    };
    if let (Some(k), Some(p)) = (k, pattern.first()) {
        kinds.insert(p.clone(), k);
    }
}

/// Process a function body: returns the rewritten node plus the kinds of its
/// mutref tails. Mixed phis (a `Let` whose If/Match value has tails of both
/// World and Struct kind, or the function tail itself) are rewritten IN PLACE
/// via `rewrite_mixed_tails`, so the returned kinds are already unified.
fn process_fn_body(
    node: IRNode,
    kinds: &mut HashMap<TempId, MutKind>,
    ctx: &PhiCtx,
    inner_ty: &Type,
) -> (IRNode, Vec<MutKind>) {
    fn mixed_struct_ty(tails: &[MutKind]) -> Option<Type> {
        let has_worldish = tails
            .iter()
            .any(|k| matches!(k, MutKind::World | MutKind::Pair(_)));
        let structs: Vec<&Type> = tails
            .iter()
            .filter_map(|k| match k {
                MutKind::Struct(t) => Some(t),
                _ => None,
            })
            .collect();
        if has_worldish && !structs.is_empty() {
            Some(structs[0].clone())
        } else {
            None
        }
    }
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let value = *value;
            let new_value = if matches!(
                value,
                IRNode::If { .. } | IRNode::Match { .. } | IRNode::MatchOption { .. }
            ) {
                let mut snap = kinds.clone();
                let (v2, vkinds) = process_fn_body(value, &mut snap, ctx, inner_ty);
                let v3 = if let Some(s_ty) = mixed_struct_ty(&vkinds) {
                    let mut snap2 = kinds.clone();
                    let out = rewrite_mixed_tails(v2, &mut snap2, ctx, inner_ty, &s_ty);
                    if let Some(p) = pattern.first() {
                        kinds.insert(p.clone(), MutKind::Pair(s_ty.clone()));
                    }
                    eprintln!(
                        "world_mode: unified heterogeneous mutable phi (let-bound) in `{}`",
                        ctx.fn_name
                    );
                    out
                } else {
                    let uniform = vkinds.first().cloned();
                    if let (Some(k), Some(p)) = (uniform, pattern.first()) {
                        if vkinds.iter().all(|x| *x == k) {
                            kinds.insert(p.clone(), k);
                        }
                    }
                    v2
                };
                v3
            } else {
                track_kind(kinds, &pattern, &value, ctx);
                value
            };
            let (b2, bk) = process_fn_body(*body, kinds, ctx, inner_ty);
            (
                IRNode::Let {
                    pattern,
                    value: Box::new(new_value),
                    body: Box::new(b2),
                },
                bk,
            )
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let mut k2 = kinds.clone();
            let (t2, mut tk) = process_fn_body(*then_branch, kinds, ctx, inner_ty);
            let (e2, ek) = process_fn_body(*else_branch, &mut k2, ctx, inner_ty);
            tk.extend(ek);
            (
                IRNode::If {
                    cond,
                    then_branch: Box::new(t2),
                    else_branch: Box::new(e2),
                },
                tk,
            )
        }
        IRNode::Match { scrutinee, cases } => {
            let mut all = Vec::new();
            let cases = cases
                .into_iter()
                .map(|(t, b, body)| {
                    let mut k2 = kinds.clone();
                    let (b2, bk) = process_fn_body(body, &mut k2, ctx, inner_ty);
                    all.extend(bk);
                    (t, b, b2)
                })
                .collect();
            (IRNode::Match { scrutinee, cases }, all)
        }
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => {
            let mut k2 = kinds.clone();
            let (s2, mut sk) = process_fn_body(*some_branch, kinds, ctx, inner_ty);
            let (n2, nk) = process_fn_body(*none_branch, &mut k2, ctx, inner_ty);
            sk.extend(nk);
            (
                IRNode::MatchOption {
                    scrutinee,
                    binding,
                    some_branch: Box::new(s2),
                    none_branch: Box::new(n2),
                },
                sk,
            )
        }
        IRNode::Tuple(elems) => {
            let mut out = Vec::new();
            match elems.first() {
                Some(IRNode::Var(m)) => {
                    if let Some(k) = kinds.get(m) {
                        out.push(k.clone());
                    }
                }
                // Already-lifted tail (idempotence across fixpoint iterations).
                Some(IRNode::Call {
                    function,
                    type_args,
                    ..
                }) if *function == ctx.world.mut_lift_world
                    || *function == ctx.world.mut_lift_state =>
                {
                    out.push(MutKind::Pair(type_args[1].clone()));
                }
                _ => {}
            }
            (IRNode::Tuple(elems), out)
        }
        IRNode::Var(m) => {
            let out = kinds.get(&m).cloned().into_iter().collect();
            (IRNode::Var(m), out)
        }
        IRNode::Call {
            function,
            type_args,
            args,
        } => {
            let out = ctx.fn_kinds.get(&function).cloned().into_iter().collect();
            (
                IRNode::Call {
                    function,
                    type_args,
                    args,
                },
                out,
            )
        }
        other => (other, Vec::new()),
    }
}

/// Rewrite the mutref tails of a MIXED function: lift World- and
/// Struct-kinded tail Mutables to the pair state.
fn rewrite_mixed_tails(
    node: IRNode,
    kinds: &mut HashMap<TempId, MutKind>,
    ctx: &PhiCtx,
    inner_ty: &Type,
    s_ty: &Type,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            track_kind(kinds, &pattern, &value, ctx);
            IRNode::Let {
                pattern,
                value,
                body: Box::new(rewrite_mixed_tails(*body, kinds, ctx, inner_ty, s_ty)),
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let mut k2 = kinds.clone();
            IRNode::If {
                cond,
                then_branch: Box::new(rewrite_mixed_tails(
                    *then_branch,
                    kinds,
                    ctx,
                    inner_ty,
                    s_ty,
                )),
                else_branch: Box::new(rewrite_mixed_tails(
                    *else_branch,
                    &mut k2,
                    ctx,
                    inner_ty,
                    s_ty,
                )),
            }
        }
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(t, b, body)| {
                    let mut k2 = kinds.clone();
                    (
                        t,
                        b,
                        rewrite_mixed_tails(body, &mut k2, ctx, inner_ty, s_ty),
                    )
                })
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => {
            let mut k2 = kinds.clone();
            IRNode::MatchOption {
                scrutinee,
                binding,
                some_branch: Box::new(rewrite_mixed_tails(
                    *some_branch,
                    kinds,
                    ctx,
                    inner_ty,
                    s_ty,
                )),
                none_branch: Box::new(rewrite_mixed_tails(
                    *none_branch,
                    &mut k2,
                    ctx,
                    inner_ty,
                    s_ty,
                )),
            }
        }
        IRNode::Tuple(mut elems) => {
            if let Some(IRNode::Var(m)) = elems.first() {
                let m = m.clone();
                match kinds.get(&m) {
                    Some(MutKind::World) => {
                        assert!(
                            elems.len() >= 2,
                            "world_mode: mixed mutref phi in `{}` has a world-kinded tail \
                             without a struct value to pair with",
                            ctx.fn_name
                        );
                        let s_val = elems[1].clone();
                        elems[0] = IRNode::Call {
                            function: ctx.world.mut_lift_world,
                            type_args: vec![inner_ty.clone(), s_ty.clone()],
                            args: vec![IRNode::Var(m), s_val],
                        };
                    }
                    Some(MutKind::Struct(_)) => {
                        elems[0] = IRNode::Call {
                            function: ctx.world.mut_lift_state,
                            type_args: vec![inner_ty.clone(), s_ty.clone()],
                            args: vec![IRNode::Var(m), IRNode::Var(world_var())],
                        };
                    }
                    _ => {}
                }
            }
            IRNode::Tuple(elems)
        }
        other => other,
    }
}

/// The entry: per-function fixpoint over the whole program. Returns the
/// fn-kind map (consumed by the caller-side pair-WriteBack rewrite).
fn unify_mixed_mutref_phis(
    program: &mut Program,
    world: &WorldFunctions,
    world_ty: &Type,
) -> HashMap<FunctionID, MutKind> {
    let mut fn_kinds: HashMap<FunctionID, MutKind> = HashMap::new();
    loop {
        let mut changed = false;
        let ids: Vec<FunctionID> = program.functions.iter_ids().collect();
        for fid in ids {
            let f = program.functions.get(&fid);
            if f.is_native {
                continue;
            }
            let Some((inner_ty, _)) = sig_mutref(&f.signature.return_type) else {
                continue;
            };
            let fname = f.name.clone();
            let body = std::mem::take(&mut program.functions.get_mut(fid).body);
            let (body2, tails) = {
                let ctx = PhiCtx {
                    world,
                    world_ty,
                    fn_kinds: &fn_kinds,
                    program,
                    fn_name: &fname,
                };
                let mut kinds = HashMap::new();
                process_fn_body(body, &mut kinds, &ctx, &inner_ty)
            };
            let has_worldish = tails
                .iter()
                .any(|k| matches!(k, MutKind::World | MutKind::Pair(_)));
            let structs: Vec<Type> = tails
                .iter()
                .filter_map(|k| match k {
                    MutKind::Struct(t) => Some(t.clone()),
                    _ => None,
                })
                .collect();
            let (body3, new_kind) = if has_worldish && !structs.is_empty() {
                let s_ty = structs[0].clone();
                let out = {
                    let ctx = PhiCtx {
                        world,
                        world_ty,
                        fn_kinds: &fn_kinds,
                        program,
                        fn_name: &fname,
                    };
                    let mut kinds = HashMap::new();
                    rewrite_mixed_tails(body2, &mut kinds, &ctx, &inner_ty, &s_ty)
                };
                eprintln!(
                    "world_mode: unified heterogeneous mutable phi (fn tail) in `{}`",
                    fname
                );
                (out, Some(MutKind::Pair(s_ty)))
            } else if let Some(k) = tails.iter().find(|k| matches!(k, MutKind::Pair(_))) {
                (body2, Some(k.clone()))
            } else if tails.iter().any(|k| matches!(k, MutKind::World)) {
                (body2, Some(MutKind::World))
            } else {
                (body2, structs.first().cloned().map(MutKind::Struct))
            };
            program.functions.get_mut(fid).body = body3;
            if let Some(k) = new_kind {
                if let MutKind::Pair(s_ty) = &k {
                    let pair_state = Type::Tuple(vec![s_ty.clone(), world_ty.clone()]);
                    let f = program.functions.get_mut(fid);
                    let new_ret = replace_sig_mutref_state(&f.signature.return_type, &pair_state);
                    if f.signature.return_type != new_ret {
                        f.signature.return_type = new_ret;
                    }
                }
                if fn_kinds.get(&fid) != Some(&k) {
                    fn_kinds.insert(fid, k);
                    changed = true;
                }
            }
        }
        if !changed {
            return fn_kinds;
        }
    }
}

/// Post-`thread_mutables` recomputation of the world-stated mutref set (the
/// functions whose returned Mutable's state IS the World): base = the return
/// type mentions a `Mutable _ World` slot OR the body holds a World-stated
/// `MutableBorrow` while the (possibly augmented) return carries a mutref;
/// closure over callers returning mutrefs.
fn restore_loop_split_scope_end_writebacks(
    body: IRNode,
    ws: &std::collections::BTreeSet<FunctionID>,
) -> IRNode {
    use crate::data::ir::WriteBackEdge;
    let mut borrow_parent: std::collections::BTreeMap<TempId, TempId> =
        std::collections::BTreeMap::new();
    let mut written_into: std::collections::BTreeSet<TempId> = std::collections::BTreeSet::new();
    let mut wb_children: std::collections::BTreeSet<TempId> = std::collections::BTreeSet::new();
    for n in body.iter() {
        if let IRNode::Let { pattern, value, .. } = n {
            if !pattern.is_empty() {
                if let IRNode::Call { function, args, .. } = value.as_ref() {
                    if ws.contains(function) {
                        if let Some(IRNode::Var(p)) = args.first() {
                            borrow_parent.insert(pattern[0].clone(), p.clone());
                        }
                    }
                }
            }
        }
        if let IRNode::WriteBack { child, parent, .. } = n {
            wb_children.insert(child.clone());
            written_into.insert(parent.clone());
        }
    }
    let targets: std::collections::BTreeSet<TempId> = borrow_parent
        .keys()
        .filter(|m| written_into.contains(*m) && !wb_children.contains(*m))
        .cloned()
        .collect();
    if targets.is_empty() {
        return body;
    }
    body.map(&mut |n| {
        if let IRNode::Let {
            pattern,
            value,
            body,
        } = &n
        {
            if let IRNode::WriteBack { parent, .. } = value.as_ref() {
                if targets.contains(parent) {
                    return IRNode::Let {
                        pattern: pattern.clone(),
                        value: value.clone(),
                        body: Box::new(IRNode::Let {
                            pattern: vec![],
                            value: Box::new(IRNode::WriteBack {
                                child: parent.clone(),
                                parent: borrow_parent[parent].clone(),
                                edge: WriteBackEdge::Direct,
                            }),
                            body: body.clone(),
                        }),
                    };
                }
            }
        }
        n
    })
}

fn world_stated_mutref_fns(
    program: &Program,
    world_ty: &Type,
) -> std::collections::BTreeSet<FunctionID> {
    fn ret_has_mutref(t: &Type) -> bool {
        match t {
            Type::MutableReference(_, _) => true,
            Type::Tuple(v) => v.iter().any(ret_has_mutref),
            _ => false,
        }
    }
    fn ret_has_world_mutref(t: &Type, world_ty: &Type) -> bool {
        match t {
            Type::MutableReference(_, state) => state.as_ref() == world_ty,
            Type::Tuple(v) => v.iter().any(|t| ret_has_world_mutref(t, world_ty)),
            _ => false,
        }
    }
    let mut set = std::collections::BTreeSet::new();
    for (fid, f) in program.functions.iter() {
        if f.is_native {
            continue;
        }
        let ret = &f.signature.return_type;
        if ret_has_world_mutref(ret, world_ty)
            || (ret_has_mutref(ret)
                && f.body.iter().any(|n| {
                    matches!(n, IRNode::MutableBorrow { state_type, .. } if state_type == world_ty)
                }))
        {
            set.insert(fid);
        }
    }
    loop {
        let mut changed = false;
        for (fid, f) in program.functions.iter() {
            if f.is_native || set.contains(&fid) || !ret_has_mutref(&f.signature.return_type) {
                continue;
            }
            if f.body.calls().any(|c| set.contains(&c)) {
                set.insert(fid);
                changed = true;
            }
        }
        if !changed {
            return set;
        }
    }
}

pub fn thread_world(program: &mut Program) {
    let Some(world) = program.world_functions.clone() else {
        return;
    };
    let world_ty = world.world_type();

    // Heterogeneous mutable phi unification (M1) — must run FIRST so mixed
    // functions are Pair-kinded before the world-stated writeback fixup
    // classifies callees (a mixed callee must NOT be treated as world-stated:
    // its `Mutable.apply` yields `(S × World)`, not `World`).
    let fn_kinds = unify_mixed_mutref_phis(program, &world, &world_ty);

    // WriteBack fixup for world-stated Mutables (see
    // `mutable_threading::fix_world_stated_writebacks`). Runs HERE — after
    // every post-threading WriteBack fixup pass has settled the child var
    // names — not at the end of `thread_mutables` (those later passes rename
    // the children, e.g. `__mut_ret_1` → `t_t6`).
    {
        let ws: std::collections::BTreeSet<FunctionID> = fn_kinds
            .iter()
            .filter(|(_, k)| matches!(k, MutKind::World))
            .map(|(fid, _)| *fid)
            .collect();
        if !ws.is_empty() {
            let ids: Vec<FunctionID> = program.functions.iter_ids().collect();
            for fid in &ids {
                if program.functions.get(fid).is_native {
                    continue;
                }
                let body = std::mem::take(&mut program.functions.get_mut(*fid).body);
                // Restore scope-end WriteBacks that the loop split dropped:
                // when a world-stated Mutable's borrow scope spans a while
                // loop, the translator's end-of-scope `WriteBack{child: m,
                // parent: p}` lands inside the split-off helper (where `m`
                // is a plain value param and the WriteBack is meaningless),
                // so the caller — which holds the actual Mutable — never
                // applies it to the World. Detect callers that write INTO
                // such a Mutable (helper-return `WriteBack{.., parent: m}`)
                // without any `WriteBack{child: m, ..}` downstream, and
                // re-emit the scope-end WriteBack so the fixup below turns
                // it into the `Mutable.apply m __world` write-back.
                let body = restore_loop_split_scope_end_writebacks(body, &ws);
                let mut w = std::collections::BTreeSet::new();
                program.functions.get_mut(*fid).body =
                    crate::analysis::mutable_threading::fix_world_stated_writebacks(
                        body, &ws, &mut w,
                    );
            }
        }
    }

    // Caller-side WriteBacks on PAIR-kinded Mutables destructure
    // `Mutable.apply m : (S × World)` into `(parent, __world)`.
    {
        let pairs: std::collections::BTreeSet<FunctionID> = fn_kinds
            .iter()
            .filter(|(_, k)| matches!(k, MutKind::Pair(_)))
            .map(|(fid, _)| *fid)
            .collect();
        // Persist for the end-of-finalize re-run (`run_pair_writeback_fixup`):
        // value-nested rewrites made here can be reverted by later optimize
        // passes, so the fixup must also run over the final body shape.
        program.pair_mut_fns = pairs.clone();
        run_pair_writeback_fixup(program);
    }

    // Seed: functions Phase A gave a `__world` param.
    let fn_ids: Vec<FunctionID> = program.functions.iter_ids().collect();
    let mut threaded: std::collections::BTreeSet<FunctionID> = fn_ids
        .iter()
        .copied()
        .filter(|fid| {
            let f = program.functions.get(fid);
            !f.is_native && has_world_param(f)
        })
        .collect();

    // Callee→caller fixpoint over the call graph.
    loop {
        let mut changed = false;
        for fid in &fn_ids {
            if threaded.contains(fid) {
                continue;
            }
            let func = program.functions.get(fid);
            if func.is_native {
                continue;
            }
            if func.body.calls().any(|callee| threaded.contains(&callee)) {
                threaded.insert(*fid);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Reader/writer split: only functions whose cone WRITES the world get
    // the augmented `(R, World)` return. Base = a direct call to a mutating
    // World native; closure over the call graph.
    let write_natives: std::collections::BTreeSet<FunctionID> = [
        world.set_df,
        world.erase_df,
        // Bag-valued df writes mutate the world exactly like the typed views:
        // a function whose only world effect is a `setDfBag`/`eraseDfBag`
        // (e.g. inside a returned world-stated Mutable's reconstruct) must
        // return the updated world or the bag update dies at function exit.
        world.set_df_bag,
        world.erase_df_bag,
        world.put_owned,
        world.put_shared,
        world.put_frozen,
        world.emit_event,
        // The take views DELETE the taken object from the store — a wrapper
        // whose only world effect is a take must still return the updated
        // world, or the deletion dies at function exit and a repeated
        // `take_from_sender` silently re-yields the same object.
        world.take_from_address_by_id,
        world.take_shared_by_id,
        // `end_transaction` RESETS the per-tx user-event counter — callers
        // must see the post-reset world or counts accumulate across txs.
        world.take_tx_user_events,
    ]
    .into_iter()
    .collect();
    let mut writers: std::collections::BTreeSet<FunctionID> = threaded
        .iter()
        .copied()
        .filter(|fid| {
            program
                .functions
                .get(fid)
                .body
                .calls()
                .any(|c| write_natives.contains(&c))
        })
        .collect();
    loop {
        let mut changed = false;
        for fid in &threaded {
            if writers.contains(fid) {
                continue;
            }
            if program
                .functions
                .get(fid)
                .body
                .calls()
                .any(|c| writers.contains(&c))
            {
                writers.insert(*fid);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Capture per-callee info before augmenting signatures.
    let mut callee_info: BTreeMap<FunctionID, CalleeInfo> = BTreeMap::new();
    for fid in &threaded {
        let func = program.functions.get(fid);
        callee_info.insert(
            *fid,
            CalleeInfo {
                value_face: is_value_face(&func.name, &func.signature.return_type)
                    && writers.contains(fid),
                orig_ret_unit: matches!(&func.signature.return_type, Type::Tuple(v) if v.is_empty()),
            },
        );
    }

    // Signature augmentation: trailing `__world` param on caller-side
    // functions that didn't get one in Phase A; trailing return slot on
    // every threaded value face.
    for fid in &threaded {
        let func = program.functions.get_mut(*fid);
        if !has_world_param(func) {
            func.signature.parameters.push(Parameter {
                name: WORLD_VAR.to_string(),
                param_type: world_ty.clone(),
                ssa_value: world_var(),
            });
        }
        if callee_info[fid].value_face {
            func.signature.return_type = augmented_return(&func.signature.return_type, &world_ty);
        }
    }

    // Body rewriting: tails wrapped on value faces, call sites threaded.
    for fid in &threaded {
        let my_face_is_value = callee_info[fid].value_face;
        let my_ret_unit = callee_info[fid].orig_ret_unit;
        let fn_name = program.functions.get(fid).name.clone();
        let body = std::mem::take(&mut program.functions.get_mut(*fid).body);

        let body = if my_face_is_value {
            wrap_tails(body, my_ret_unit, &callee_info)
        } else {
            body
        };

        let body = body.map_top_down(&mut |node| rewrite_call_node(node, &callee_info, &fn_name));

        // Branch-scoped `__world` rebinds (a threaded call inside an
        // `If`/`Match` branch) are lexically trapped exactly like the
        // post-mutable-threading shadow updates — the same phi lift makes
        // them escape (`let (x, __world) := if … then (…, __world') else …`).
        // Without this the world update inside a branch is silently lost.
        let body = crate::analysis::lift_post_threading_phis(body);

        program.functions.get_mut(*fid).body = body;
    }
}

/// Mirror `ghost_threading::augmented_return` for the single world slot.
fn augmented_return(original: &Type, world_ty: &Type) -> Type {
    if matches!(original, Type::Tuple(v) if v.is_empty()) {
        world_ty.clone()
    } else {
        Type::Tuple(vec![original.clone(), world_ty.clone()])
    }
}

/// Number of trailing PROOF-slot arguments on a call: loop-invariant
/// hypothesis forwards (`hinv`), entry-cascade precondition forwards
/// (`hpre*`), and `Abort` entry placeholders — all emitted by the loop-inv
/// machinery (structure building / entry cascades) as value-args-with-proof-
/// meaning. The `__world` argument must sit BEFORE this suffix, because the
/// materialized signature orders proof params after all value params.
fn proof_suffix_len(args: &[IRNode]) -> usize {
    let mut n = 0;
    for a in args.iter().rev() {
        match a {
            IRNode::Abort { .. } => n += 1,
            IRNode::Var(v) if v.as_ref() == "hinv" || v.as_ref().starts_with("hpre") => n += 1,
            _ => break,
        }
    }
    n
}

fn args_already_threaded(args: &[IRNode]) -> bool {
    let vlen = args.len() - proof_suffix_len(args);
    vlen > 0 && matches!(&args[vlen - 1], IRNode::Var(v) if v.as_ref() == WORLD_VAR)
}

/// Insert the `__world` argument before any trailing proof-slot args.
fn push_world_arg(args: &mut Vec<IRNode>) {
    let at = args.len() - proof_suffix_len(args);
    args.insert(at, IRNode::Var(world_var()));
}

fn rewrite_call_node(
    node: IRNode,
    info: &BTreeMap<FunctionID, CalleeInfo>,
    caller_name: &str,
) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            if let IRNode::Call {
                function,
                type_args,
                args,
            } = *value
            {
                if let Some(ci) = info.get(&function) {
                    if args_already_threaded(&args) {
                        return IRNode::Let {
                            pattern,
                            value: Box::new(IRNode::Call {
                                function,
                                type_args,
                                args,
                            }),
                            body,
                        };
                    }
                    let mut new_args = args;
                    push_world_arg(&mut new_args);
                    let call = IRNode::Call {
                        function,
                        type_args,
                        args: new_args,
                    };
                    if !ci.value_face {
                        return IRNode::Let {
                            pattern,
                            value: Box::new(call),
                            body,
                        };
                    }
                    return build_destructure(pattern, call, *body, ci);
                }
                return IRNode::Let {
                    pattern,
                    value: Box::new(IRNode::Call {
                        function,
                        type_args,
                        args,
                    }),
                    body,
                };
            }
            IRNode::Let {
                pattern,
                value,
                body,
            }
        }
        IRNode::Call {
            function,
            type_args,
            args,
        } => {
            if let Some(ci) = info.get(&function) {
                if !args_already_threaded(&args) {
                    if ci.value_face {
                        panic!(
                            "world_threading: threaded value-face call (callee fid {}) at an \
                             unsupported position in {} — expected all such calls at Let-value, \
                             sequencing, or tail positions",
                            function, caller_name
                        );
                    }
                    let mut new_args = args;
                    push_world_arg(&mut new_args);
                    return IRNode::Call {
                        function,
                        type_args,
                        args: new_args,
                    };
                }
            }
            IRNode::Call {
                function,
                type_args,
                args,
            }
        }
        other => other,
    }
}

fn build_destructure(pattern: Vec<TempId>, call: IRNode, body: IRNode, ci: &CalleeInfo) -> IRNode {
    if ci.orig_ret_unit {
        return IRNode::Let {
            pattern: vec![world_var()],
            value: Box::new(call),
            body: Box::new(body),
        };
    }
    if pattern.len() <= 1 {
        let mut pat = if pattern.is_empty() {
            vec![Rc::from("_") as TempId]
        } else {
            pattern
        };
        pat.push(world_var());
        return IRNode::Let {
            pattern: pat,
            value: Box::new(call),
            body: Box::new(body),
        };
    }
    // Multi-element original pattern: bind the original tuple return as one
    // component, then destructure it (mirrors ghost_threading).
    let orig_temp: TempId = Rc::from("__world_orig_ret");
    IRNode::Let {
        pattern: vec![orig_temp.clone(), world_var()],
        value: Box::new(call),
        body: Box::new(IRNode::Let {
            pattern,
            value: Box::new(IRNode::Var(orig_temp)),
            body: Box::new(body),
        }),
    }
}

fn wrap_tails(node: IRNode, my_ret_unit: bool, info: &BTreeMap<FunctionID, CalleeInfo>) -> IRNode {
    match node {
        IRNode::Let {
            pattern,
            value,
            body,
        } => IRNode::Let {
            pattern,
            value,
            body: Box::new(wrap_tails(*body, my_ret_unit, info)),
        },
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(wrap_tails(*then_branch, my_ret_unit, info)),
            else_branch: Box::new(wrap_tails(*else_branch, my_ret_unit, info)),
        },
        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(tag, bindings, body)| (tag, bindings, wrap_tails(body, my_ret_unit, info)))
                .collect(),
        },
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch: Box::new(wrap_tails(*some_branch, my_ret_unit, info)),
            none_branch: Box::new(wrap_tails(*none_branch, my_ret_unit, info)),
        },
        other => wrap_terminal(other, my_ret_unit, info),
    }
}

fn wrap_terminal(
    node: IRNode,
    my_ret_unit: bool,
    info: &BTreeMap<FunctionID, CalleeInfo>,
) -> IRNode {
    // Abort tails never return normally; `sorry` inhabits the augmented
    // tuple (same rule as mutable/ghost threading).
    if matches!(node, IRNode::Abort { .. }) {
        return node;
    }
    if let IRNode::Call {
        function,
        type_args,
        args,
    } = node
    {
        if let Some(ci) = info.get(&function) {
            if !ci.value_face {
                // Reader (param-only) callee: the tail keeps the callee's
                // original return type — wrap like any plain expression and
                // let `rewrite_call_node` append the `__world` argument.
                return build_my_tail(
                    Some(IRNode::Call {
                        function,
                        type_args,
                        args,
                    }),
                    my_ret_unit,
                );
            }
            let mut new_args = args;
            if !args_already_threaded(&new_args) {
                push_world_arg(&mut new_args);
            }
            let call = IRNode::Call {
                function,
                type_args,
                args: new_args,
            };
            if ci.orig_ret_unit == my_ret_unit {
                // Pass-through: the callee returns the caller's augmented shape.
                return call;
            }
            if ci.orig_ret_unit {
                // Callee returns World alone; caller expects (orig, World)
                // with a non-unit orig — impossible for a type-preserving
                // tail call, so this cannot occur.
                panic!("world_threading: unit-return callee in non-unit tail position");
            }
            let r: TempId = Rc::from("__world_tail_ret");
            return IRNode::Let {
                pattern: vec![r, world_var()],
                value: Box::new(call),
                body: Box::new(build_my_tail(None, my_ret_unit)),
            };
        }
        return build_my_tail(
            Some(IRNode::Call {
                function,
                type_args,
                args,
            }),
            my_ret_unit,
        );
    }
    if my_ret_unit {
        if matches!(&node, IRNode::Tuple(v) if v.is_empty()) {
            return IRNode::Var(world_var());
        }
        return IRNode::Let {
            pattern: vec![],
            value: Box::new(node),
            body: Box::new(IRNode::Var(world_var())),
        };
    }
    build_my_tail(Some(node), my_ret_unit)
}

fn build_my_tail(orig: Option<IRNode>, my_ret_unit: bool) -> IRNode {
    match orig {
        Some(e) if !my_ret_unit => IRNode::Tuple(vec![e, IRNode::Var(world_var())]),
        Some(e) => IRNode::Let {
            pattern: vec![],
            value: Box::new(e),
            body: Box::new(IRNode::Var(world_var())),
        },
        None => IRNode::Var(world_var()),
    }
}
