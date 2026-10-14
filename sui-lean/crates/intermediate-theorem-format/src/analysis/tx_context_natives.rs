// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Model the stateful `sui::tx_context` VM natives from the threaded
//! `TxContext` struct fields.
//!
//! `tx_context::fresh_object_address(_ctx)` and `tx_context::sender(_self)`
//! both bottom out in nullary VM natives (`fresh_id()` / `native_sender()`)
//! that the prelude models as `default` (address 0). In world-mode that is
//! fatal: every `object::new` yields uid 0, so the World object store aliases
//! all objects to a single slot (`putShared` clobbers `putOwned`), and
//! `take_from_sender` queries account 0 while objects are owned by the real
//! sender. The runtime VM derives these from tx-execution state; our faithful
//! model reads the state that already threads through the program:
//!
//! * `fresh_object_address(ctx)` -> `(derive_id ctx.tx_hash ctx.ids_created,
//!   { ctx with ids_created := ids_created + 1 })`. The sui source documents
//!   fresh ids as `hash(tx_hash || ids_created)`; `derive_id` (natives) is
//!   injective, and `tx_hash` encodes the txn number so ids stay distinct
//!   across transactions even though `next_tx` resets `ids_created`.
//! * `sender(self)` -> `self.sender` (the field set by `begin` / `next_tx`).
//!
//! Runs after `thread_mutables` (so `fresh_object_address` already returns the
//! threaded `(address, TxContext)` tuple) and before `dead_param_elimination`
//! (so the now-used `self` param on `sender` survives). World-mode-gated to
//! avoid perturbing non-world object-identity behaviour.

use crate::data::functions::{Function, FunctionSignature, Parameter};
use crate::data::ir::{BinOp, Const, IRNode};
use crate::data::types::Type;
use crate::data::Program;
use ethnum::U256;

pub fn model_tx_context_natives(program: &mut Program) {
    let Some((tx_struct_id, tx_module_id, txhash_idx, ids_idx, sender_idx, epoch_idx, ts_idx)) =
        find_tx_context_struct(program)
    else {
        return;
    };

    let mut sender_fn = None;
    let mut epoch_fn = None;
    let mut ts_fn = None;
    let mut incr_epoch_fn = None;
    let mut fresh_fn = None;
    let mut derive_id_fn = None;
    let mut create_fn = None;
    for (id, f) in program.functions.iter() {
        if f.module_id != tx_module_id {
            continue;
        }
        match f.name.as_str() {
            "sender" => sender_fn = Some(id),
            "epoch" => epoch_fn = Some(id),
            "epoch_timestamp_ms" => ts_fn = Some(id),
            "increment_epoch_number" => incr_epoch_fn = Some(id),
            "fresh_object_address" => fresh_fn = Some(id),
            "derive_id" => derive_id_fn = Some(id),
            "create" => create_fn = Some(id),
            _ => {}
        }
    }

    // `tx_context::create` hardcodes the `sender`/`epoch`/`epoch_timestamp_ms`
    // fields to 0 (the real VM carries them out-of-band via `replace` + nullary
    // natives, discarding the arguments). Our field-read models below need the
    // constructor to actually store the passed values or every
    // `begin`/`next_tx`-derived ctx reports 0 — breaking sender-keyed lookups
    // (candidate tables, owned inventory) and epoch arithmetic (second
    // `advance_epoch` raises EAdvancedToWrongEpoch because `new_epoch` is
    // always 0 + 1).
    if let Some(cid) = create_fn {
        let (sender_ssa, epoch_ssa, ts_ssa) = {
            let f = program.functions.get(&cid);
            assert!(
                f.signature.parameters.len() >= 4,
                "tx_context::create is missing its sender/tx_hash/epoch/epoch_timestamp_ms params"
            );
            (
                f.signature.parameters[0].ssa_value.clone(),
                f.signature.parameters[2].ssa_value.clone(),
                f.signature.parameters[3].ssa_value.clone(),
            )
        };
        let f = program.functions.get_mut(cid);
        let body = std::mem::replace(&mut f.body, IRNode::Tuple(vec![]));
        f.body = body.map(&mut |node| match node {
            IRNode::Pack {
                struct_id,
                type_args,
                mut fields,
                variant_index,
            } if struct_id == tx_struct_id => {
                assert!(
                    sender_idx < fields.len() && epoch_idx < fields.len() && ts_idx < fields.len(),
                    "tx_context::create TxContext pack missing modeled fields"
                );
                fields[sender_idx] = IRNode::Var(sender_ssa.clone());
                fields[epoch_idx] = IRNode::Var(epoch_ssa.clone());
                fields[ts_idx] = IRNode::Var(ts_ssa.clone());
                IRNode::Pack {
                    struct_id,
                    type_args,
                    fields,
                    variant_index,
                }
            }
            other => other,
        });
    }

    // `epoch`/`epoch_timestamp_ms` bottom out in nullary VM natives (= 0
    // forever); model them as field reads like `sender`. Field reads keep the
    // self param alive so the ctx argument at call sites survives.
    for (fid, field_index) in [(epoch_fn, epoch_idx), (ts_fn, ts_idx)] {
        let Some(fid) = fid else { continue };
        let f = program.functions.get_mut(fid);
        assert!(
            !f.signature.parameters.is_empty(),
            "tx_context epoch accessor lost its self param before native modeling"
        );
        let self_ssa = f.signature.parameters[0].ssa_value.clone();
        f.body = IRNode::Field {
            struct_id: tx_struct_id,
            field_index,
            base: Box::new(IRNode::Var(self_ssa)),
        };
    }

    // `increment_epoch_number` delegates to the no-op `replace` native (epoch
    // never advances). It is the only epoch mutator `test_scenario::next_epoch`
    // uses; model it as the field update `{ self with epoch := self.epoch + 1 }`.
    if let Some(fid) = incr_epoch_fn {
        let f = program.functions.get_mut(fid);
        assert!(
            !f.signature.parameters.is_empty(),
            "tx_context::increment_epoch_number lost its self param before native modeling"
        );
        let self_ssa = f.signature.parameters[0].ssa_value.clone();
        let bumped = IRNode::BinOp {
            op: BinOp::Add,
            lhs: Box::new(IRNode::Field {
                struct_id: tx_struct_id,
                field_index: epoch_idx,
                base: Box::new(IRNode::Var(self_ssa.clone())),
            }),
            rhs: Box::new(IRNode::Const(Const::UInt {
                bits: 64,
                value: U256::new(1),
            })),
        };
        f.body = IRNode::UpdateField {
            base: Box::new(IRNode::Var(self_ssa)),
            struct_id: tx_struct_id,
            field_index: epoch_idx,
            value: Box::new(bumped),
        };
    }

    if let Some(sid) = sender_fn {
        let f = program.functions.get_mut(sid);
        assert!(
            !f.signature.parameters.is_empty(),
            "tx_context::sender lost its self param before native modeling"
        );
        let self_ssa = f.signature.parameters[0].ssa_value.clone();
        f.body = IRNode::Field {
            struct_id: tx_struct_id,
            field_index: sender_idx,
            base: Box::new(IRNode::Var(self_ssa)),
        };
    }

    if let Some(fid) = fresh_fn {
        let derive_id_fn = derive_id_fn.unwrap_or_else(|| {
            program.functions.add(Function {
                module_id: tx_module_id,
                name: "derive_id".to_string(),
                signature: FunctionSignature {
                    type_params: vec![],
                    parameters: vec![
                        Parameter {
                            name: "tx_hash".to_string(),
                            param_type: Type::Vector(Box::new(Type::UInt(8))),
                            ssa_value: "tx_hash".into(),
                        },
                        Parameter {
                            name: "ids_created".to_string(),
                            param_type: Type::UInt(64),
                            ssa_value: "ids_created".into(),
                        },
                    ],
                    proof_params: vec![],
                    return_type: Type::Address,
                },
                body: IRNode::default(),
                theorem: None,
                is_native: true,
                mutual_group_id: None,
                test_expectation: None,
                is_uninterpreted: false,
            })
        });

        let ctx_ssa = {
            let f = program.functions.get(&fid);
            assert!(
                !f.signature.parameters.is_empty(),
                "tx_context::fresh_object_address has no ctx param after threading"
            );
            f.signature.parameters[0].ssa_value.clone()
        };
        let ctx = || IRNode::Var(ctx_ssa.clone());
        let tx_hash = IRNode::Field {
            struct_id: tx_struct_id,
            field_index: txhash_idx,
            base: Box::new(ctx()),
        };
        let ids = IRNode::Field {
            struct_id: tx_struct_id,
            field_index: ids_idx,
            base: Box::new(ctx()),
        };
        let addr = IRNode::Call {
            function: derive_id_fn,
            type_args: vec![],
            args: vec![tx_hash, ids.clone()],
        };
        let new_ids = IRNode::BinOp {
            op: BinOp::Add,
            lhs: Box::new(ids),
            rhs: Box::new(IRNode::Const(Const::UInt {
                bits: 64,
                value: U256::new(1),
            })),
        };
        let new_ctx = IRNode::UpdateField {
            base: Box::new(ctx()),
            struct_id: tx_struct_id,
            field_index: ids_idx,
            value: Box::new(new_ids),
        };
        program.functions.get_mut(fid).body = IRNode::Tuple(vec![addr, new_ctx]);
    }
}

fn find_tx_context_struct(
    program: &Program,
) -> Option<(usize, usize, usize, usize, usize, usize, usize)> {
    for (sid, s) in program.structs.iter() {
        if s.qualified_name != "tx_context::TxContext" {
            continue;
        }
        let idx = |n: &str| {
            s.fields
                .iter()
                .position(|f| f.name == n)
                .unwrap_or_else(|| panic!("tx_context::TxContext missing field {n}"))
        };
        return Some((
            *sid,
            s.module_id,
            idx("tx_hash"),
            idx("ids_created"),
            idx("sender"),
            idx("epoch"),
            idx("epoch_timestamp_ms"),
        ));
    }
    None
}
