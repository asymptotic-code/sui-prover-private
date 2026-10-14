// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Per-basic-block live-borrow tracking for the IR translator.
//!
//! Move stackless bytecode encodes mutable-reference call arguments by passing
//! the parent slot index — the borrow path is recorded in side-channel
//! metadata (BorrowAnnotation) and instrumented into explicit `WriteBack`
//! ops. When a Move source `dyn::add(&mut bag.id, k, v)` lowers to
//!
//!   [N]   BorrowField(slot 0=bag, field 0) -> $t3
//!   [N+1] Function(dyn::add)  srcs=[0, 1, 2]
//!   ...
//!   [M]   WriteBack(Reference(0), Field(_, F)) srcs=[$tF]
//!
//! the lean-backend's IR translator needs to recognise that `srcs[0] = 0` at
//! [N+1] really refers to `$t3`, not slot 0 directly.
//!
//! After `EliminateImmRefsProcessor`, immutable references are erased:
//! `bag: &Bag` becomes a `Bag` value, and `&bag.id` becomes `GetField`
//! producing a UID value. The same disambiguation applies — the call still
//! passes slot 0 (Bag value), but the function expects the GetField result.
//!
//! `BorrowState` tracks BorrowField/BorrowLoc/GetField (the latter for the
//! immutable-ref erased case). To avoid false positives on regular field
//! reads (`bag.size`) followed by an unrelated call on the parent,
//! `resolve_typed` is type-aware: it only substitutes when the slot's
//! declared type does not match the callee's expected param type.
//!
//! Borrows do not cross basic-block boundaries — `BorrowState` is reset by
//! the caller at every Label/Branch/Jump.

use std::collections::BTreeMap;

use move_model::ty::Type;
use move_stackless_bytecode::ast::TempIndex;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Operation};

/// Per-block live-borrow state. Maps a borrow-handle temp to its parent slot.
/// (We do not track the `BorrowEdge` here — only the parent — because the
/// substitution logic only cares about which temp to swap in for a slot.)
///
/// `aliases` records ReadRef-derived temps as aliases of the source slot:
/// when bytecode does `ReadRef -> $tN, srcs=[K]` we treat $tN as semantically
/// equivalent to slot K, so a Function call passing $tN is resolved against
/// slot K's borrow children. This handles the post-EliminateImmRefs case
/// where the bytecode `ReadRef`s a parent struct value before passing it to
/// a function that expects an inner field.
#[derive(Debug, Default, Clone)]
pub struct BorrowState {
    /// child_temp -> parent_slot
    by_child: BTreeMap<TempIndex, TempIndex>,
    /// parent_slot -> child_temp(s) that borrow from it
    by_parent: BTreeMap<TempIndex, Vec<TempIndex>>,
    /// alias_temp -> original_slot (from `ReadRef -> alias, srcs=[original]`)
    aliases: BTreeMap<TempIndex, TempIndex>,
    /// Sticky: every parent_slot that ever had a `BorrowField` /
    /// `BorrowLoc` / `GetField` child introduced in this block, even after
    /// the borrow itself was consumed by an intervening call. Used by the
    /// IR translator's WriteBack handler to discriminate the
    /// "BorrowField-then-call" pattern (Reserve / Asset family — apply
    /// returns the inner state, field-update needed) from the
    /// "wrapper-function-on-whole-parent" pattern (Bag.borrow_mut — apply
    /// already returns the parent type, no field-update needed).
    borrow_field_seen: std::collections::BTreeSet<TempIndex>,
}

impl BorrowState {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn clear(&mut self) {
        self.by_child.clear();
        self.by_parent.clear();
        self.aliases.clear();
        self.borrow_field_seen.clear();
    }

    /// Did `slot` ever have a `BorrowField` / `BorrowLoc` / `GetField`
    /// child introduced in this block, regardless of whether the borrow
    /// is still live now? The intermediate `Function` call that consumed
    /// the borrow (via `kill_rooted_at`) leaves the live tracking empty
    /// at the WriteBack site, so we check the sticky set instead.
    ///
    /// Used by the IR translator's WriteBack handler to discriminate the
    /// "BorrowField-then-call" pattern (Reserve / Asset family) from the
    /// "wrapper-function-on-whole-parent" pattern (Bag.borrow_mut).
    pub fn saw_borrow_field(&self, slot: TempIndex) -> bool {
        let effective = self.aliases.get(&slot).copied().unwrap_or(slot);
        self.borrow_field_seen.contains(&effective)
    }

    /// Pre-seed `borrow_field_seen` with a precomputed set. Used to make
    /// "did slot N have a BorrowField introduced anywhere in the function?"
    /// queryable from a fresh per-block `BorrowState`. The IR translator
    /// resets borrow tracking at every block boundary (the live `by_child`
    /// / `by_parent` are per-block by contract), but `borrow_field_seen`
    /// describes a function-wide invariant we need at WriteBack sites
    /// even when the BorrowField op lives in a different block.
    pub fn seed_borrow_field_seen(&mut self, seen: &std::collections::BTreeSet<TempIndex>) {
        self.borrow_field_seen.extend(seen.iter().copied());
    }

    fn introduce(&mut self, child: TempIndex, parent: TempIndex) {
        // If child was already tracked under a different parent, drop the old link.
        if let Some(prev_parent) = self.by_child.get(&child).copied() {
            if let Some(siblings) = self.by_parent.get_mut(&prev_parent) {
                siblings.retain(|&t| t != child);
            }
        }
        self.by_child.insert(child, parent);
        self.by_parent.entry(parent).or_default().push(child);
        self.borrow_field_seen.insert(parent);
    }

    fn kill(&mut self, child: TempIndex) {
        if let Some(parent) = self.by_child.remove(&child) {
            if let Some(siblings) = self.by_parent.get_mut(&parent) {
                siblings.retain(|&t| t != child);
                if siblings.is_empty() {
                    self.by_parent.remove(&parent);
                }
            }
        }
        // Drop any alias whose effective slot is `child` — the source went away.
        self.aliases.remove(&child);
    }

    /// Drop every borrow rooted at this slot.
    fn kill_rooted_at(&mut self, slot: TempIndex) {
        let children = self.by_parent.remove(&slot).unwrap_or_default();
        for c in children {
            self.by_child.remove(&c);
        }
    }

    /// At a Function call, decide whether to swap `slot` for one of its live
    /// child borrows. `expected` is the callee's declared param type at this
    /// position (after type-arg substitution). `target` provides slot type
    /// lookups.
    ///
    /// Substitute iff:
    /// - slot has at least one live child,
    /// - slot's type does NOT match `expected`,
    /// - exactly one live child has a type matching `expected`.
    pub fn resolve_typed(
        &self,
        target: &FunctionTarget,
        slot: TempIndex,
        expected: &Type,
    ) -> Option<TempIndex> {
        // If `slot` is a ReadRef alias, resolve against the original slot — the
        // semantic content is the same, only the type wrapper differs.
        let effective_slot = self.aliases.get(&slot).copied().unwrap_or(slot);
        let kids = self.by_parent.get(&effective_slot)?;
        if kids.is_empty() {
            return None;
        }
        let slot_ty = target.get_local_type(slot);
        if types_compatible(slot_ty, expected) {
            return None;
        }
        let mut matches: Vec<TempIndex> = Vec::new();
        for &k in kids {
            let kty = target.get_local_type(k);
            if types_compatible(kty, expected) {
                matches.push(k);
            }
        }
        if matches.len() == 1 {
            Some(matches[0])
        } else {
            None
        }
    }

    /// Update the state given a bytecode that has *just been substituted into*
    /// the call (or a non-call instruction). Bytecode has the original srcs
    /// (pre-substitution), so we kill rooted borrows on the slots actually
    /// passed.
    pub fn observe(&mut self, bc: &Bytecode) {
        match bc {
            Bytecode::Call(_, dests, op, srcs, _) => {
                match op {
                    Operation::BorrowField(_, _, _, _)
                    | Operation::BorrowLoc
                    | Operation::GetField(_, _, _, _) => {
                        if let (Some(&parent), Some(&dest)) = (srcs.first(), dests.first()) {
                            self.introduce(dest, parent);
                        }
                    }
                    Operation::ReadRef => {
                        // Record alias: dest IS slot (after deref). Function
                        // calls that pass dest are equivalent to calls passing slot.
                        if let (Some(&parent), Some(&dest)) = (srcs.first(), dests.first()) {
                            self.aliases.insert(dest, parent);
                        }
                    }
                    Operation::WriteBack(_, _) => {
                        if let Some(&child) = srcs.first() {
                            self.kill(child);
                        }
                    }
                    Operation::Destroy => {
                        for &s in srcs {
                            self.kill(s);
                            self.kill_rooted_at(s);
                        }
                    }
                    Operation::Function(..)
                    | Operation::OpaqueCallBegin(..)
                    | Operation::OpaqueCallEnd(..) => {
                        // The call consumes any borrow rooted at slots it passes.
                        for &s in srcs {
                            self.kill_rooted_at(s);
                        }
                        // Calls may overwrite dest slots with new values.
                        for &d in dests {
                            self.kill(d);
                            self.kill_rooted_at(d);
                        }
                    }
                    _ => {
                        // Other ops (WriteRef/ReadRef/Pack/Unpack/GetField/...)
                        // overwrite their dests — kill any borrow tracking on those.
                        for &d in dests {
                            self.kill(d);
                            self.kill_rooted_at(d);
                        }
                    }
                }
            }
            Bytecode::Assign(_, dest, _, _) => {
                self.kill(*dest);
                self.kill_rooted_at(*dest);
            }
            Bytecode::Load(_, dest, _) => {
                self.kill(*dest);
                self.kill_rooted_at(*dest);
            }
            _ => {}
        }
    }
}

/// Pre-scan a function's bytecode for every parent slot that ever has a
/// `BorrowField` / `BorrowLoc` / `GetField` introduced as its child. Used
/// to seed per-block `BorrowState`s with a function-wide view, so the
/// WriteBack handler can identify the "BorrowField-then-call" pattern
/// even when the BorrowField op was in a different block.
pub fn precompute_borrow_field_parents(
    target: &FunctionTarget,
) -> std::collections::BTreeSet<TempIndex> {
    let mut out = std::collections::BTreeSet::new();
    for bc in target.get_bytecode() {
        if let Bytecode::Call(_, _, op, srcs, _) = bc {
            match op {
                Operation::BorrowField(_, _, _, _)
                | Operation::BorrowLoc
                | Operation::GetField(_, _, _, _) => {
                    if let Some(&parent) = srcs.first() {
                        out.insert(parent);
                    }
                }
                _ => {}
            }
        }
    }
    out
}

/// Two Move types are "compatible" if they're equal modulo top-level
/// reference wrappers. After `EliminateImmRefsProcessor`, callers pass
/// values where references were declared, so `&T` and `T` should match.
fn types_compatible(a: &Type, b: &Type) -> bool {
    fn unwrap_ref(t: &Type) -> &Type {
        match t {
            Type::Reference(_, inner) => inner.as_ref(),
            other => other,
        }
    }
    unwrap_ref(a) == unwrap_ref(b)
}
