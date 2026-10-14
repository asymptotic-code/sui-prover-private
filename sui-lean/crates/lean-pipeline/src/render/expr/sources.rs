//! Borrow-source machinery (split from `expr/mod.rs`,
//! `plans/lean-pipeline/renderer-split.md`).

use super::{BorrowMutOrigin, RuntimeBorrowSource};
use crate::ir::visit::Visitor;
use crate::ir::{Block, BlockTail, Const, Expr, Program, Stmt, VarId};
use ethnum::U256;
use std::collections::BTreeMap;

/// Recurse ONLY into the nested-block-bearing sub-positions of `e`
/// (`If`/`Match`/`While`/`Quantifier`), exactly mirroring the
/// hand-rolled `collect_*_in_expr` partners these collectors used to
/// carry. This is deliberately NOT [`crate::ir::visit::walk_expr_default`]:
/// the borrow-source collectors must NOT descend into `Call`/`BinOp`/
/// `Borrow`/`Update`/`Field`/`ReadRef`/... operand sub-expressions,
/// because the only sites they inspect are `Stmt::Let`s, and a `Let`
/// can only live inside a `Block` reached through one of these four
/// control-flow variants. Descending into operand sub-expressions
/// would reach extra (operand-nested) blocks the original walks
/// skipped and record spurious entries -- a behavior change.
///
/// Observation is per-`Stmt` (done in the callers' `visit_block` /
/// `visit_stmt` overrides); this helper only threads the recursion, so
/// every family shares ONE copy of the "which positions hold nested
/// blocks" decision instead of re-listing it in a `_in_expr` partner.
fn walk_nested_blocks<V: Visitor + ?Sized>(v: &mut V, e: &Expr) {
    match e {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            v.visit_expr(cond);
            v.visit_block(then_branch);
            v.visit_block(else_branch);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            v.visit_expr(selector);
            for arm in cases {
                v.visit_block(&arm.body);
            }
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            for (_, init) in iter_locals {
                v.visit_expr(init);
            }
            v.visit_block(header);
            v.visit_expr(cond);
            v.visit_block(body);
        }
        Expr::Quantifier { body, .. } => v.visit_block(body),
        _ => {}
    }
}

/// Recurse a `Stmt`'s value expression for nested blocks, ignoring the
/// let-pattern binders (none of these collectors inspect binders via
/// the walk). Dispatches through `visit_expr` so the override's
/// per-stmt observation runs at each nested block.
fn walk_stmt_value<V: Visitor + ?Sized>(v: &mut V, s: &Stmt) {
    match s {
        Stmt::Let { value, .. } => v.visit_expr(value),
        Stmt::Eval(e) => v.visit_expr(e),
    }
}

/// Recurse a `BlockTail`'s carried expression for nested blocks. Every
/// tail variant carries one expression; `Abort` carries the abort
/// code. Mirrors the `_in_tail` partners (the family that skipped
/// `Abort` overrides `visit_tail` to short-circuit instead).
fn walk_tail_value<V: Visitor + ?Sized>(v: &mut V, t: &BlockTail) {
    let e = match t {
        BlockTail::Value(e) => e,
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => value,
        BlockTail::Abort { code } => code,
    };
    v.visit_expr(e);
}

/// Walk a function body and populate `out` with every
/// `Stmt::Let { pattern: [v], value: Expr::BorrowVecIndex | BorrowMapKey { .. } }`
/// site. Called by the function renderer before `render_function_body`
/// so the `WriteBack` arms can recover runtime indices / keys.
pub(in crate::render) fn collect_borrow_sources(
    block: &Block,
    out: &mut BTreeMap<VarId, RuntimeBorrowSource>,
) {
    struct W<'a> {
        out: &'a mut BTreeMap<VarId, RuntimeBorrowSource>,
    }
    impl Visitor for W<'_> {
        fn visit_block(&mut self, b: &Block) {
            for s in &b.stmts {
                if let Stmt::Let { pattern, value } = s {
                    if let [Some(v)] = pattern.as_slice() {
                        match value {
                            Expr::Borrow {
                                step: crate::ir::path::PathStep::VecIndex(index),
                                ..
                            } => {
                                self.out.insert(
                                    v.clone(),
                                    RuntimeBorrowSource::VecIndex {
                                        index: (**index).clone(),
                                    },
                                );
                            }
                            Expr::Borrow {
                                step: crate::ir::path::PathStep::MapKey { key, key_type, .. },
                                ..
                            } => {
                                self.out.insert(
                                    v.clone(),
                                    RuntimeBorrowSource::MapKey {
                                        key: (**key).clone(),
                                        key_type: key_type.clone(),
                                    },
                                );
                            }
                            // Inherit the parent's borrow source through
                            // `WriteBack { node: Reference(parent), .. }`
                            // chains: at the IR level these render as
                            // `let v := Mutation.set parent <inner>`,
                            // which preserves `parent.path`, so `v`
                            // shares the same borrow ancestry. Without
                            // this, lookups for `v` in `borrow_sources`
                            // return None and the writeback dispatch
                            // falls back to identity-insert.
                            Expr::WriteBack {
                                node: crate::ir::BorrowNode::Reference(parent_name),
                                ..
                            } => {
                                if let Some(src) = self.out.get(parent_name).cloned() {
                                    self.out.insert(v.clone(), src);
                                }
                            }
                            // Inherit the borrow source through `WriteRef`
                            // (`*r := v`) chains. This is the IR shape stage 3
                            // emits for `*stored = value` after a
                            // `dynamic_field::borrow_mut`: `stored` is bound by a
                            // `BorrowMapKey` (recorded above), then
                            // `let w := *stored := value` is an `Expr::WriteRef`
                            // whose result `w` feeds the enclosing
                            // `WriteBack { edge: MapKey }` into the owning struct.
                            // Without propagating `stored`'s key to `w`, the
                            // writeback can't recover the key in
                            // `apply_edge_inner_only` and degrades to the identity
                            // no-op `(fun m _ _ => m)` -- dropping the update
                            // (e.g. momentum `set_min_tick_range_factor`, whose
                            // first call hits the borrow_mut branch because pool
                            // init pre-adds the key with a default value).
                            Expr::WriteRef { reference, .. } => {
                                if let Expr::Var(ref_var) = reference.as_ref() {
                                    if let Some(src) = self.out.get(ref_var).cloned() {
                                        self.out.insert(v.clone(), src);
                                    }
                                }
                            }
                            // Inherit through the stage-4 lowered forms: a
                            // value-form Update chain rebinding the parent
                            // (`let p2 = Update{.., base: ..Var(p)..}`)
                            // preserves p's borrow ancestry the same way
                            // the WriteBack it replaced did.
                            Expr::Update { base, .. } => {
                                let mut root = base.as_ref();
                                while let Expr::Update { base, .. } | Expr::ReadRef(base) = root {
                                    root = base.as_ref();
                                }
                                if let Expr::Var(root_var) = root {
                                    if let Some(src) = self.out.get(root_var).cloned() {
                                        self.out.insert(v.clone(), src);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    // Recurse the value for nested blocks (matches the
                    // original `collect_borrow_sources_in_expr(value)`
                    // call) BEFORE the If/Match common-source step below.
                    self.visit_expr(value);
                    // If/Match common-source propagation. A
                    // `let v := if c then a else b` (or `match`) where EVERY
                    // branch tail resolves -- through the `out` map just
                    // populated by the recursion above -- to the SAME borrow
                    // source means `v` shares that source. Covers conditional
                    // borrow_mut threading, e.g. cetus factory
                    // `add_allowed_pair_config`: `let mgr := if !contains then
                    // <mgr with the freshly-added entry> else <mgr>`, where both
                    // arms trace back to the `dof::borrow_mut` source. Without
                    // this, the outer dof writeback can't recover the (non-
                    // concrete String) key and degrades to the identity no-op.
                    if let [Some(v)] = pattern.as_slice() {
                        if !self.out.contains_key(v) {
                            if let Some(src) = if_match_common_source(value, None, self.out) {
                                self.out.insert(v.clone(), src);
                            }
                        }
                    } else if pattern.len() > 1 {
                        // Multi-slot tuple-`if`/`match`:
                        // `let (v0, .., vn) := if c then (a0, .., an) else (b0, .., bn)`.
                        // Propagate per slot -- the i-th tuple element of every branch
                        // must trace to the same source. Covers register-style helpers
                        // that thread `(mgr, ctx) := if .. then (<mgr+entry>, ..) else
                        // (<mgr>, ..)`, where slot 0 (the borrowed manager) shares the
                        // dof::borrow_mut source but slot 1 (ctx) does not.
                        for (i, slot) in pattern.iter().enumerate() {
                            if let Some(v) = slot {
                                if !self.out.contains_key(v) {
                                    if let Some(src) =
                                        if_match_common_source(value, Some(i), self.out)
                                    {
                                        self.out.insert(v.clone(), src);
                                    }
                                }
                            }
                        }
                    }
                } else if let Stmt::Eval(e) = s {
                    self.visit_expr(e);
                }
            }
            walk_tail_value(self, &b.tail);
        }

        fn visit_expr(&mut self, e: &Expr) {
            walk_nested_blocks(self, e);
        }
    }
    let mut w = W { out };
    w.visit_block(block);
}

/// Program-aware companion to `collect_borrow_sources`: record the
/// borrowed VALUE produced by a witness-gated map `borrow_mut` -- scallop
/// `x::wit_table::borrow_mut(witness, &mut self, key)`, which lowers to
/// `(Mutation V, Mutation WitTable)` -- as a `MapKey` borrow source keyed
/// by the call's last argument. `collect_borrow_sources` only matches the
/// IR `BorrowMapKey` primitive, so a tuple-returning USER borrow_mut over
/// a `WitTable { table : Table K V, .. }` is otherwise invisible, and the
/// later writeback of the mutated value into the inner `.table` can't
/// recover the key -- it degrades to the identity `(fun m _ _ => m)` no-op
/// and the mutation is silently dropped (e.g. scallop reserve balance
/// sheet `cash` stays 0 -> spurious `reserve_not_enough`).
///
/// Must run BEFORE `collect_borrow_sources` so its WriteBack/WriteRef
/// inheritance propagates the recorded source through the borrowed
/// value's field-set chain to the eventual writeback child.
pub(in crate::render) fn collect_map_borrow_sources(
    program: &Program,
    block: &Block,
    out: &mut BTreeMap<VarId, RuntimeBorrowSource>,
) {
    struct W<'a> {
        program: &'a Program,
        out: &'a mut BTreeMap<VarId, RuntimeBorrowSource>,
    }
    impl Visitor for W<'_> {
        fn visit_stmt(&mut self, s: &Stmt) {
            if let Stmt::Let { pattern, value } = s {
                if let Expr::Call {
                    fun,
                    type_args,
                    args,
                } = value
                {
                    if is_witness_map_borrow_mut(self.program, *fun) {
                        // (witness, self: Mutation Map, key)
                        //   -> (Mutation V, Mutation Map).
                        // Slot 0 is the borrowed value; the key is the
                        // last positional arg; the container's key type
                        // is the map's 2nd type param (W, K, V).
                        if let Some(Some(v0)) = pattern.first() {
                            if let Some(key) = args.last() {
                                let key_type =
                                    type_args.get(1).cloned().unwrap_or(crate::ir::Type::Unit);
                                self.out
                                    .entry(v0.clone())
                                    .or_insert(RuntimeBorrowSource::MapKey {
                                        key: key.clone(),
                                        key_type,
                                    });
                            }
                        }
                    } else if is_option_borrow_mut(self.program, *fun) {
                        // `std::option::borrow_mut(&mut self) -> &mut T`
                        // lowers to `(Mutation T, Mutation MoveOption)`,
                        // borrowing the Some payload at vec index 0
                        // (MoveOption is modeled as a 0/1-element list).
                        // Record slot 0 as a `VecIndex { index: 0 }` source
                        // so a writeback whose child derives from it (e.g.
                        // `vec_set::insert` on the borrowed value, as in
                        // `wit_table::add`'s `.keys` update) can recover the
                        // index and emit `writeBackVecIndex .. 0 ..` instead
                        // of the path-less `writeBackVecIndex` no-op.
                        if let Some(Some(v0)) = pattern.first() {
                            self.out
                                .entry(v0.clone())
                                .or_insert(RuntimeBorrowSource::VecIndex {
                                    index: Expr::Const(Const::UInt {
                                        bits: 64,
                                        value: U256::from(0u64),
                                    }),
                                });
                        }
                    }
                }
            }
            walk_stmt_value(self, s);
        }

        fn visit_expr(&mut self, e: &Expr) {
            walk_nested_blocks(self, e);
        }

        fn visit_tail(&mut self, t: &BlockTail) {
            walk_tail_value(self, t);
        }
    }
    let mut w = W { program, out };
    w.visit_block(block);
}

/// True for the witness-gated map `borrow_mut` whose result slot 0 is a
/// borrowed map value: `x::wit_table::borrow_mut`. Matched by module +
/// function name (the package qualifier varies by client vendoring).
pub(in crate::render) fn is_witness_map_borrow_mut(
    program: &Program,
    fid: crate::ir::FunId,
) -> bool {
    program
        .functions
        .get(&fid)
        .and_then(|f| program.modules.get(&f.module).map(|m| (m, f)))
        .map(|(m, f)| m.name == "wit_table" && f.name == "borrow_mut")
        .unwrap_or(false)
}

/// True for `std::option::borrow_mut` -- borrows the Some payload, which
/// MoveOption models as vec index 0. Slot 0 of its `(Mutation T,
/// Mutation MoveOption)` return is the borrowed payload.
pub(in crate::render) fn is_option_borrow_mut(program: &Program, fid: crate::ir::FunId) -> bool {
    program
        .functions
        .get(&fid)
        .and_then(|f| program.modules.get(&f.module).map(|m| (m, f)))
        .map(|(m, f)| m.name == "option" && f.name == "borrow_mut")
        .unwrap_or(false)
}

/// For a `let v := if .. then a else b` / `match` value, return the
/// single borrow source shared by ALL branch tails (looked up in
/// `out`), or `None` if the branches disagree or any tail isn't a
/// recorded borrow var. Used by `collect_borrow_sources` to thread a
/// borrow source through conditional re-binding.
///
/// `slot` selects which value the branch tail contributes:
///   * `None` -- the tail itself is the bound var (single-slot let).
///   * `Some(i)` -- the tail is an `Expr::Tuple` and its `i`-th element
///     is the bound var (multi-slot destructuring let).
pub(in crate::render) fn if_match_common_source(
    value: &Expr,
    slot: Option<usize>,
    out: &BTreeMap<VarId, RuntimeBorrowSource>,
) -> Option<RuntimeBorrowSource> {
    let tails: Vec<&Expr> = match value {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => [then_branch, else_branch]
            .into_iter()
            .filter_map(|b| match &b.tail {
                BlockTail::Value(e) => Some(e),
                _ => None,
            })
            .collect(),
        Expr::Match { cases, .. } => cases
            .iter()
            .filter_map(|arm| match &arm.body.tail {
                BlockTail::Value(e) => Some(e),
                _ => None,
            })
            .collect(),
        _ => return None,
    };
    if tails.is_empty() {
        return None;
    }
    let mut found: Option<RuntimeBorrowSource> = None;
    for t in tails {
        // Project the slot: for a tuple branch, take the i-th element.
        let leaf = match slot {
            None => t,
            Some(i) => match t {
                Expr::Tuple(es) => es.get(i)?,
                _ => return None,
            },
        };
        let src = match leaf {
            Expr::Var(vv) => out.get(vv).cloned()?,
            _ => return None,
        };
        match &found {
            None => found = Some(src),
            Some(existing) if *existing == src => {}
            Some(_) => return None,
        }
    }
    found
}

/// Walk a function body and populate `out` with every
/// `Stmt::Let { pattern: [_, Some(parent_alias)], value: Expr::Call { args, .. } }`
/// site where the call returns a 2-tuple (the canonical Move borrow_mut shape
/// after stage 3 augmentation: `(value_mut, parent_pass_through)`).
///
/// The key is taken to be `args.last()` -- works for both the native
/// `Dynamic_field.borrow_mut(parent, key)` and thin Move wrappers
/// `wrap(parent, ..., key)`. Recorded entries are read by
/// `apply_edge_inner_only`'s cross-type bridge branch via
/// `ExprCtx::borrow_mut_origins`.
///
/// Entries are recorded unconditionally on shape match. The actual gating on
/// "parent has a ghost `dynamic_fields[_N]` field matching the child's value
/// type" happened at use time in the (deleted) ghost writeback path. A 2-slot
/// let from a non-borrow_mut call simply never finds a matching ghost field
/// and falls through to the existing placeholder emission -- so this walker
/// is safe to be permissive.
pub(in crate::render) fn collect_borrow_mut_origins(
    block: &Block,
    out: &mut BTreeMap<VarId, BorrowMutOrigin>,
) {
    struct W<'a> {
        out: &'a mut BTreeMap<VarId, BorrowMutOrigin>,
    }
    impl Visitor for W<'_> {
        fn visit_stmt(&mut self, s: &Stmt) {
            if let Stmt::Let { pattern, value } = s {
                if pattern.len() == 2 {
                    if let Some(parent_alias) = &pattern[1] {
                        if let Expr::Call { args, .. } = value {
                            if let Some(key) = args.last() {
                                self.out.insert(
                                    parent_alias.clone(),
                                    BorrowMutOrigin { key: key.clone() },
                                );
                            }
                        }
                    }
                }
            }
            walk_stmt_value(self, s);
        }

        fn visit_expr(&mut self, e: &Expr) {
            walk_nested_blocks(self, e);
        }

        fn visit_tail(&mut self, t: &BlockTail) {
            // `BlockTail::Abort` carries only the abort code, which the
            // original `collect_borrow_mut_origins_in_tail` skipped
            // outright (the OTHER families recursed into it). Preserve
            // that asymmetry: do not recurse into `code`.
            if matches!(t, BlockTail::Abort { .. }) {
                return;
            }
            walk_tail_value(self, t);
        }
    }
    let mut w = W { out };
    w.visit_block(block);
}

/// Classifies a Sui-framework mutating native by where the
/// post-mutation container value lands in the let-destructuring of
/// its result. Returned indices are 0-based positions in the
/// `Stmt::Let { pattern }` slice.
///
/// * `Single0` — the call returns just the new container; bound by
///   a 1-slot let `let new_bag := Bag.add ...`.
/// * `TupleSlot(n)` — the call returns a tuple whose `n`-th slot
///   is the new container. E.g. `Bag.remove` returns `(V, Bag)`,
///   so the new bag is slot 1 in
///   `let (removed_val, new_bag) := Bag.remove ...`.
///
/// Used by `collect_borrow_mut_derivatives` to record the right
/// derived variable as a derivative of the borrow source.
#[derive(Debug, Clone, Copy)]
pub(in crate::render) enum MutatingNativeReturnShape {
    Single0,
    TupleSlot(usize),
}

pub(in crate::render) fn mutating_native_return_shape(
    program: &Program,
    fid: crate::ir::FunId,
) -> Option<MutatingNativeReturnShape> {
    use MutatingNativeReturnShape::*;
    // Native mutating container ops (bag / table / dynamic_field / ...).
    if let Some(decl) = program.natives.decls.get(&fid) {
        if let Some(m) = program.modules.get(&decl.module) {
            if m.package_name == "Sui" {
                match (m.name.as_str(), decl.name.as_str()) {
                    // 1-slot: native returns the new container directly.
                    ("bag", "add") => return Some(Single0),
                    ("object_bag", "add") => return Some(Single0),
                    ("table", "add") => return Some(Single0),
                    ("vec_map", "insert") => return Some(Single0),
                    // `vec_set::{insert,remove}(self: &mut VecSet, k): ()`
                    // lower to `Vec_set.{insert,remove}(self, k): VecSet`
                    // (Single0). Recognising them threads
                    // `borrow_mut_derivatives` from the new VecSet back
                    // to the originating `borrow_mut` source, so a
                    // `vec_set::insert(table::borrow_mut(&mut t, k), x)`
                    // writeback recovers the (non-concrete) container key
                    // and emits `Table.set` instead of the identity no-op
                    // (cetus-clmm factory `add_allowed_pair_config`'s
                    // `allowed_pair_config: Table<TypeName, VecSet<u32>>`).
                    ("vec_set", "insert") => return Some(Single0),
                    ("vec_set", "remove") => return Some(Single0),
                    ("dynamic_field", "add") => return Some(Single0),
                    ("dynamic_object_field", "add") => return Some(Single0),
                    // 2-slot: native returns `(removed_value, new_container)`.
                    // The new container is at slot 1.
                    ("bag", "remove") => return Some(TupleSlot(1)),
                    ("object_bag", "remove") => return Some(TupleSlot(1)),
                    ("table", "remove") => return Some(TupleSlot(1)),
                    // `vec_map::remove(&mut self, &K): (K, V)` returns a
                    // PAIR, so the augmented `&mut self` VecMap lands at
                    // slot 2 (after K, V) -- not slot 1 like the
                    // single-value `remove`s above. Recording the
                    // derivative at slot 1 (the V) instead of the VecMap
                    // means a subsequent writeback can't recover the
                    // borrow path and silently drops the mutation
                    // (current-lending referral `claim_rebates`'s
                    // `user_rebates.remove(&coin_type)`).
                    ("vec_map", "remove") => return Some(TupleSlot(2)),
                    ("dynamic_field", "remove") => return Some(TupleSlot(1)),
                    ("dynamic_object_field", "remove") => return Some(TupleSlot(1)),
                    _ => {}
                }
            } else if m.package_name == "MoveStdlib" && m.name == "vector" {
                // `std::vector` mutating ops lower to value-form rebinds
                // returning the new list (Stage 3 augments the `&mut self`
                // return). Recording the derivative threads
                // `borrow_mut_derivatives` from the new list back to the
                // originating `borrow_mut` / `returning_mut_ref` source, so a
                // writeback whose child is e.g.
                // `vector::push_back(table::borrow_mut(&mut t, k).val, x)`
                // recovers the container key and emits `Table.set` instead of
                // re-wrapping via a fresh `ofLocal` -- whose empty path makes
                // writeBackMapKeyAuto silently drop the write via `| _ => p`
                // (securitize `record_investor_issuance`'s
                // `investor_issuances: Table<String, vector<Issuance>>`).
                match decl.name.as_str() {
                    // 1-slot: native returns the new list directly.
                    "push_back" => return Some(Single0),
                    "swap" => return Some(Single0),
                    "reverse" => return Some(Single0),
                    "append" => return Some(Single0),
                    "insert" => return Some(Single0),
                    // 2-slot: native returns `(removed_value, new_list)`.
                    "pop_back" => return Some(TupleSlot(1)),
                    "remove" => return Some(TupleSlot(1)),
                    "swap_remove" => return Some(TupleSlot(1)),
                    _ => {}
                }
            }
        }
    }
    // Translated Sui value-type functions that thread a borrowed-mut
    // `self` through and return the augmented `Mutation` in a tuple
    // slot. These are Move-defined (not natives), so they don't appear
    // in `program.natives.decls`, but a writeback whose child is their
    // result still needs to recover the container key from the
    // borrowed-mut source (e.g. cetus-clmm `rewarder::deposit_reward`:
    // `balance::join(self: &mut Balance, b): u64` lowers to Lean
    // `(u64, Mutation Balance)`; without threading the derivative back
    // to the originating `bag::borrow_mut`, the writeback degrades to
    // the identity `(fun m _ _ => m)` and the joined balance is
    // silently dropped -> `balance_of` reads 0 -> spurious abort).
    if let Some(f) = program.functions.get(&fid) {
        if let Some(m) = program.modules.get(&f.module) {
            if m.package_name == "Sui" {
                match (m.name.as_str(), f.name.as_str()) {
                    // `balance::join(&mut self, b): u64` -> `(u64, Mutation Balance)`.
                    ("balance", "join") => return Some(TupleSlot(1)),
                    _ => {}
                }
            }
        }
    }
    // General user-defined mutation pass-through. Any function whose
    // first parameter is a `Mutation X` (MutableRef) and whose return
    // threads a `Mutation X` of the SAME inner type back is the
    // standard Move `&mut self`-threading shape: the prover IR lowers
    // `fun f(self: &mut X, ..) -> &mut X` to `f(Mutation X, ..) ->
    // Mutation X` (Single0) and tuple-returning threaders to a
    // `(.., Mutation X, ..)` slot. User wrappers around a borrowed
    // map/struct mutation -- e.g. x_oracle
    // `update_price_feed(&mut PriceFeed, ..) -> &mut PriceFeed` invoked
    // on a `Table<TypeName, PriceFeed>` borrow_mut -- need the same
    // derivative threading the Sui-native allowlist above provides, or
    // the writeback whose child is their result can't recover the
    // originating `borrow_mut` container key and degrades to the
    // identity `(fun m _ _ => m)` (the mutation is silently dropped).
    // Compare INNER types only: a MutableRef's `root` differs between
    // the borrowed parameter and the returned self-reference.
    if let Some(f) = program.functions.get(&fid) {
        let first_inner = f.signature.params.first().and_then(|p| match &p.ty {
            crate::ir::Type::MutableRef { inner, .. } => Some((**inner).clone()),
            _ => None,
        });
        if let Some(first_inner) = first_inner {
            match &f.signature.return_type {
                crate::ir::Type::MutableRef { inner, .. } if **inner == first_inner => {
                    return Some(Single0);
                }
                crate::ir::Type::Tuple(elems) => {
                    for (n, e) in elems.iter().enumerate() {
                        if let crate::ir::Type::MutableRef { inner, .. } = e {
                            if **inner == first_inner {
                                return Some(TupleSlot(n));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
    None
}

/// Trace `e` back to a source borrowed-mut variable, walking through
/// `.val` projections, prior recorded derivatives, and direct
/// borrow-source variables.
///
/// Returns `Some(src)` where `src` is the variable that names the
/// upstream borrowed Mutation (e.g. the `let t = BorrowMapKey ...`
/// binding, or the second-slot pass-through of a borrow_mut'd
/// destructuring). Returns `None` otherwise.
pub(in crate::render) fn trace_to_borrow_mut_source(
    e: &Expr,
    borrow_sources: &BTreeMap<VarId, RuntimeBorrowSource>,
    borrow_mut_origins: &BTreeMap<VarId, BorrowMutOrigin>,
    derivatives: &BTreeMap<VarId, VarId>,
) -> Option<VarId> {
    // Strip a `.val` projection if present (`ReadRef(Var(v))`) -- the
    // typical shape stage 3 produces for accessing a Mutation's
    // underlying value at a native call site.
    let v = match e {
        Expr::ReadRef(inner) => {
            if let Expr::Var(v) = &**inner {
                v.clone()
            } else {
                return None;
            }
        }
        Expr::Var(v) => v.clone(),
        _ => return None,
    };
    // Direct match: `v` is itself a borrowed-mut source.
    if borrow_sources.contains_key(&v) || borrow_mut_origins.contains_key(&v) {
        return Some(v);
    }
    // Transitive match: `v` was derived from a prior mutating-native call.
    derivatives.get(&v).cloned()
}

/// Walk a function body and record, for each variable `v` bound by
/// `Stmt::Let { pattern: [v], value: Call(<mutating_native>, [<src>.val, ...]) }`,
/// the source borrowed-mut variable that `v` "logically replaces".
///
/// The renderer uses this map at writeback sites to thread the new
/// container value back through the borrowed mutation's path -- which
/// is the only way to recover the runtime `.mapKey k` edge that
/// `Prover.Mutation.Mutation.writeBackGhostMapKey` needs.
///
/// Without this, the renderer wraps the new value in
/// `Mutation.ofLocal AnyKey ...` (empty path), the writeback can't
/// find the key, and the parent struct is silently left unchanged.
///
/// Allowlist-gated -- see `mutating_native_return_shape`.
/// Transitive: `let t1 := Bag.add src.val k v; let t2 := Bag.add t1 k2 v2`
/// records both `t1 -> src` and `t2 -> src`.
pub(in crate::render) fn collect_borrow_mut_derivatives(
    program: &Program,
    block: &Block,
    borrow_sources: &BTreeMap<VarId, RuntimeBorrowSource>,
    borrow_mut_origins: &BTreeMap<VarId, BorrowMutOrigin>,
    out: &mut BTreeMap<VarId, VarId>,
) {
    struct W<'a> {
        program: &'a Program,
        borrow_sources: &'a BTreeMap<VarId, RuntimeBorrowSource>,
        borrow_mut_origins: &'a BTreeMap<VarId, BorrowMutOrigin>,
        out: &'a mut BTreeMap<VarId, VarId>,
    }
    impl Visitor for W<'_> {
        fn visit_stmt(&mut self, s: &Stmt) {
            if let Stmt::Let { pattern, value } = s {
                if let Expr::Call { fun, args, .. } = value {
                    if let Some(shape) = mutating_native_return_shape(self.program, *fun) {
                        if let Some(first_arg) = args.first() {
                            if let Some(src) = trace_to_borrow_mut_source(
                                first_arg,
                                self.borrow_sources,
                                self.borrow_mut_origins,
                                self.out,
                            ) {
                                // Locate the derived variable in the
                                // destructuring pattern according to the
                                // native's return shape.
                                let derived_slot = match shape {
                                    MutatingNativeReturnShape::Single0 => 0,
                                    MutatingNativeReturnShape::TupleSlot(n) => n,
                                };
                                if let Some(Some(derived)) = pattern.get(derived_slot) {
                                    self.out.insert(derived.clone(), src);
                                }
                            }
                        }
                    }
                }
            }
            walk_stmt_value(self, s);
        }

        fn visit_expr(&mut self, e: &Expr) {
            walk_nested_blocks(self, e);
        }

        fn visit_tail(&mut self, t: &BlockTail) {
            walk_tail_value(self, t);
        }
    }
    let mut w = W {
        program,
        borrow_sources,
        borrow_mut_origins,
        out,
    };
    w.visit_block(block);
}

/// Walk a function body and record, for each `Stmt::Let { pattern,
/// value: Call(<mutating_native>, [<src>, ...]) }`, the mapping
/// `derived_slot_var -> src_var` -- where `src` is the (Mutation-
/// typed) first argument that the native writes back.
///
/// This is a strictly-broader sibling of
/// `collect_borrow_mut_derivatives`: it does NOT require `src` to be
/// a recognized container borrow source. The only consumer is the
/// `Expr::IsParent` child renderer, which uses it to thread the
/// borrow path of a value-form mutating-native rebind result back
/// through `Mutation.set src derived` (preserving loc + path) rather
/// than `Mutation.ofLocal` (which resets both and makes `isParent`
/// always false, silently dropping a conditional writeback).
///
/// Concrete case: `liquidity_miner::support_coin` does
/// `let $t7 = table::add($t7, ..)` where `$t7` came from
/// `get_reward_table_mut(self, reward_type) -> &mut Table` (a
/// CONDITIONAL `&mut self.deposit` / `&mut self.borrow`). The
/// subsequent `is_parent(ref(self), .deposit, $t7)` must see `$t7`'s
/// `[.structField .deposit]` path to dispatch the right writeback.
///
/// Transitive: `let t1 = table::add(src, ..); let t2 = table::add(t1, ..)`
/// records both `t1 -> src` and `t2 -> src` (chases to the root).
pub(in crate::render) fn collect_mutref_rebind_sources(
    program: &Program,
    block: &Block,
    out: &mut BTreeMap<VarId, VarId>,
) {
    struct W<'a> {
        program: &'a Program,
        out: &'a mut BTreeMap<VarId, VarId>,
    }
    impl Visitor for W<'_> {
        fn visit_stmt(&mut self, s: &Stmt) {
            if let Stmt::Let { pattern, value } = s {
                if let Expr::Call { fun, args, .. } = value {
                    if let Some(shape) = mutating_native_return_shape(self.program, *fun) {
                        if let Some(first_arg) = args.first() {
                            let src = match first_arg {
                                Expr::ReadRef(inner) => match &**inner {
                                    Expr::Var(v) => Some(v.clone()),
                                    _ => None,
                                },
                                Expr::Var(v) => Some(v.clone()),
                                _ => None,
                            };
                            if let Some(src) = src {
                                let root = self.out.get(&src).cloned().unwrap_or(src);
                                let derived_slot = match shape {
                                    MutatingNativeReturnShape::Single0 => 0,
                                    MutatingNativeReturnShape::TupleSlot(n) => n,
                                };
                                if let Some(Some(derived)) = pattern.get(derived_slot) {
                                    self.out.insert(derived.clone(), root);
                                }
                            }
                        }
                    }
                }
                // If-join phi rule: `let (.., v_k, ..) := if c then
                // (.., a_k, ..) else (.., b_k, ..)` where `a_k` and
                // `b_k` root-chase (through mappings recorded so far)
                // to the SAME source var records `v_k -> root`. This
                // is the conditional-mutation rebind of a borrowed
                // container element, e.g. Move's
                //   `if (table::contains(t, k)) { table::remove(t, k); }`
                // on `t = vector::borrow_mut(&mut v, i)`: the then-arm
                // rebinds `t` through the value-form `remove` (mapped
                // to the borrow var by the Call rule above), the else-
                // arm passes the borrow var through unchanged, and the
                // join var is the same borrowed cell on both paths. A
                // later `table::add(<join>, ..)` then chases to the
                // original `BorrowVecIndex`/`BorrowMapKey` source, so
                // its writeback recovers the index/key instead of
                // `ofLocal`-wrapping (empty path) and silently
                // dropping the write (navi-lending v1
                // `incentive::base_claim_reward` /
                // `incentive::update_reward` reward-table advances).
                // Inner-branch mappings are recorded AFTER this outer
                // Let is visited, so the caller iterates the walk to a
                // fixpoint for the rule to see them.
                if let Expr::If {
                    then_branch,
                    else_branch,
                    ..
                } = value
                {
                    let then_vals = tail_slot_vars(then_branch, pattern.len());
                    let else_vals = tail_slot_vars(else_branch, pattern.len());
                    for (k, derived) in pattern.iter().enumerate() {
                        let (Some(derived), Some(Some(tv)), Some(Some(ev))) =
                            (derived, then_vals.get(k), else_vals.get(k))
                        else {
                            continue;
                        };
                        let troot = self.out.get(tv).cloned().unwrap_or_else(|| tv.clone());
                        let eroot = self.out.get(ev).cloned().unwrap_or_else(|| ev.clone());
                        if troot == eroot && *derived != troot {
                            self.out.insert(derived.clone(), troot);
                        }
                    }
                }
            }
            walk_stmt_value(self, s);
        }

        fn visit_expr(&mut self, e: &Expr) {
            walk_nested_blocks(self, e);
        }

        fn visit_tail(&mut self, t: &BlockTail) {
            walk_tail_value(self, t);
        }
    }
    // Iterate to a fixpoint: the If-join phi rule consults mappings
    // recorded for the arms' inner statements, which a single pass
    // only records after the enclosing `Let` was already visited.
    // The map is monotone (insert-only), so the loop terminates.
    loop {
        let before = out.len();
        let mut w = W {
            program,
            out: &mut *out,
        };
        w.visit_block(block);
        if out.len() == before {
            break;
        }
    }
}

/// Per-slot variable of a block's tail value, aligned with a
/// destructuring pattern of `arity` slots: `Tuple(es)` yields each
/// slot's `Var` (peeling one `ReadRef`), a single non-tuple tail
/// yields slot 0 for `arity == 1`. Non-var slots are `None`.
fn tail_slot_vars(block: &Block, arity: usize) -> Vec<Option<VarId>> {
    let as_var = |e: &Expr| -> Option<VarId> {
        match e {
            Expr::Var(v) => Some(v.clone()),
            Expr::ReadRef(inner) => match &**inner {
                Expr::Var(v) => Some(v.clone()),
                _ => None,
            },
            _ => None,
        }
    };
    match &block.tail {
        BlockTail::Value(Expr::Tuple(es)) => es.iter().map(as_var).collect(),
        BlockTail::Value(e) if arity == 1 => vec![as_var(e)],
        _ => vec![None; arity],
    }
}

/// Walk a function body and find let-bound `BorrowLoc(x)` temps
/// whose every use is a `ReadRef(Var(v))` (i.e. the renderer would
/// emit them as `v.val`). For such temps the wrap+unwrap is a pure
/// round-trip; we record `v -> x` so the body renderer can drop the
/// `let v := Mutation.ofLocal AnyKey ...` statement and emit the
/// bare source `x` wherever `v` would otherwise be unwrapped.
///
/// This is a renderer-only peephole: the IR remains unchanged, so
/// downstream stages still see the BorrowLoc/ReadRef pair. It
/// eliminates `AnyKey` references in lemma function bodies whose
/// signatures don't expose Mutation, which is what triggers Lean's
/// "can't synthesize implicit argument `__MutKey`" failure at every
/// caller (see the Ascii / MoveOption.destroy_some case in
/// `plans/lean-pipeline/lake-build-remaining-errors.md`).
pub(in crate::render) fn collect_redundant_borrowloc(
    program: &Program,
    block: &Block,
    out: &mut BTreeMap<VarId, VarId>,
) {
    // First pass: collect candidate `(v, x)` from
    // `let v := BorrowLoc(x)` in any block reachable from the body.
    let mut candidates: BTreeMap<VarId, VarId> = BTreeMap::new();
    gather_borrowloc_candidates_block(block, &mut candidates);

    // Second pass: scan every use of every candidate `v`. A use is
    // PERMITTED if it appears as `ReadRef(Var(v))` (explicit `.val`
    // unwrap) or as `Var(v)` in a `Call` arg slot where the renderer
    // would auto-unwrap (callee is native, or callee param is not
    // `MutableRef`). Otherwise the candidate is DISQUALIFIED.
    let mut disqualified: std::collections::BTreeSet<VarId> = std::collections::BTreeSet::new();
    check_uses_block(program, block, &candidates, &mut disqualified);

    for (v, x) in candidates {
        if !disqualified.contains(&v) {
            out.insert(v, x);
        }
    }
}

pub(in crate::render) fn gather_borrowloc_candidates_block(
    block: &Block,
    out: &mut BTreeMap<VarId, VarId>,
) {
    struct W<'a> {
        out: &'a mut BTreeMap<VarId, VarId>,
    }
    impl Visitor for W<'_> {
        fn visit_stmt(&mut self, s: &Stmt) {
            if let Stmt::Let { pattern, value } = s {
                if let [Some(v)] = pattern.as_slice() {
                    if let Expr::BorrowLoc(x) = value {
                        self.out.insert(v.clone(), x.clone());
                    }
                }
            }
            walk_stmt_value(self, s);
        }

        fn visit_expr(&mut self, e: &Expr) {
            walk_nested_blocks(self, e);
        }

        fn visit_tail(&mut self, t: &BlockTail) {
            walk_tail_value(self, t);
        }
    }
    let mut w = W { out };
    w.visit_block(block);
}

pub(in crate::render) fn check_uses_block(
    program: &Program,
    block: &Block,
    candidates: &BTreeMap<VarId, VarId>,
    disqualified: &mut std::collections::BTreeSet<VarId>,
) {
    for s in &block.stmts {
        match s {
            Stmt::Let { pattern: _, value } => {
                if let Expr::BorrowLoc(_) = value {
                    // Skip -- this is a candidate introduction site.
                } else {
                    check_uses_expr(program, value, candidates, disqualified);
                }
            }
            Stmt::Eval(e) => check_uses_expr(program, e, candidates, disqualified),
        }
    }
    let tail_e = match &block.tail {
        BlockTail::Value(e) => e,
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => value,
        BlockTail::Abort { code } => code,
    };
    check_uses_expr(program, tail_e, candidates, disqualified);
}

pub(in crate::render) fn check_uses_expr(
    program: &Program,
    e: &Expr,
    candidates: &BTreeMap<VarId, VarId>,
    disqualified: &mut std::collections::BTreeSet<VarId>,
) {
    match e {
        Expr::Borrow { step, base } => {
            for __pe in step.exprs() {
                check_uses_expr(program, __pe, candidates, disqualified);
            }
            check_uses_expr(program, base, candidates, disqualified);
        }
        Expr::Update { step, base, value } => {
            for __pe in step.exprs() {
                check_uses_expr(program, __pe, candidates, disqualified);
            }
            check_uses_expr(program, base, candidates, disqualified);
            check_uses_expr(program, value, candidates, disqualified);
        }
        Expr::Var(v) if candidates.contains_key(v) => {
            // Bare `Var(v)` outside a `ReadRef` or auto-unwrapping
            // Call arg -- disqualify.
            disqualified.insert(v.clone());
        }
        Expr::ReadRef(inner) => {
            match inner.as_ref() {
                Expr::Var(v) if candidates.contains_key(v) => {
                    // Permitted use -- do not recurse.
                }
                other => check_uses_expr(program, other, candidates, disqualified),
            }
        }
        // `Call` args: a candidate `Var(v)` is permitted if the
        // callee auto-unwraps (callee is native, or callee's param
        // at that position is not `MutableRef`). Other args recurse
        // normally.
        Expr::Call { fun, args, .. } => {
            let callee = program.functions.get(fun);
            for (i, a) in args.iter().enumerate() {
                if let Expr::Var(v) = a {
                    if candidates.contains_key(v) {
                        // A native callee is absent from `program.functions`
                        // (it lives in `natives.decls`), so `callee` is
                        // `None` and this yields `false` (auto-unwrap,
                        // permitted) -- the param-type check subsumes the
                        // native case directly.
                        let callee_expects_mut = callee
                            .and_then(|f| f.signature.params.get(i))
                            .map(|p| matches!(p.ty, crate::ir::Type::MutableRef { .. }))
                            .unwrap_or(false);
                        if !callee_expects_mut {
                            // Auto-unwrap at render time -- permitted.
                            continue;
                        }
                    }
                }
                check_uses_expr(program, a, candidates, disqualified);
            }
        }
        // Recurse into all sub-expressions of compound forms.
        Expr::BinOp { lhs, rhs, .. } => {
            check_uses_expr(program, lhs, candidates, disqualified);
            check_uses_expr(program, rhs, candidates, disqualified);
        }
        Expr::UnOp { operand, .. } => check_uses_expr(program, operand, candidates, disqualified),
        Expr::Tuple(items) | Expr::Pack { fields: items, .. } => {
            for i in items {
                check_uses_expr(program, i, candidates, disqualified);
            }
        }
        Expr::Unpack { value, .. } => check_uses_expr(program, value, candidates, disqualified),
        Expr::Field { base, .. } => check_uses_expr(program, base, candidates, disqualified),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            check_uses_expr(program, cond, candidates, disqualified);
            check_uses_block(program, then_branch, candidates, disqualified);
            check_uses_block(program, else_branch, candidates, disqualified);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            check_uses_expr(program, selector, candidates, disqualified);
            for arm in cases {
                check_uses_block(program, &arm.body, candidates, disqualified);
            }
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            for (_, init) in iter_locals {
                check_uses_expr(program, init, candidates, disqualified);
            }
            check_uses_block(program, header, candidates, disqualified);
            check_uses_expr(program, cond, candidates, disqualified);
            check_uses_block(program, body, candidates, disqualified);
        }
        Expr::WriteRef { reference, value } => {
            check_uses_expr(program, reference, candidates, disqualified);
            check_uses_expr(program, value, candidates, disqualified);
        }
        Expr::WriteBack { child, .. } => {
            if candidates.contains_key(child) {
                disqualified.insert(child.clone());
            }
        }
        Expr::IsParent { child, .. } => {
            if candidates.contains_key(child) {
                disqualified.insert(child.clone());
            }
        }
        Expr::ToProp(inner) | Expr::ToBool(inner) => {
            check_uses_expr(program, inner, candidates, disqualified);
        }
        Expr::Quantifier { body, .. } => check_uses_block(program, body, candidates, disqualified),
        Expr::BitOp(_)
        | Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_) => {}
        Expr::LabeledBlock { .. } => {
            unreachable!("Expr::LabeledBlock should be eliminated by stage 7 helper extraction")
        }
    }
}

// ---------------------------------------------------------------------
// Adversarial coverage battery for the Visitor conversions. The borrow-
// source collectors must NOT descend into non-control-flow operand
// sub-expressions (`Call` arg / `BinOp` operand / `Borrow`/`Update`
// operand / `Field` base / `ReadRef` / `Abort` code) -- only into
// `If`/`Match`/`While`/`Quantifier` nested blocks, where `Stmt::Let`s
// live. These fixtures plant a target-shaped `Stmt::Let` in exactly
// those operand positions and assert each collector records NOTHING
// from them (matching the original hand-rolled `_in_expr` walks, which
// stopped at `_ => {}`). A regression that swapped `walk_nested_blocks`
// for the full `walk_expr_default` would record spurious entries and
// trip these.
#[cfg(test)]
mod conversion_tests {
    use super::*;
    use crate::ir::builder::{
        block, borrow_loc, call, eval, field, if_expr, just, let_stmt, let_stmt_pat, read_ref,
        tail_abort, tail_value, var,
    };
    use crate::ir::ops::BinOp;
    use crate::ir::path::PathStep;
    use crate::ir::{BorrowEdge, BorrowNode};

    fn lit0() -> Expr {
        Expr::Const(Const::UInt {
            bits: 64,
            value: U256::from(0u64),
        })
    }

    fn borrow_vec_index(base: Expr, index: Expr) -> Expr {
        Expr::Borrow {
            step: PathStep::VecIndex(Box::new(index)),
            base: Box::new(base),
        }
    }

    fn binop(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
        Expr::BinOp {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    fn write_back_ref(parent: &str, child: &str) -> Expr {
        Expr::WriteBack {
            node: BorrowNode::Reference(parent.into()),
            edge: BorrowEdge::Direct,
            child: child.into(),
            world: None,
        }
    }

    /// An `If` whose then-branch contains `let bv := &base[0]`.
    fn if_with_borrow_let(bound: &str, base: &str) -> Expr {
        if_expr(
            var("c"),
            block(
                vec![let_stmt(&[bound], borrow_vec_index(var(base), lit0()))],
                tail_value(var(bound)),
            ),
            just(var("e")),
        )
    }

    /// The borrow-let nested in non-control-flow operand positions
    /// (Call arg / BinOp operand / Borrow base / Field base / ReadRef /
    /// Abort code) must NOT be recorded -- the walk stops before them.
    #[test]
    fn borrow_sources_does_not_descend_into_operands() {
        let cases = [
            call(0, vec![if_with_borrow_let("bv", "base")]),
            binop(BinOp::Add, if_with_borrow_let("bv", "base"), var("z")),
            borrow_vec_index(if_with_borrow_let("bv", "base"), lit0()),
            field(0, 0, if_with_borrow_let("bv", "base")),
            read_ref(if_with_borrow_let("bv", "base")),
        ];
        for value in cases {
            let b = block(vec![eval(value)], tail_value(Expr::Unit));
            let mut out = BTreeMap::new();
            collect_borrow_sources(&b, &mut out);
            assert!(
                out.is_empty(),
                "recorded a borrow nested in an operand: {out:?}"
            );
        }
        // Abort tail carrying the If -- IS recorded (the original
        // `collect_borrow_sources_in_tail` recurses into Abort.code).
        let b = block(vec![], tail_abort(if_with_borrow_let("bv", "base")));
        let mut out = BTreeMap::new();
        collect_borrow_sources(&b, &mut out);
        assert!(
            out.contains_key(&VarId::from("bv")),
            "Abort-tail If should be walked"
        );
    }

    /// Control-flow positions the walk DOES descend into still record:
    /// a borrow-let directly in an If branch block, plus forward
    /// inheritance through a following WriteBack reading the accumulator
    /// in SOURCE ORDER.
    #[test]
    fn borrow_sources_records_in_blocks_and_inherits_in_order() {
        let inner = if_expr(
            var("c"),
            block(
                vec![let_stmt(&["bv"], borrow_vec_index(var("base"), lit0()))],
                tail_value(var("bv")),
            ),
            just(var("e")),
        );
        let b = block(vec![eval(inner)], tail_value(Expr::Unit));
        let mut out = BTreeMap::new();
        collect_borrow_sources(&b, &mut out);
        assert!(out.contains_key(&VarId::from("bv")));

        // Forward inheritance: `c` inherits `p`'s source via WriteBack.
        let b2 = block(
            vec![
                let_stmt(&["p"], borrow_vec_index(var("base"), lit0())),
                let_stmt(&["c"], write_back_ref("p", "inner")),
            ],
            tail_value(Expr::Unit),
        );
        let mut out2 = BTreeMap::new();
        collect_borrow_sources(&b2, &mut out2);
        assert!(out2.contains_key(&VarId::from("p")));
        assert!(out2.contains_key(&VarId::from("c")));
    }

    /// `collect_borrow_mut_origins`: a 2-slot borrow_mut-shaped let
    /// nested in a Call arg must NOT be recorded; and `Abort.code` is
    /// NOT walked (this family's `_in_tail` skipped Abort).
    #[test]
    fn borrow_mut_origins_operand_and_abort_skip() {
        let two_slot_if = if_expr(
            var("c"),
            block(
                vec![let_stmt_pat(
                    vec![Some("v"), Some("parent")],
                    call(0, vec![var("p"), var("key")]),
                )],
                tail_value(var("parent")),
            ),
            just(var("e")),
        );
        let b = block(
            vec![eval(call(0, vec![two_slot_if.clone()]))],
            tail_value(Expr::Unit),
        );
        let mut out = BTreeMap::new();
        collect_borrow_mut_origins(&b, &mut out);
        assert!(
            out.is_empty(),
            "recorded a 2-slot let nested in a Call arg: {out:?}"
        );

        // Abort-tail If -- this family skips Abort.code entirely.
        let b2 = block(vec![], tail_abort(two_slot_if));
        let mut out2 = BTreeMap::new();
        collect_borrow_mut_origins(&b2, &mut out2);
        assert!(
            out2.is_empty(),
            "Abort.code must NOT be walked by this family: {out2:?}"
        );
    }

    /// `gather_borrowloc_candidates`: a `let v := BorrowLoc(x)` nested
    /// in operand positions must NOT become a candidate. Drives the
    /// full `collect_redundant_borrowloc` and confirms an empty result.
    #[test]
    fn redundant_borrowloc_skips_operand_nested_borrowloc() {
        let prog = Program::default();
        let bl_if = if_expr(
            var("c"),
            block(
                vec![let_stmt(&["v"], borrow_loc("x"))],
                tail_value(read_ref(var("v"))),
            ),
            just(var("e")),
        );
        for value in [
            call(0, vec![bl_if.clone()]),
            binop(BinOp::Add, bl_if.clone(), var("z")),
            field(0, 0, bl_if.clone()),
        ] {
            let b = block(vec![eval(value)], tail_value(Expr::Unit));
            let mut cand = BTreeMap::new();
            gather_borrowloc_candidates_block(&b, &mut cand);
            assert!(
                cand.is_empty(),
                "candidate from operand-nested BorrowLoc: {cand:?}"
            );
            let mut out = BTreeMap::new();
            collect_redundant_borrowloc(&prog, &b, &mut out);
            assert!(out.is_empty());
        }
    }

    /// The program-aware collectors that key off `Expr::Call` shape
    /// must likewise not descend into operands. With no native match
    /// (empty Program) nothing is recorded regardless; this guards the
    /// walk shape itself (no panic, empty result) on operand-nested
    /// control flow.
    #[test]
    fn program_aware_collectors_walk_shape() {
        let prog = Program::default();
        let inner_if = if_expr(
            var("c"),
            block(
                vec![let_stmt(&["t"], call(1, vec![var("src"), var("k")]))],
                tail_value(var("t")),
            ),
            just(var("e")),
        );
        let b = block(vec![eval(call(0, vec![inner_if]))], tail_value(Expr::Unit));

        let mut m1 = BTreeMap::new();
        collect_map_borrow_sources(&prog, &b, &mut m1);
        assert!(m1.is_empty());

        let bs = BTreeMap::new();
        let bo = BTreeMap::new();
        let mut m2 = BTreeMap::new();
        collect_borrow_mut_derivatives(&prog, &b, &bs, &bo, &mut m2);
        assert!(m2.is_empty());

        let mut m3 = BTreeMap::new();
        collect_mutref_rebind_sources(&prog, &b, &mut m3);
        assert!(m3.is_empty());
    }
}
