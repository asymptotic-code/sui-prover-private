// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Convert `.aborts` companion bodies from `Bool` to `Option MoveAbort` and
//! inject Move's implicit-arithmetic-abort guards.
//!
//! Used by the test-mode pipeline (`Program::finalize_for_test`).
//!
//! Two orthogonal concerns are handled here:
//!
//! 1. **Bool → Option lowering**: walk the existing `.aborts` body and
//!    rewrite terminals: `Bool(true)` → `some(userAssert, 0)`,
//!    `Bool(false)` → `none`, `Abort { code }` → `some(userAssert, code)`.
//!    The signature's return type is updated to `Option MoveAbort`.
//!
//! 2. **Arithmetic-abort synthesis**: the upstream aborts-derivation pass
//!    only captures explicit `assert!` / `abort` sites — it does not see
//!    Move's implicit aborts on division by zero, mul/add overflow, sub
//!    underflow, shift width, or narrowing casts. For each `.aborts`
//!    companion we walk the matching impl function's body and synthesise
//!    a parallel `Option MoveAbort` expression that fires `arithmetic`
//!    aborts at every reachable site. The two are chained:
//!    `synth(impl_body) ||| transform(aborts_body)`.
//!
//! Inline checks (Div/Mod by zero, Shl/Shr width, narrowing Cast) are
//! expressed using existing IR (`BinOp::Eq` / `Ge` against bound-derived
//! constants). Mul / Add overflow and Sub underflow have no IR-level
//! encoding because BoundedNat ops wrap modulo bound, so we emit
//! `IRNode::ArithOverflowCheck` which the renderer lowers to the
//! corresponding `BoundedNat.*_overflows` / `sub_underflows` prelude
//! helper.

use crate::data::Program;
use crate::{AbortSource, BinOp, Const, FunctionID, IRNode, Type, UnOp, VariableRegistry};
use ethnum::U256;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub fn inject_arithmetic_aborts(program: &mut Program) {
    let mut aborts_ids: HashSet<FunctionID> = HashSet::new();
    let mut impl_index: HashMap<(usize, String), FunctionID> = HashMap::new();
    for (id, f) in program.functions.iter() {
        if f.name.contains(".aborts") {
            if !f.is_native {
                aborts_ids.insert(id);
            }
        } else {
            impl_index.insert((f.module_id, f.name.clone()), id);
        }
    }

    let mut impl_for: HashMap<FunctionID, FunctionID> = HashMap::new();
    for &aborts_id in &aborts_ids {
        let f = program.functions.get(&aborts_id);
        if let Some(stem) = f.name.strip_suffix(".aborts") {
            if let Some(&impl_id) = impl_index.get(&(f.module_id, stem.to_string())) {
                impl_for.insert(aborts_id, impl_id);
            }
        }
    }

    // Build the callee → callee.aborts map and the native-aborts set
    // *before* walking. `walk` synthesises a callee-abort check at every
    // `Call` site (closing the gap that `compose_callee_aborts_option`
    // can't reach: Calls buried in a Let's value-position
    // control-flow). Skip mapping into trivially-non-aborting *natives*
    // (their `.aborts` body is `Bool(false)` at this point in the
    // pipeline) — the wrap would degenerate to `if false then some else
    // none` after folding, but the unfolded form trips on the same
    // Bool/Prop param-type asymmetries that `build_aborts_map` in
    // `aborts_derivation` documents.
    //
    // The `Bool(false)` skip is native-ONLY. For a *generated* callee the
    // pre-inject Bool-shape `.aborts` body is not authoritative: this same
    // pass re-derives that callee's `.aborts` from its impl body via `walk`
    // in this run, and that walk-derived body may abort even when the stale
    // Bool body says `false`. `Math_u256.div_mod` is exactly this shape — its
    // pre-inject Bool `.aborts` is `Bool(false)` (the Bool derivation misses
    // the `num / denom` div-by-zero), but its walk-derived `.aborts` correctly
    // fires on `denom == 0`. Dropping such a callee from the map made a
    // `let (_, _) := div_mod n 0` caller (the `#[expected_failure]`
    // `test_div_mod_zero` driver) report `none`, so the expected abort was
    // never observed.
    let mut by_module_name: HashMap<(usize, &str), FunctionID> = HashMap::new();
    for (id, func) in program.functions.iter() {
        by_module_name.insert((func.module_id, &func.name), id);
    }
    let mut aborts_map_for_walk: HashMap<FunctionID, FunctionID> = HashMap::new();
    let mut native_aborts_for_walk: HashSet<FunctionID> = HashSet::new();
    for (id, func) in program.functions.iter() {
        if func.name.contains(".aborts") {
            continue;
        }
        let aborts_name = format!("{}.aborts", func.name);
        if let Some(&aborts_id) = by_module_name.get(&(func.module_id, aborts_name.as_str())) {
            let aborts_func = program.functions.get(&aborts_id);
            if aborts_func.is_native
                && matches!(&aborts_func.body, IRNode::Const(Const::Bool(false)))
            {
                continue;
            }
            aborts_map_for_walk.insert(id, aborts_id);
            if aborts_func.is_native {
                native_aborts_for_walk.insert(aborts_id);
            }
        }
    }

    let mut updates: Vec<(FunctionID, IRNode)> = Vec::new();
    for &fn_id in &aborts_ids {
        let func = program.functions.get(&fn_id);
        // Loop / mutual helpers (`<name>.while_N.aborts`, `.after.aborts`) sit
        // in mutual groups with their bodies; a faithful `.aborts` would be
        // recursive and the Lean kernel hits `deep recursion detected`
        // elaborating it. Model them as non-aborting — the enclosing
        // function's `.aborts` still covers per-iteration `Call`s, which
        // `walk` checks at the call site. (This mitigation previously lived
        // in `compose_callee_aborts_option`, which the option path no longer
        // runs.)
        let is_mutual_helper = func.mutual_group_id.is_some()
            && (func.name.contains(".while_") || func.name.contains(".after"));
        if is_mutual_helper {
            // EXCEPTION: a loop whose exit continuation can itself abort (an
            // `.after` helper containing an explicit `Abort` — the
            // `#[expected_failure]` build-then-abort shape) must keep a
            // faithful recursive `.aborts`: the exit abort happens with
            // exit-time loop-carried values only the loop itself can compute,
            // so the enclosing face cannot reconstruct it and gutting to
            // `none` erases the expected abort entirely (validator_tests
            // `*_too_long`). The gutted form stays for every other loop —
            // the deep-recursion mitigation the gutting exists for.
            // The exit abort can live in two places: a called `.after`
            // helper's body, or — when the continuation was inlined into the
            // loop's break/exit branches during structure building — directly
            // in the loop helper's own impl body as an inline `Abort`.
            // (`Abort`s in call-argument position are loop-invariant
            // hypothesis placeholders, not value aborts — skip those.)
            let exit_can_abort = impl_for
                .get(&fn_id)
                .map(|&impl_id| {
                    let impl_body = &program.functions.get(&impl_id).body;
                    has_inline_abort(impl_body)
                        || impl_body.calls().any(|callee| {
                            let cf = program.functions.get(&callee);
                            cf.name.contains(".after")
                                && cf.body.iter().any(|n| matches!(n, IRNode::Abort { .. }))
                        })
                })
                .unwrap_or(false);
            if !exit_can_abort {
                updates.push((fn_id, IRNode::OptionNone));
                continue;
            }
        }

        // Single-pass derivation: `walk` over the implementation body emits
        // every abort in one traversal — arithmetic overflow/div/cast,
        // explicit `assert!` aborts, and a callee-abort check at every
        // `Call`. This replaces the former
        // `chain_option(walk, lifted-existing-aborts-body)` union, which
        // derived callee aborts twice (here, and again via
        // `compose_callee_aborts_option`) and could disagree on a shared call
        // — leaving a spurious unconditional abort.
        let body = if let Some(&impl_id) = impl_for.get(&fn_id) {
            let impl_func = program.functions.get(&impl_id);
            let reg = impl_func.param_registry(program);
            // `walk` calls `get_type`, which panics on any free var not in the
            // registry. A handful of upstream translation bugs leave bodies
            // with stray references; fall back to lifting the pre-derived Bool
            // aborts body for those (validation already warns about them).
            let free = impl_func.body.free_vars();
            if free.iter().all(|v| reg.contains(v)) {
                // Skip synthesizing an abort check only for direct
                // self-recursion (`impl_id` calling itself) — that would make
                // the `.aborts` def recursive. Other in-group calls (notably
                // the loop helpers, whose `.aborts` are `Option.none` above)
                // are emitted as ordinary none-valued checks.
                //
                // EXCEPT for the exit-abort loop helpers that reached here via
                // the mutual-helper exception: their whole point is a faithful
                // RECURSIVE `.aborts` (guard → self-check on the next
                // iteration → exit-branch `after.aborts` with exit-time
                // loop-carried values). Without the self-check, iterations ≥ 2
                // — and hence the eventual exit abort — are never consulted.
                let mut self_skip: HashSet<FunctionID> = HashSet::new();
                if !is_mutual_helper {
                    self_skip.insert(impl_id);
                }
                let ctx = WalkCtx {
                    reg,
                    aborts_map: &aborts_map_for_walk,
                    aborts_ids: &aborts_ids,
                    native_aborts_ids: &native_aborts_for_walk,
                    same_group_impls: &self_skip,
                };
                let walked = walk(&impl_func.body, &ctx);
                // Recover explicit `assert!` aborts that the Body-mode prune
                // (`try_abort_prune_if` in control-flow reconstruction) drops from
                // the value body: lift them from the pre-derived (Aborts-mode)
                // `.aborts` body with `drop_callee = true`, keeping ONLY the
                // explicit-assert terminals (`walk` already synthesises the callee
                // `.aborts` checks; dropping them here avoids the double-emission
                // that motivated removing the old union). Without this, every Move
                // `assert!` is silently absent from the derived `.aborts`.
                //
                // SKIP for self-/mutual-recursive impls: their `.aborts` carry
                // `loop_hyp`/decreasing termination machinery whose client
                // `by`-macros are tuned to the exact body structure, and chaining
                // the assert residue changes the recursive call's context enough to
                // break them (`simp made no progress`). Such functions keep the
                // prior under-approximation; non-recursive `.aborts` — the common
                // case, including loop continuations — recover their asserts.
                let impl_recursive = impl_func.mutual_group_id.is_some()
                    || impl_func.body.calls().any(|c| c == impl_id);
                if impl_recursive {
                    walked
                } else {
                    let asserts = collapse_none(transform_existing(
                        program.functions.get(&fn_id).body.clone(),
                        &aborts_ids,
                        true,
                    ));
                    chain_option(walked, asserts)
                }
            } else {
                collapse_none(transform_existing(
                    program.functions.get(&fn_id).body.clone(),
                    &aborts_ids,
                    false,
                ))
            }
        } else {
            // No matching impl — lift the pre-derived aborts body.
            collapse_none(transform_existing(
                program.functions.get(&fn_id).body.clone(),
                &aborts_ids,
                false,
            ))
        };

        updates.push((fn_id, body));
    }

    for (fn_id, new_body) in updates {
        let func = program.functions.get_mut(fn_id);
        func.body = new_body;
        func.signature.return_type = Type::Option(Box::new(Type::MoveAbort));
    }
}

/// True when `node` contains an explicit `Abort` in value position.
/// `Abort`s appearing directly as call arguments are loop-invariant
/// hypothesis proof placeholders (see the comment in `walk`'s `Call`
/// arm), not value aborts, so they are excluded.
fn has_inline_abort(node: &IRNode) -> bool {
    match node {
        IRNode::Abort { .. } => true,
        IRNode::Call { args, .. } => args
            .iter()
            .filter(|a| !matches!(a, IRNode::Abort { .. }))
            .any(has_inline_abort),
        other => other.iter_children().any(has_inline_abort),
    }
}

fn arith_some() -> IRNode {
    IRNode::OptionSome(Box::new(IRNode::MoveAbortValue {
        source: AbortSource::Arithmetic,
        code: Box::new(IRNode::Const(Const::UInt {
            bits: 64,
            value: U256::from(0u64),
        })),
    }))
}

fn user_assert_some(code: IRNode) -> IRNode {
    IRNode::OptionSome(Box::new(IRNode::MoveAbortValue {
        source: AbortSource::UserAssert,
        code: Box::new(code),
    }))
}

fn zero_u64() -> IRNode {
    IRNode::Const(Const::UInt {
        bits: 64,
        value: U256::from(0u64),
    })
}

/// Combine two `Option MoveAbort` expressions: emit the first abort if any,
/// otherwise fall through to the second. Eliminates trivial `OptionNone`
/// halves so the chain stays compact.
fn chain_option(first: IRNode, second: IRNode) -> IRNode {
    if matches!(first, IRNode::OptionNone) {
        return second;
    }
    if matches!(second, IRNode::OptionNone) {
        return first;
    }
    let binding: Rc<str> = Rc::from("__abort");
    IRNode::MatchOption {
        scrutinee: Box::new(first),
        binding: binding.clone(),
        some_branch: Box::new(IRNode::OptionSome(Box::new(IRNode::Var(binding)))),
        none_branch: Box::new(second),
    }
}

fn fold_chain<I>(parts: I) -> IRNode
where
    I: IntoIterator<Item = IRNode>,
{
    parts
        .into_iter()
        .fold(IRNode::OptionNone, |acc, p| chain_option(acc, p))
}

/// Collapse subtrees that can never abort (every terminal is `OptionNone`) to
/// `OptionNone`. The assert residue lifted by `transform_existing` carries the
/// full value-body skeleton; for an assert-free function that is a dead
/// all-`none` if/let chain, and for a function with real asserts it wraps the
/// abort guards in dead structure. Folding the dead parts away leaves only the
/// real `OptionSome` (assert) terminals — so an assert-free residue becomes
/// `OptionNone` (then dropped by `chain_option`) and the `.aborts` spine stays
/// flat. Any `OptionSome` is preserved, so this never changes which inputs
/// abort.
fn collapse_none(node: IRNode) -> IRNode {
    match node {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let then_branch = collapse_none(*then_branch);
            let else_branch = collapse_none(*else_branch);
            if matches!(then_branch, IRNode::OptionNone)
                && matches!(else_branch, IRNode::OptionNone)
            {
                IRNode::OptionNone
            } else {
                IRNode::If {
                    cond,
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                }
            }
        }
        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let body = collapse_none(*body);
            if matches!(body, IRNode::OptionNone) {
                IRNode::OptionNone
            } else {
                IRNode::Let {
                    pattern,
                    value,
                    body: Box::new(body),
                }
            }
        }
        IRNode::Match { scrutinee, cases } => {
            let cases: Vec<_> = cases
                .into_iter()
                .map(|(idx, binds, body)| (idx, binds, collapse_none(body)))
                .collect();
            if cases
                .iter()
                .all(|(_, _, b)| matches!(b, IRNode::OptionNone))
            {
                IRNode::OptionNone
            } else {
                IRNode::Match { scrutinee, cases }
            }
        }
        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => {
            let none_branch = collapse_none(*none_branch);
            // Abort-chain `orElse(scrut, none) = scrut`: drop a trivial none tail
            // rather than leave `MoveAbort.orElse scrut none`.
            let is_abort_chain = binding.as_ref() == "__abort"
                && matches!(
                    some_branch.as_ref(),
                    IRNode::OptionSome(inner)
                        if matches!(inner.as_ref(), IRNode::Var(v) if v.as_ref() == "__abort")
                );
            if is_abort_chain && matches!(none_branch, IRNode::OptionNone) {
                return *scrutinee;
            }
            IRNode::MatchOption {
                scrutinee,
                binding,
                some_branch,
                none_branch: Box::new(none_branch),
            }
        }
        other => other,
    }
}

/// Walk the `.aborts` body that the upstream pipeline produced (Bool-shaped)
/// and lift it to `Option MoveAbort`. This mirrors the previous pass: it
/// rewrites Bool terminals, leaves `Call` to a sibling `.aborts` alone, and
/// recurses into branch / Let-body positions.
fn transform_existing(node: IRNode, aborts_ids: &HashSet<FunctionID>, drop_callee: bool) -> IRNode {
    match node {
        IRNode::Const(Const::Bool(true)) => user_assert_some(zero_u64()),
        IRNode::Const(Const::Bool(false)) => IRNode::OptionNone,

        IRNode::Abort { code } => {
            let code_expr = code.map(|c| *c).unwrap_or_else(zero_u64);
            user_assert_some(code_expr)
        }

        IRNode::Call { ref function, .. } if aborts_ids.contains(function) => {
            // Assert-residue mode (`drop_callee`): drop callee `.aborts` calls —
            // `walk` already synthesises a check at every `Call`, so keeping them
            // here would double-emit (the reason the old `chain_option` union was
            // removed). Keeping only the explicit-`assert!` terminals lets us
            // re-add JUST the asserts the Body-mode prune dropped.
            if drop_callee {
                IRNode::OptionNone
            } else {
                node
            }
        }

        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond,
            then_branch: Box::new(transform_existing(*then_branch, aborts_ids, drop_callee)),
            else_branch: Box::new(transform_existing(*else_branch, aborts_ids, drop_callee)),
        },

        IRNode::Match { scrutinee, cases } => IRNode::Match {
            scrutinee,
            cases: cases
                .into_iter()
                .map(|(idx, bindings, body)| {
                    (
                        idx,
                        bindings,
                        transform_existing(body, aborts_ids, drop_callee),
                    )
                })
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
            some_branch: Box::new(transform_existing(*some_branch, aborts_ids, drop_callee)),
            none_branch: Box::new(transform_existing(*none_branch, aborts_ids, drop_callee)),
        },

        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            // Spec-mode `.aborts` bodies use `let _ := <bool-disjunction>;
            // <bool-rest>` to chain assertion-side-effects: the Bool
            // value of `<bool-disjunction>` says "did this assertion
            // fire?", and the whole expression is implicit `value ||
            // body`. In option form we want to short-circuit on the
            // first abort, otherwise fall through:
            //
            //     match <option-form-value> with
            //       | some __abort => some __abort
            //       | none         => <option-form-body>
            //
            // We only do this for `_`-discard patterns whose value is a
            // syntactic control-flow expression (If/Match/MatchOption).
            // Other Let shapes — `let result := some_call()`, `let _ :=
            // Debug.print(...)`, etc. — bind real values whose type
            // isn't Bool; recursing into their value would mis-wrap a
            // non-Bool expression as `if <expr> then some else none`.
            let is_discard = pattern.iter().all(|p| p.as_ref() == "_");
            let value_is_control_flow = matches!(
                *value,
                IRNode::If { .. } | IRNode::Match { .. } | IRNode::MatchOption { .. }
            );
            if is_discard && value_is_control_flow {
                let new_value = transform_existing(*value, aborts_ids, drop_callee);
                let new_body = transform_existing(*body, aborts_ids, drop_callee);
                // Trivial-none short-circuit: if the value can never
                // abort, just emit the body directly.
                if matches!(new_value, IRNode::OptionNone) {
                    return new_body;
                }
                let binding: Rc<str> = Rc::from("__abort");
                IRNode::MatchOption {
                    scrutinee: Box::new(new_value),
                    binding: binding.clone(),
                    some_branch: Box::new(IRNode::OptionSome(Box::new(IRNode::Var(binding)))),
                    none_branch: Box::new(new_body),
                }
            } else {
                IRNode::Let {
                    pattern,
                    value,
                    body: Box::new(transform_existing(*body, aborts_ids, drop_callee)),
                }
            }
        }

        other => IRNode::If {
            cond: Box::new(other),
            then_branch: Box::new(user_assert_some(zero_u64())),
            else_branch: Box::new(IRNode::OptionNone),
        },
    }
}

/// Context carried through `walk`'s recursion. Bundles the
/// `VariableRegistry` (rebuilt at scope-extending nodes) with the
/// program-wide callee-abort maps that let `walk` synthesise abort
/// checks for direct `IRNode::Call` nodes — including ones buried
/// inside `let`'s value position, which `compose_callee_aborts_option`
/// can't reach because its `Let` arm only handles direct-Call values.
struct WalkCtx<'a> {
    reg: VariableRegistry<'a>,
    aborts_map: &'a HashMap<FunctionID, FunctionID>,
    aborts_ids: &'a HashSet<FunctionID>,
    native_aborts_ids: &'a HashSet<FunctionID>,
    /// Function IDs of the impl side of the function being processed AND
    /// every other function in the same mutual group. Calls to any of
    /// these are recursive (self or mutual). The synthesized abort
    /// check for such a call is redundant — `transform_existing` (the
    /// other half of `chain_option`) already includes the recursive
    /// `.aborts` call from the spec body, and emitting both at every
    /// level produces a 2-recursive-calls-per-iteration shape that
    /// explodes runtime evaluation to 2^N for an N-level loop.
    same_group_impls: &'a HashSet<FunctionID>,
}

impl<'a> WalkCtx<'a> {
    fn with_reg(&self, reg: VariableRegistry<'a>) -> WalkCtx<'a> {
        WalkCtx {
            reg,
            aborts_map: self.aborts_map,
            aborts_ids: self.aborts_ids,
            native_aborts_ids: self.native_aborts_ids,
            same_group_impls: self.same_group_impls,
        }
    }
}

/// Synthesise a callee-abort check for a single `Call`. Returns
/// `OptionNone` if the callee has no `.aborts` companion, or a
/// `MatchOption(callee.aborts(args))` shim that fires `Some(__abort)`
/// when the callee would abort. For native callees whose `.aborts`
/// returns `Bool` (per the hand-written prelude), wrap the predicate
/// with an `if` lift to option-shape on the fly.
fn synth_callee_check(
    function: FunctionID,
    args: &[IRNode],
    type_args: &[Type],
    ctx: &WalkCtx,
) -> IRNode {
    if ctx.aborts_ids.contains(&function) {
        // Calling an `.aborts` function itself — don't double-wrap; its
        // result is already Option-shaped and gets composed at the
        // calling Let's chain_option site.
        return IRNode::OptionNone;
    }
    if ctx.same_group_impls.contains(&function) {
        // Recursive call (self or mutual) — the spec-side aborts body
        // (the `transformed_existing` half of `chain_option`) already
        // contains the `.aborts` recursive call covering this. Emitting
        // a synthesized abort check here too would double the recursive
        // call per iteration, producing 2^N runtime cost for N-level
        // loops (notably `dummy_tx_hash_with_hint.while_0.aborts` with
        // its 32-iteration push_back loop).
        return IRNode::OptionNone;
    }
    let Some(&aborts_id) = ctx.aborts_map.get(&function) else {
        return IRNode::OptionNone;
    };
    let aborts_call = IRNode::Call {
        function: aborts_id,
        type_args: type_args.to_vec(),
        args: args.to_vec(),
    };
    // Every `.aborts` companion is `Option MoveAbort` — generated ones via this
    // pass, hand-written natives directly in their `lemmas/` source files. Match
    // on the result uniformly.
    let binding: Rc<str> = Rc::from("__abort");
    IRNode::MatchOption {
        scrutinee: Box::new(aborts_call),
        binding: binding.clone(),
        some_branch: Box::new(IRNode::OptionSome(Box::new(IRNode::Var(binding)))),
        none_branch: Box::new(IRNode::OptionNone),
    }
}

/// Synthesise an `Option MoveAbort` expression that captures every
/// arithmetic abort reachable when evaluating `node` in evaluation order.
/// Variables introduced in `node`'s `Let`s are bound for the synth check
/// inside the same `Let`'s body, then go out of scope — so the synth
/// expression composes safely with anything chained after it.
fn walk(node: &IRNode, ctx: &WalkCtx) -> IRNode {
    match node {
        IRNode::Var(_) | IRNode::Const(_) => IRNode::OptionNone,

        IRNode::BinOp { op, lhs, rhs } => {
            let l = walk(lhs, ctx);
            let r = walk(rhs, ctx);
            let self_check = check_binop(*op, lhs, rhs, &ctx.reg);
            chain_option(l, chain_option(r, self_check))
        }

        IRNode::UnOp { op, operand } => {
            let inner = walk(operand, ctx);
            let self_check = check_unop(op, operand, &ctx.reg);
            chain_option(inner, self_check)
        }

        IRNode::BitOp(_) => IRNode::OptionNone,

        IRNode::Call {
            function,
            args,
            type_args,
        } => {
            // Walk args first (their evaluation may abort), then check the
            // callee's `.aborts` companion. Without the callee check here,
            // calls buried inside `let`'s value position never get
            // wrapped — `compose_callee_aborts_option` only handles
            // direct-Let-value Calls, so e.g. a Call inside an
            // `if cond then ... else (let __pair := callee(...))` shape
            // is missed and its potential abort never propagates to the
            // `.aborts` companion's return.
            // A bare `Abort` in argument position is not a value computation —
            // it is the loop-invariant hypothesis *proof* placeholder threaded
            // onto `while_N` / `while_N.aborts` calls (later replaced by a
            // `(by <entry>)` term in `thread_loop_inv_entry`, which runs after
            // this pass). Walking it would mis-synthesize an unconditional
            // `some(userAssert)`. Skip such args; real value args still walk.
            let args_check = fold_chain(
                args.iter()
                    .filter(|a| !matches!(a, IRNode::Abort { .. }))
                    .map(|a| walk(a, ctx)),
            );
            let callee_check = synth_callee_check(*function, args, type_args, ctx);
            chain_option(args_check, callee_check)
        }

        IRNode::Pack { fields, .. } => fold_chain(fields.iter().map(|f| walk(f, ctx))),

        IRNode::Field { base, .. } => walk(base, ctx),
        IRNode::Unpack { value, .. } => walk(value, ctx),

        IRNode::Tuple(elems) => fold_chain(elems.iter().map(|e| walk(e, ctx))),

        IRNode::Let {
            pattern,
            value,
            body,
        } => {
            let v_check = walk(value, ctx);
            let val_type = value.get_type(&ctx.reg);
            let mut inner = ctx.reg.clone();
            inner.register_pattern(pattern, val_type);
            let body_check = IRNode::Let {
                pattern: pattern.clone(),
                value: value.clone(),
                body: Box::new(walk(body, &ctx.with_reg(inner))),
            };
            chain_option(v_check, body_check)
        }

        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let c_check = walk(cond, ctx);
            let branched = IRNode::If {
                cond: cond.clone(),
                then_branch: Box::new(walk(then_branch, ctx)),
                else_branch: Box::new(walk(else_branch, ctx)),
            };
            chain_option(c_check, branched)
        }

        IRNode::Match { scrutinee, cases } => {
            let s_check = walk(scrutinee, ctx);
            let scrutinee_ty = match scrutinee.get_type(&ctx.reg) {
                Type::Reference(inner) => *inner,
                Type::MutableReference(val, _) => *val,
                other => other,
            };
            let new_cases = cases
                .iter()
                .map(|(tag, bindings, body)| {
                    let mut inner = ctx.reg.clone();
                    if let Type::Struct {
                        struct_id,
                        type_args,
                    } = &scrutinee_ty
                    {
                        let s = ctx.reg.program().structs.get(*struct_id);
                        if let Some(variants) = s.variants.as_ref() {
                            if let Some(variant) = variants.iter().find(|v| v.tag == *tag) {
                                for (name, field) in bindings.iter().zip(variant.fields.iter()) {
                                    let ty =
                                        field.field_type.clone().substitute_type_params(type_args);
                                    inner.register(name.clone(), ty);
                                }
                            }
                        }
                    }
                    (*tag, bindings.clone(), walk(body, &ctx.with_reg(inner)))
                })
                .collect();
            let m = IRNode::Match {
                scrutinee: scrutinee.clone(),
                cases: new_cases,
            };
            chain_option(s_check, m)
        }

        IRNode::MatchOption {
            scrutinee,
            binding,
            some_branch,
            none_branch,
        } => {
            let s_check = walk(scrutinee, ctx);
            let mut inner = ctx.reg.clone();
            // We don't know the option's element type without re-deriving the
            // scrutinee type, but registering with a placeholder keeps the
            // `Var(binding)` lookups happy if any walk step looks it up.
            inner.register(binding.clone(), Type::TypeParameter(0));
            let mo = IRNode::MatchOption {
                scrutinee: scrutinee.clone(),
                binding: binding.clone(),
                some_branch: Box::new(walk(some_branch, &ctx.with_reg(inner))),
                none_branch: Box::new(walk(none_branch, ctx)),
            };
            chain_option(s_check, mo)
        }

        IRNode::UpdateField { base, value, .. } => chain_option(walk(base, ctx), walk(value, ctx)),
        IRNode::UpdateVec { base, index, value } => chain_option(
            walk(base, ctx),
            chain_option(walk(index, ctx), walk(value, ctx)),
        ),

        IRNode::ReadRef(inner) => walk(inner, ctx),
        IRNode::WriteRef { reference, value } => {
            chain_option(walk(reference, ctx), walk(value, ctx))
        }
        IRNode::MutableBorrow {
            val_expr,
            reconstruct_param: _,
            reconstruct_expr: _,
            state_type: _,
        } => {
            // Only the val_expr executes at borrow time. The reconstruct
            // lambda body fires later — when `Mutable.apply` /
            // `Mutable.set` invokes it — so its aborts belong at the
            // apply site, not here. Walking the lambda body would also
            // leak free references to `reconstruct_param` (commonly
            // `__v`) into the surrounding scope: the synth result is
            // chained via `chain_option` into a sibling expression, and
            // there is no lambda binder around it. This is the same
            // reasoning that already treats `WriteBack` / `MutableCompose`
            // as no-abort below — they execute the same lambda elsewhere.
            walk(val_expr, ctx)
        }

        IRNode::Quantifier { .. } => IRNode::OptionNone,

        IRNode::ToProp(inner) | IRNode::ToBool(inner) => walk(inner, ctx),

        IRNode::OptionSome(inner) => walk(inner, ctx),
        IRNode::OptionNone
        | IRNode::Inhabited
        | IRNode::WriteBack { .. }
        | IRNode::MutableCompose { .. } => IRNode::OptionNone,

        // Explicit aborts in the impl body show up as `IRNode::Abort` in
        // Test-mode IR. The Spec-mode `.aborts` body collapses these to
        // `Bool(true)` (which `transform_existing` can only lift to
        // `some(userAssert, 0)` — the code was lost during the
        // Bool-style spec build). The impl body still has the original
        // `code` expression, so we synthesize the abort here with the
        // preserved code instead. This is what makes
        // `assert!(cond, CODE)` round-trip in test mode: tests that
        // expect a specific abort code (e.g. `#[expected_failure(abort_code = E...)]`)
        // see CODE rather than 0 when the abort fires inline.
        IRNode::Abort { code } => {
            let code_expr = code.clone().map(|c| *c).unwrap_or_else(zero_u64);
            user_assert_some(code_expr)
        }

        IRNode::MoveAbortValue { .. } | IRNode::ArithOverflowCheck { .. } => IRNode::OptionNone,
    }
}

fn check_binop(op: BinOp, lhs: &IRNode, rhs: &IRNode, reg: &VariableRegistry) -> IRNode {
    match op {
        BinOp::Add | BinOp::Sub | BinOp::Mul => {
            // BoundedNat helpers handle these.
            let cond = IRNode::ArithOverflowCheck {
                op,
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs.clone()),
            };
            IRNode::If {
                cond: Box::new(cond),
                then_branch: Box::new(arith_some()),
                else_branch: Box::new(IRNode::OptionNone),
            }
        }
        BinOp::Div | BinOp::Mod => {
            let bits = match lhs.get_type(reg) {
                Type::UInt(b) => b as usize,
                _ => return IRNode::OptionNone,
            };
            let zero = IRNode::Const(Const::UInt {
                bits,
                value: U256::from(0u64),
            });
            let cond = IRNode::BinOp {
                op: BinOp::Eq,
                lhs: Box::new(rhs.clone()),
                rhs: Box::new(zero),
            };
            IRNode::If {
                cond: Box::new(cond),
                then_branch: Box::new(arith_some()),
                else_branch: Box::new(IRNode::OptionNone),
            }
        }
        BinOp::Shl | BinOp::Shr => {
            let lhs_bits = match lhs.get_type(reg) {
                Type::UInt(b) => b,
                _ => return IRNode::OptionNone,
            };
            // u256 shift width never aborts: rhs is at most u8 (max 255 < 256).
            if lhs_bits >= 256 {
                return IRNode::OptionNone;
            }
            let rhs_bits = match rhs.get_type(reg) {
                Type::UInt(b) => b as usize,
                _ => return IRNode::OptionNone,
            };
            let bound = IRNode::Const(Const::UInt {
                bits: rhs_bits,
                value: U256::from(lhs_bits as u64),
            });
            let cond = IRNode::BinOp {
                op: BinOp::Ge,
                lhs: Box::new(rhs.clone()),
                rhs: Box::new(bound),
            };
            IRNode::If {
                cond: Box::new(cond),
                then_branch: Box::new(arith_some()),
                else_branch: Box::new(IRNode::OptionNone),
            }
        }
        _ => IRNode::OptionNone,
    }
}

fn check_unop(op: &UnOp, operand: &IRNode, reg: &VariableRegistry) -> IRNode {
    match op {
        UnOp::Cast(target_bits) => {
            let source_bits = match operand.get_type(reg) {
                Type::UInt(b) => b,
                _ => return IRNode::OptionNone,
            };
            // Widening casts never abort.
            if *target_bits >= source_bits {
                return IRNode::OptionNone;
            }
            // operand >= 2^target_bits — narrowing cast aborts when value
            // doesn't fit.
            let two_pow = U256::ONE << (*target_bits as u32);
            let bound = IRNode::Const(Const::UInt {
                bits: source_bits as usize,
                value: two_pow,
            });
            let cond = IRNode::BinOp {
                op: BinOp::Ge,
                lhs: Box::new(operand.clone()),
                rhs: Box::new(bound),
            };
            IRNode::If {
                cond: Box::new(cond),
                then_branch: Box::new(arith_some()),
                else_branch: Box::new(IRNode::OptionNone),
            }
        }
        _ => IRNode::OptionNone,
    }
}
