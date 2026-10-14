//! Stage 7 -- defunctionalize deep abort loops so `partial_fixpoint`'s
//! monotonicity proof stays shallow.
//!
//! A `.aborts.while_N` loop whose body is a deep/heavy abort-propagation
//! cascade makes Lean's `partial_fixpoint` monotonicity proof term overflow the
//! KERNEL recursion limit ("(kernel) deep recursion detected") -- even though
//! the body type-checks fine as an opaque `partial def`, and even when split
//! into a mutual `partial_fixpoint` block (mutual proves the COMBINED system,
//! so the total proof is unchanged).
//!
//! Fix: defunctionalize. Emit a TOTAL step function `<loop>_step` returning a
//! per-loop sum `<Loop>Step | cont <next params> | done <AbortResult>`, and
//! shrink the loop to a tiny recursive matcher:
//!
//!   def loop_step p... : <Loop>Step := <heavy body, recursive call -> cont,
//!                                        every other tail -> done(<that tail>)>
//!   def loop p... : AbortResult :=
//!     match loop_step p... with | cont q... => loop q... | done r => r
//!   partial_fixpoint
//!
//! The heavy computation now lives in the TOTAL `loop_step` (no fixpoint, so no
//! monotonicity proof traverses it); `loop`'s proof is one recursive call in
//! one match arm. Validated by hand on current-lending
//! `update_pool_reward_manager.aborts.while_0` (286s + kernel overflow ->
//! 0.66s clean, `partial_fixpoint` preserved).

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::ir::analysis::type_of::{bind_pattern, substitute_type_params, type_of};
use crate::ir::expr::{Block, BlockTail, Expr, MatchArm};
use crate::ir::function::{Function, FunctionKind, Signature};
use crate::ir::program::{Field, Struct, Variant};
use crate::ir::ty::Type;
use crate::ir::visit::{walk_expr_default, Visitor};
use crate::ir::{FunId, Program, StructId, VarId};

const CONT_TAG: usize = 0;
const DONE_TAG: usize = 1;

/// True iff `s` is a loop-step inductive synthesised by this pass: a 2-variant
/// enum `cont | done` whose name ends in `_Step`. The renderer uses this to
/// route these types into the impl (Funcs) file rather than the restricted
/// `_Types` / `_Types_Skeleton` files -- their `cont` variant carries impl-only
/// types (the `World` `local notation`, `Generated.*`-imported project structs)
/// that the Types files do not bring into scope.
pub fn is_loop_step_struct(s: &Struct) -> bool {
    s.name.ends_with("_Step")
        && s.variants.as_ref().map_or(false, |vs| {
            vs.len() == 2 && vs[0].name == "cont" && vs[1].name == "done"
        })
}

pub fn run(program: &mut Program) {
    // Candidate abort-loop bodies. EVERY abort loop is defunctionalized when it
    // is safe (see the gates below). Lean elaborates a `partial_fixpoint` by
    // building a monotonicity proof over the WHOLE loop body; for a heavy body
    // that proof both overflows the kernel recursion limit (current-lending,
    // bluefin, momentum, cetus-dlmm) AND blows up memory -- cetus-stl's
    // `test_with_seed_0.aborts.while_0` needs ~21.5 GB to type-check vs ~4 GB
    // defunctionalized. Defunctionalization moves the body into a TOTAL step fn
    // (no monotonicity proof), so apply it to all abort loops, not just the
    // deep/clustered ones -- gated only by what would otherwise break it.
    let candidates: Vec<FunId> = program
        .functions
        .iter()
        .filter(|(_, f)| {
            matches!(f.kind, FunctionKind::LoopBody { .. })
                && f.name.contains(".aborts.")
                // Skip lemma/framework modules (Sui, MoveStdlib, Prover): they
                // render `World` as a file-scoped POLYMORPHIC notation
                // (`__WorldEvent` / `__WorldObject` / ...), so a `Step` inductive
                // carrying `World` captures those as implicit parameters that Lean
                // cannot synthesize at the use site (observed as `Sui::Display`'s
                // `don't know how to synthesize implicit argument __World*`). User
                // modules use the concrete `Generated.World` and are unaffected.
                && !program.modules.get(&f.module).map_or(false, |m| {
                    crate::render::escape::is_lemma_package(&m.package_name)
                })
        })
        .map(|(fid, _)| *fid)
        .collect();
    // Precompute the whole-program call graph (both directions) once.
    let callee_map: HashMap<FunId, HashSet<FunId>> = program
        .functions
        .iter()
        .map(|(fid, f)| (*fid, callees_of(&f.body)))
        .collect();
    let mut caller_map: HashMap<FunId, HashSet<FunId>> = HashMap::new();
    for (caller, callees) in &callee_map {
        for c in callees {
            caller_map.entry(*c).or_default().insert(*caller);
        }
    }
    let loop_bodies: HashSet<FunId> = program
        .functions
        .iter()
        .filter(|(_, f)| matches!(f.kind, FunctionKind::LoopBody { .. }))
        .map(|(fid, _)| *fid)
        .collect();
    let targets: Vec<FunId> = candidates
        .into_iter()
        .filter(|fid| {
            // A loop whose recursive SCC contains ANOTHER loop body is nested /
            // mutually recursive (e.g. cetus-dlmm `settle_rewards` and ika
            // `verify_certificate`, where `while_0`'s cont tail-calls `while_1`).
            // This pass flattens one loop at a time and does not pull the second
            // loop into the cont cluster, so defunctionalizing a member leaves
            // its `loop_step` recursive. Such inter-loop SCCs already compile as
            // a `mutual partial_fixpoint`; leave them alone.
            if loop_in_multiloop_scc(*fid, &callee_map, &caller_map, &loop_bodies) {
                return false;
            }
            // Fully flattenable only: cluster-free (a plain self-recursive body)
            // or a cluster whose entire cycle is soundly retypeable. A cont
            // escaping the cluster (safe != full) would leave `loop_step`
            // recursive.
            let (full, safe) = loop_cont_clusters(program, *fid);
            safe == full
        })
        .collect();
    for fid in targets {
        defunctionalize(program, fid);
    }
}

fn defunctionalize(program: &mut Program, fid: FunId) {
    let (loop_name, module, type_params, params, ret_type, effects, explicit_pure, qn) = {
        let f = &program.functions[&fid];
        (
            f.name.clone(),
            f.module,
            f.signature.type_params.clone(),
            f.signature.params.clone(),
            f.signature.return_type.clone(),
            f.effects.clone(),
            f.explicit_pure,
            // MODULE name, not package name. Every other `Struct` in the
            // IR is keyed `<module>::<Name>` (`module_lift::lift_struct`);
            // using the package here made the step enums of two loops
            // that share a function name in different modules of one
            // package collide on `qualified_name` -- e.g. sui-system's
            // `coin_vec_sum.aborts.while_0`, replicated by the
            // cross-layer delegate copies. The name is a datatype's
            // identity now (`render::struct_idx`), so the collision is
            // no longer merely cosmetic.
            program.modules[&f.module].name.clone(),
        )
    };
    let type_args: Vec<Type> = (0..type_params.len() as u16).map(Type::TypeParam).collect();

    // 0. The loop's recursive continuation cluster (empty for a plain
    // self-recursive loop). Computed BEFORE any new function is inserted so the
    // single-use call counts reflect the original program.
    let cluster = loop_cont_cluster(program, fid);

    // 1. Per-loop step inductive: `<Loop>Step | cont(params) | done(ret)`.
    let step_id = program.next_struct_id();
    let step_name = format!("{}_Step", sanitize(&loop_name));
    let step_struct = Struct {
        module_id: module,
        name: step_name.clone(),
        qualified_name: format!("{}::{}", qn, step_name),
        type_params: type_params.clone(),
        fields: Vec::new(),
        variants: Some(vec![
            Variant {
                name: "cont".into(),
                tag: CONT_TAG,
                fields: params
                    .iter()
                    .map(|p| Field {
                        name: p.name.clone(),
                        // A `Mutation` (MutableRef) param is carried as its FULL
                        // `Mutation` type, preserving the reference's `loc` + `path`
                        // (borrow identity) across the loop. This is required for any
                        // in-loop conditional writeback: the `isParent` / `isParentHyper`
                        // / `isSameMutation` predicates that re-sync aliased `&mut`s
                        // mid-loop (e.g. a df-backed group ref written back into its
                        // parent container before a sibling reads it) compare `loc` +
                        // `path`, which a value-stripped `cont` would erase -- the
                        // renderer would re-wrap each value with `Mutation.ofLocal`
                        // (fresh `localRoot`, empty `path`), desyncing every alias and
                        // silently dropping the mutation (cetus-dlmm
                        // `remove_liquidity` / `close_position_with_fee` /
                        // `remove_liquidity_by_percent_internal`). The non-defunctionalized
                        // loop (`<fn>.while_N`) already threads the full `Mutation`
                        // through its recursive call; carrying it here keeps the
                        // `.aborts` companion consistent. Step inductives always render
                        // into the impl (Funcs) file (see `is_loop_step_struct` routing),
                        // where the `Mutation` prelude is in scope, so no `_Types`
                        // scoping concern arises.
                        field_type: p.ty.clone(),
                    })
                    .collect(),
            },
            Variant {
                name: "done".into(),
                tag: DONE_TAG,
                fields: vec![Field {
                    name: "r".into(),
                    field_type: ret_type.clone(),
                }],
            },
        ]),
        is_native: false,
    };
    let step_ty = Type::Struct {
        struct_id: step_id,
        type_args: type_args.clone(),
    };

    // 2. Total `loop_step`: the heavy body with tails retargeted to the sum.
    let step_fid = program.next_function_id();
    let mut step_body = program.functions[&fid].body.clone();
    let initial_scope: BTreeMap<VarId, Type> = params
        .iter()
        .map(|param| (param.var.clone(), param.ty.clone()))
        .collect();
    if !transform_block_tails(
        &mut step_body,
        fid,
        step_id,
        &type_args,
        &cluster,
        &ret_type,
        &initial_scope,
        program,
    ) {
        return;
    }
    // 2b. Retarget and retype the cluster continuations the same way: each now
    // returns the step sum (its `loop` calls become `cont`, sibling-cont calls
    // pass through, every other exit becomes `done`). They stay separate TOTAL
    // defs -- only the matcher (below) carries `partial_fixpoint`, so the kernel
    // monotonicity proof never traverses the heavy cluster bodies.
    let mut transformed_cont_bodies = Vec::with_capacity(cluster.len());
    for &cont_fid in &cluster {
        let mut body = program.functions[&cont_fid].body.clone();
        let cont = &program.functions[&cont_fid];
        let scope: BTreeMap<VarId, Type> = cont
            .signature
            .params
            .iter()
            .map(|param| (param.var.clone(), param.ty.clone()))
            .collect();
        if !transform_block_tails(
            &mut body, fid, step_id, &type_args, &cluster, &ret_type, &scope, program,
        ) {
            // This is an atomic transformation. No generated function or
            // signature has been installed yet, so an unsupported recursive
            // value context leaves the original loop cluster untouched.
            return;
        }
        transformed_cont_bodies.push((cont_fid, body));
    }

    program.functions.insert(
        step_fid,
        Function {
            module,
            name: format!("{}_step", loop_name),
            signature: Signature {
                type_params: type_params.clone(),
                params: params.clone(),
                return_type: step_ty.clone(),
            },
            body: step_body,
            kind: FunctionKind::Synthetic,
            effects: effects.clone(),
            explicit_pure,
        },
    );
    program.structs.insert(step_id, step_struct);

    for (cont_fid, body) in transformed_cont_bodies {
        let f = program.functions.get_mut(&cont_fid).unwrap();
        f.body = body;
        f.signature.return_type = step_ty.clone();
    }

    // 3. Rewrite the loop into the tiny recursive matcher.
    let conts: Vec<VarId> = (0..params.len())
        .map(|i| VarId::from(format!("__ds_{i}").as_str()))
        .collect();
    let cont_arm = MatchArm {
        variant: CONT_TAG,
        bindings: conts.clone(),
        body: Box::new(Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::Call {
                fun: fid,
                type_args: type_args.clone(),
                args: conts.iter().map(|v| Expr::Var(v.clone())).collect(),
            }),
        }),
    };
    let r: VarId = VarId::from("__dr");
    let done_arm = MatchArm {
        variant: DONE_TAG,
        bindings: vec![r.clone()],
        body: Box::new(Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::Var(r)),
        }),
    };
    let step_call = Expr::Call {
        fun: step_fid,
        type_args: type_args.clone(),
        args: params.iter().map(|p| Expr::Var(p.var.clone())).collect(),
    };
    program.functions.get_mut(&fid).unwrap().body = Block {
        stmts: Vec::new(),
        tail: BlockTail::Value(Expr::Match {
            struct_id: step_id,
            selector: Box::new(step_call),
            cases: vec![cont_arm, done_arm],
        }),
    };
}

/// Retarget every TAIL (terminal) position of `b` to the step sum: a recursive
/// `loop` call becomes `cont(args)`; any other tail becomes `done(<tail>)`.
/// `If`/`Match` tails are recursed into (their arms hold the real tails).
#[allow(clippy::too_many_arguments)]
fn transform_block_tails(
    b: &mut Block,
    loop_fid: FunId,
    step_id: StructId,
    type_args: &[Type],
    cluster: &HashSet<FunId>,
    ret_type: &Type,
    scope: &BTreeMap<VarId, Type>,
    program: &Program,
) -> bool {
    let mut local_scope = scope.clone();
    for statement in &b.stmts {
        let value = match statement {
            crate::ir::Stmt::Let { value, .. } | crate::ir::Stmt::Eval(value) => value,
        };
        // A recursive call is safe only as the complete terminal value. Any
        // call hidden in a statement RHS would remain recursive in the total
        // step function, defeating defunctionalisation. Reject the whole
        // candidate before committing any generated artefact.
        if expr_calls_recursive_cluster(value, loop_fid, cluster) {
            return false;
        }
        if let crate::ir::Stmt::Let { pattern, value } = statement {
            if let Ok(value_type) = type_of(value, &local_scope, program) {
                let _ = bind_pattern(pattern, &value_type, &mut local_scope);
            }
        }
    }

    match &mut b.tail {
        BlockTail::Value(e) => transform_tail_expr(
            e,
            loop_fid,
            step_id,
            type_args,
            cluster,
            ret_type,
            &local_scope,
            program,
        ),
        // Value-carrying terminals (a non-recursive abort-propagation exit, or
        // the rare surviving structured jump): retarget the carried value the
        // same way and collapse to a plain `Value` tail so the matcher/renderer
        // see a Step-typed block. Without this the carried `AbortResult` reaches
        // `loop_step` unwrapped -> "expected ..._Step, got AbortResult".
        BlockTail::Return(v)
        | BlockTail::Break { value: v, .. }
        | BlockTail::Continue { value: v, .. }
        | BlockTail::ReturnFromBlock { value: v, .. } => {
            let mut e = std::mem::replace(v.as_mut(), Expr::Unit);
            if !transform_tail_expr(
                &mut e,
                loop_fid,
                step_id,
                type_args,
                cluster,
                ret_type,
                &local_scope,
                program,
            ) {
                return false;
            }
            b.tail = BlockTail::Value(e);
            true
        }
        BlockTail::Abort { .. } => {
            // Not observed in deep abort loops: the `.aborts` companion lowers
            // raw aborts to `AbortResult` values (a `Value` tail) before this
            // pass runs (validated: 0 abort tails across the client sweep). If
            // one reaches here, decline the entire atomic candidate instead of
            // constructing a partial Step conversion.
            false
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn transform_tail_expr(
    e: &mut Expr,
    loop_fid: FunId,
    step_id: StructId,
    type_args: &[Type],
    cluster: &HashSet<FunId>,
    ret_type: &Type,
    scope: &BTreeMap<VarId, Type>,
    program: &Program,
) -> bool {
    if matches!(e, Expr::Match { .. }) {
        let mut candidate = e.clone();
        if let Some(transformed) = try_transform_return_carrier(
            &mut candidate,
            loop_fid,
            step_id,
            type_args,
            cluster,
            ret_type,
            scope,
            program,
        ) {
            if transformed {
                *e = candidate;
            }
            return transformed;
        }
    }
    match e {
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            if expr_calls_recursive_cluster(cond, loop_fid, cluster) {
                return false;
            }
            transform_block_tails(
                then_branch,
                loop_fid,
                step_id,
                type_args,
                cluster,
                ret_type,
                scope,
                program,
            ) && transform_block_tails(
                else_branch,
                loop_fid,
                step_id,
                type_args,
                cluster,
                ret_type,
                scope,
                program,
            )
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            if expr_calls_recursive_cluster(selector, loop_fid, cluster) {
                return false;
            }
            let Some(arm_scopes) = match_arm_scopes(*struct_id, selector, cases, scope, program)
            else {
                return false;
            };
            cases.iter_mut().zip(arm_scopes).all(|(arm, arm_scope)| {
                transform_block_tails(
                    &mut arm.body,
                    loop_fid,
                    step_id,
                    type_args,
                    cluster,
                    ret_type,
                    &arm_scope,
                    program,
                )
            })
        }
        // A tail call to a cluster continuation already yields the step sum
        // (those conts are retyped to return Step) -- pass it through unwrapped.
        Expr::Call { fun, args, .. } if cluster.contains(&*fun) => !args
            .iter()
            .any(|arg| expr_calls_recursive_cluster(arg, loop_fid, cluster)),
        _ => wrap_terminal_atomically(
            e, loop_fid, step_id, type_args, cluster, ret_type, scope, program,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn wrap_terminal_atomically(
    expression: &mut Expr,
    loop_fid: FunId,
    step_id: StructId,
    type_args: &[Type],
    cluster: &HashSet<FunId>,
    ret_type: &Type,
    scope: &BTreeMap<VarId, Type>,
    program: &Program,
) -> bool {
    let owned = std::mem::replace(expression, Expr::Unit);
    *expression = match owned {
        Expr::Call {
            fun,
            type_args: call_type_args,
            args,
        } if fun == loop_fid
            && !args
                .iter()
                .any(|arg| expr_calls_recursive_cluster(arg, loop_fid, cluster)) =>
        {
            let _ = call_type_args;
            Expr::Pack {
                struct_id: step_id,
                type_args: type_args.to_vec(),
                variant: Some(CONT_TAG),
                fields: args,
            }
        }
        other
            if !expr_calls_recursive_cluster(&other, loop_fid, cluster)
                && type_of(&other, scope, program).ok().as_ref() == Some(ret_type) =>
        {
            Expr::Pack {
                struct_id: step_id,
                type_args: type_args.to_vec(),
                variant: Some(DONE_TAG),
                fields: vec![other],
            }
        }
        other => {
            *expression = other;
            return false;
        }
    };
    true
}

#[allow(clippy::too_many_arguments)]
fn try_transform_return_carrier(
    expression: &mut Expr,
    loop_fid: FunId,
    step_id: StructId,
    step_type_args: &[Type],
    cluster: &HashSet<FunId>,
    ret_type: &Type,
    scope: &BTreeMap<VarId, Type>,
    program: &Program,
) -> Option<bool> {
    let Expr::Match {
        struct_id,
        selector,
        cases,
    } = expression
    else {
        return None;
    };
    let option_id =
        program.struct_id_by_qualified_name(super::option_aborts::OPTION_QUALIFIED_NAME)?;
    if *struct_id != option_id || cases.len() != 2 {
        return None;
    }
    let none_index = cases
        .iter()
        .position(|arm| arm.variant == super::option_aborts::OPTION_NONE_TAG)?;
    let some_index = cases
        .iter()
        .position(|arm| arm.variant == super::option_aborts::OPTION_SOME_TAG)?;
    if !cases[none_index].bindings.is_empty() || cases[some_index].bindings.len() != 1 {
        return None;
    }
    let payload = cases[some_index].bindings[0].clone();
    if !cases[some_index].body.stmts.is_empty()
        || !matches!(
            &cases[some_index].body.tail,
            BlockTail::Value(Expr::Var(value)) if *value == payload
        )
    {
        return None;
    }
    let Ok(Type::Struct {
        struct_id: selector_struct,
        type_args: selector_type_args,
    }) = type_of(selector, scope, program)
    else {
        return Some(false);
    };
    if selector_struct != option_id || selector_type_args.len() != 1 {
        return Some(false);
    }

    let step_type = Type::Struct {
        struct_id: step_id,
        type_args: step_type_args.to_vec(),
    };
    let old_payload_type = selector_type_args[0].clone();
    if !transform_carrier_selector(
        selector,
        option_id,
        &old_payload_type,
        &step_type,
        loop_fid,
        step_id,
        step_type_args,
        cluster,
        ret_type,
        scope,
        program,
    ) {
        return Some(false);
    }

    if !transform_block_tails(
        &mut cases[none_index].body,
        loop_fid,
        step_id,
        step_type_args,
        cluster,
        ret_type,
        scope,
        program,
    ) {
        return Some(false);
    }
    cases[some_index].body.tail = BlockTail::Value(Expr::Var(payload));
    Some(true)
}

#[allow(clippy::too_many_arguments)]
fn transform_carrier_selector(
    expression: &mut Expr,
    option_id: StructId,
    old_payload_type: &Type,
    step_type: &Type,
    loop_fid: FunId,
    step_id: StructId,
    step_type_args: &[Type],
    cluster: &HashSet<FunId>,
    ret_type: &Type,
    scope: &BTreeMap<VarId, Type>,
    program: &Program,
) -> bool {
    match expression {
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            if expr_calls_recursive_cluster(cond, loop_fid, cluster) {
                return false;
            }
            transform_carrier_selector_block(
                then_branch,
                option_id,
                old_payload_type,
                step_type,
                loop_fid,
                step_id,
                step_type_args,
                cluster,
                ret_type,
                scope,
                program,
            ) && transform_carrier_selector_block(
                else_branch,
                option_id,
                old_payload_type,
                step_type,
                loop_fid,
                step_id,
                step_type_args,
                cluster,
                ret_type,
                scope,
                program,
            )
        }
        Expr::Match {
            struct_id,
            selector,
            cases,
        } => {
            if expr_calls_recursive_cluster(selector, loop_fid, cluster) {
                return false;
            }
            let Some(arm_scopes) = match_arm_scopes(*struct_id, selector, cases, scope, program)
            else {
                return false;
            };
            cases.iter_mut().zip(arm_scopes).all(|(arm, arm_scope)| {
                transform_carrier_selector_block(
                    &mut arm.body,
                    option_id,
                    old_payload_type,
                    step_type,
                    loop_fid,
                    step_id,
                    step_type_args,
                    cluster,
                    ret_type,
                    &arm_scope,
                    program,
                )
            })
        }
        Expr::Pack {
            struct_id,
            type_args,
            variant,
            fields,
        } if *struct_id == option_id
            && type_args.as_slice() == [old_payload_type.clone()]
            && *variant == Some(super::option_aborts::OPTION_NONE_TAG)
            && fields.is_empty() =>
        {
            *type_args = vec![step_type.clone()];
            true
        }
        Expr::Pack {
            struct_id,
            type_args,
            variant,
            fields,
        } if *struct_id == option_id
            && type_args.as_slice() == [old_payload_type.clone()]
            && *variant == Some(super::option_aborts::OPTION_SOME_TAG)
            && fields.len() == 1 =>
        {
            if !transform_tail_expr(
                &mut fields[0],
                loop_fid,
                step_id,
                step_type_args,
                cluster,
                ret_type,
                scope,
                program,
            ) {
                return false;
            }
            *type_args = vec![step_type.clone()];
            true
        }
        _ => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn transform_carrier_selector_block(
    block: &mut Block,
    option_id: StructId,
    old_payload_type: &Type,
    step_type: &Type,
    loop_fid: FunId,
    step_id: StructId,
    step_type_args: &[Type],
    cluster: &HashSet<FunId>,
    ret_type: &Type,
    scope: &BTreeMap<VarId, Type>,
    program: &Program,
) -> bool {
    let mut local_scope = scope.clone();
    for statement in &block.stmts {
        let value = match statement {
            crate::ir::Stmt::Let { value, .. } | crate::ir::Stmt::Eval(value) => value,
        };
        if expr_calls_recursive_cluster(value, loop_fid, cluster) {
            return false;
        }
        if let crate::ir::Stmt::Let { pattern, value } = statement {
            let Ok(value_type) = type_of(value, &local_scope, program) else {
                return false;
            };
            if bind_pattern(pattern, &value_type, &mut local_scope).is_err() {
                return false;
            }
        }
    }
    let BlockTail::Value(tail) = &mut block.tail else {
        return false;
    };
    transform_carrier_selector(
        tail,
        option_id,
        old_payload_type,
        step_type,
        loop_fid,
        step_id,
        step_type_args,
        cluster,
        ret_type,
        &local_scope,
        program,
    )
}

fn match_arm_scopes(
    struct_id: StructId,
    selector: &Expr,
    cases: &[MatchArm],
    scope: &BTreeMap<VarId, Type>,
    program: &Program,
) -> Option<Vec<BTreeMap<VarId, Type>>> {
    let Type::Struct {
        struct_id: selector_struct,
        type_args,
    } = type_of(selector, scope, program).ok()?
    else {
        return None;
    };
    if selector_struct != struct_id {
        return None;
    }
    let structure = program.structs.get(&struct_id)?;
    cases
        .iter()
        .map(|arm| {
            let variant = structure.variant_by_tag(arm.variant)?;
            if variant.fields.len() != arm.bindings.len() {
                return None;
            }
            let mut arm_scope = scope.clone();
            for (binding, field) in arm.bindings.iter().zip(&variant.fields) {
                arm_scope.insert(
                    binding.clone(),
                    substitute_type_params(&field.field_type, &type_args),
                );
            }
            Some(arm_scope)
        })
        .collect()
}

fn expr_calls_recursive_cluster(
    expression: &Expr,
    loop_fid: FunId,
    cluster: &HashSet<FunId>,
) -> bool {
    struct Finder<'a> {
        loop_fid: FunId,
        cluster: &'a HashSet<FunId>,
        found: bool,
    }

    impl Visitor for Finder<'_> {
        fn visit_expr(&mut self, expression: &Expr) {
            if let Expr::Call { fun, .. } = expression {
                if *fun == self.loop_fid || self.cluster.contains(fun) {
                    self.found = true;
                    return;
                }
            }
            if !self.found {
                walk_expr_default(self, expression);
            }
        }
    }

    let mut finder = Finder {
        loop_fid,
        cluster,
        found: false,
    };
    finder.visit_expr(expression);
    finder.found
}

/// Every function id called anywhere in `b` (any position, any depth).
fn callees_of(b: &Block) -> HashSet<FunId> {
    #[derive(Default)]
    struct C {
        callees: HashSet<FunId>,
    }
    impl Visitor for C {
        fn visit_expr(&mut self, e: &Expr) {
            if let Expr::Call { fun, .. } = e {
                self.callees.insert(*fun);
            }
            walk_expr_default(self, e);
        }
    }
    let mut c = C::default();
    c.visit_block(b);
    c.callees
}

/// The loop's recursive continuation cluster: `Synthetic` continuation helpers
/// that `return_lift` extracted (and `cont_inline` left behind because they
/// exceed its size cap) which both (a) are reachable from the loop body via
/// cont calls and (b) can reach the loop again -- i.e. the mutually-recursive
/// `while_0 -> cont_1 -> cont_0 -> while_0` ring. Restricted by a caller-closure
/// fixpoint to conts whose EVERY caller is the loop or another cluster member,
/// so retyping each to the step sum is sound (no out-of-cluster `AbortResult`
/// use is mistyped). Empty for a plain self-recursive loop (e.g.
/// current-lending), which then defunctionalizes exactly as before.
/// Returns `(full, safe)`:
///
///   * `full` -- the entire recursive cont cycle (reachable-from-loop AND
///     reach-loop Synthetic conts), with no soundness filtering.
///   * `safe` -- `full` minus conts that also have a caller OUTSIDE the cluster
///     (those can't be retyped to the step sum without mistyping that other use).
/// `safe == full` means the loop is FULLY flattenable: defunctionalizing leaves
/// a total `loop_step` and only the matcher recurses. A strict subset means a
/// cycle edge escapes, so the loop must be left as its `mutual partial_fixpoint`.
fn loop_cont_clusters(program: &Program, loop_fid: FunId) -> (HashSet<FunId>, HashSet<FunId>) {
    let is_synth = |fid: FunId| {
        program
            .functions
            .get(&fid)
            .is_some_and(|f| matches!(f.kind, FunctionKind::Synthetic))
    };
    // Forward: Synthetic conts transitively called from the loop body.
    let mut forward: HashSet<FunId> = HashSet::new();
    let mut work: Vec<FunId> = callees_of(&program.functions[&loop_fid].body)
        .into_iter()
        .filter(|f| is_synth(*f))
        .collect();
    while let Some(c) = work.pop() {
        if !forward.insert(c) {
            continue;
        }
        for d in callees_of(&program.functions[&c].body) {
            if is_synth(d) && !forward.contains(&d) {
                work.push(d);
            }
        }
    }
    // Backward: conts that can transitively reach `loop_fid` (fixpoint).
    let mut reaches: HashSet<FunId> = HashSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for &c in &forward {
            if reaches.contains(&c) {
                continue;
            }
            let cs = callees_of(&program.functions[&c].body);
            if cs.contains(&loop_fid) || cs.iter().any(|d| reaches.contains(d)) {
                reaches.insert(c);
                changed = true;
            }
        }
    }
    // Candidates: reachable-from-loop AND reach-loop Synthetic conts.
    let mut candidates: HashSet<FunId> = forward
        .iter()
        .copied()
        .filter(|c| reaches.contains(c))
        .collect();
    let full = candidates.clone();
    // Reverse call map: which functions call each id.
    let mut callers: HashMap<FunId, HashSet<FunId>> = HashMap::new();
    for (caller, f) in program.functions.iter() {
        for callee in callees_of(&f.body) {
            callers.entry(callee).or_default().insert(*caller);
        }
    }
    // Soundness: only retype a cont when EVERY caller is inside the cluster
    // (the loop itself or another candidate). A cont also reachable from a
    // non-cluster site (e.g. the loop's `after` block) must keep its
    // `AbortResult` type, so drop it -- and, by fixpoint, anything that then
    // depends on it -- rather than mistype that other use.
    loop {
        let bad: Vec<FunId> = candidates
            .iter()
            .copied()
            .filter(|c| {
                callers.get(c).is_some_and(|cs| {
                    cs.iter()
                        .any(|caller| *caller != loop_fid && !candidates.contains(caller))
                })
            })
            .collect();
        if bad.is_empty() {
            break;
        }
        for b in bad {
            candidates.remove(&b);
        }
    }
    (full, candidates)
}

/// The soundly-retypeable cont cluster (the `safe` half of [`loop_cont_clusters`]).
fn loop_cont_cluster(program: &Program, loop_fid: FunId) -> HashSet<FunId> {
    loop_cont_clusters(program, loop_fid).1
}

/// Transitive closure over `graph` starting from `start` (inclusive).
fn reach(start: FunId, graph: &HashMap<FunId, HashSet<FunId>>) -> HashSet<FunId> {
    let mut seen = HashSet::new();
    let mut work = vec![start];
    while let Some(f) = work.pop() {
        if !seen.insert(f) {
            continue;
        }
        if let Some(next) = graph.get(&f) {
            for &n in next {
                if !seen.contains(&n) {
                    work.push(n);
                }
            }
        }
    }
    seen
}

/// True iff `loop_fid`'s strongly-connected component (functions both reachable
/// from it and able to reach it) contains a DIFFERENT loop body -- i.e. the
/// loop is mutually recursive with another loop (possibly via a continuation).
fn loop_in_multiloop_scc(
    loop_fid: FunId,
    callee_map: &HashMap<FunId, HashSet<FunId>>,
    caller_map: &HashMap<FunId, HashSet<FunId>>,
    loop_bodies: &HashSet<FunId>,
) -> bool {
    let fwd = reach(loop_fid, callee_map);
    let bwd = reach(loop_fid, caller_map);
    loop_bodies
        .iter()
        .any(|l| *l != loop_fid && fwd.contains(l) && bwd.contains(l))
}

fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

// (depth heuristics removed -- defunctionalization is now applied to every
// safe abort loop, so no nesting-depth threshold is needed.)
