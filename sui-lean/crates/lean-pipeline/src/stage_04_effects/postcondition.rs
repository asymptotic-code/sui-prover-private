//! Stage 4 postcondition validator.
//!
//! Runs after Transforms A-E and again before rendering. Checks the
//! stage-4-local effects and world-threading invariants:
//!
//! 1. Every executable source/test function and state-writing helper that
//!    needs World carries a `World` parameter and return slot. Read-only
//!    stage-7 helpers may instead capture a World snapshot while preserving
//!    their natural return type.
//! 2. Every executable Call supplies concrete World variables at all World
//!    argument positions and captures every returned World slot. Calls that
//!    return World cannot remain buried inside another expression.
//! 3. World-consuming calls and WriteBack operations consume the current
//!    token, and every executable exit returns the current token. Branch,
//!    loop, and labeled-block joins preserve that succession.
//! 4. Quantifiers can observe the current World snapshot but cannot advance
//!    it or call mutating functions.
//! 5. Every GlobalMut native declaration has a complete World ABI, including
//!    declarations unreachable from translated functions.
//! 6. Other executable functions have no stray World plumbing. Logical proof
//!    environments may carry World as read-only input data.
//!
//! This deliberately does not run the base IR scope validator. Before
//! stage 5, stage 2's branch-local assignment merges are represented as
//! `Eval(If { arm: let t = ... })` followed by a use of `t`; stage 5's
//! phi pass turns that into an explicitly scoped `Let`. Running the full
//! validator here rejects valid pre-SSA input for the wrong reason.
//!
//! Called from `run()` in `cfg(debug_assertions)` after Transform E.

use crate::ir::{Block, BlockTail, Expr, FunId, Function, MatchArm, Program, Stmt, StructId};

use super::common::{direct_world_positions, is_impure_user, is_world_type, type_carries_world};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PostconditionError {
    /// A function with an executable World channel is missing either its
    /// World parameter or its World return slot.
    MalformedSignature { function: FunId },
    /// A GlobalMut native declaration was not augmented with both a World
    /// parameter and a World return slot.
    MalformedNativeSignature { native: FunId },
    /// A dynamic-field WriteBack used a non-World input or failed to expose
    /// its returned World slot through a supported sequencing position.
    MalformedWorldWriteBack { function: FunId },
    /// A stateful operation or function exit used an older World token after
    /// a newer token had already been produced.
    StaleWorldToken { function: FunId },
    /// A call whose declared ABI returns World was not rewritten to thread
    /// its World arguments or capture every returned World slot.
    LingeringUnthreadedCall { function: FunId, callee: FunId },
    /// A function with an executable World channel does not return World at
    /// every function exit.
    ReturnMissingWorld { function: FunId },
    /// A function outside the World-threading closure has stray World
    /// plumbing in its executable signature.
    WorldOnPureFunction { function: FunId },
    /// A Call inside a quantifier body (`forall!` / `map!` etc.)
    /// targets a callee that mutates state -- either a
    /// `&mut`-bearing helper (LocalMut) or one with global side
    /// effects (GlobalMut). Quantifier bodies are pure logical
    /// predicates and must not contain mutation: a `bag::add(&mut
    /// bag, k, v)` or `transfer::transfer(...)` inside a `forall!`
    /// makes no semantic sense, and the renderer would in any case
    /// treat the call as an uninterpreted symbol -- propagating
    /// silently incorrect verification. Reject loudly instead.
    MutCallInQuantifier {
        function: FunId,
        callee: FunId,
        callee_mutation: crate::ir::MutLevel,
    },
}

pub fn check(program: &Program, world_id: StructId) -> Result<(), PostconditionError> {
    // `needs_world` is the same set stage 4's signature pass uses --
    // see the doc on `compute_needs_world` in `common.rs`. A
    // `#[ext(pure)]` user helper that transitively calls
    // globally-mutating framework natives ends up in `needs_world`
    // and is legitimately World-augmented even though its
    // `Function::effects` stays `Effects::PURE`. We use the set to
    // decide whether a World param on a non-GlobalMut function is
    // legitimate (skip `WorldOnPureFunction`) or stray (still
    // report it).
    let needs_world = super::common::compute_needs_world(program);
    let proof_environments = proof_environment_ids(program);

    for (fid, func) in &program.functions {
        let fid = *fid;
        // Reject mutation inside logical quantifier bodies before the more
        // general call-threading checks so the specific violation wins.
        check_quantifier_bodies_are_pure(fid, func, program)?;
        let var_types = collect_typed_vars(func, program);
        check_world_call_argument_types(fid, func, program, world_id, &var_types)?;
        let has_world_param = func
            .signature
            .params
            .iter()
            .any(|param| is_world_type(&param.ty, world_id));
        let return_carries_world = type_carries_world(&func.signature.return_type, world_id);
        let is_proof_environment = proof_environments.contains(&fid);
        let is_stage7_helper = matches!(
            func.kind,
            crate::ir::FunctionKind::LoopBody { .. }
                | crate::ir::FunctionKind::LoopAfter { .. }
                | crate::ir::FunctionKind::Synthetic
        );
        if !is_proof_environment {
            check_impure_body_calls(fid, func, program, world_id)?;
        }
        let checks_world_body = !is_proof_environment
            && (is_impure_user(func)
                || func.effects.world_writes
                || (!is_stage7_helper && needs_world.contains(&fid))
                || (has_world_param && return_carries_world));
        if checks_world_body {
            check_impure_signature(fid, func, world_id)?;
            check_impure_body_tails(fid, func, program, world_id, var_types)?;
        } else {
            check_non_channel_signature(fid, func, world_id)?;
        }
        super::world_flow::check_function(func, program, world_id).map_err(
            |error| match error {
                super::world_flow::WorldFlowError::StaleToken => {
                    PostconditionError::StaleWorldToken { function: fid }
                }
                super::world_flow::WorldFlowError::MalformedWriteBack => {
                    PostconditionError::MalformedWorldWriteBack { function: fid }
                }
            },
        )?;
    }
    check_global_mut_native_signatures(program, world_id)
}

fn check_global_mut_native_signatures(
    program: &Program,
    world_id: StructId,
) -> Result<(), PostconditionError> {
    for (fid, native) in &program.natives.decls {
        if native.effects.mutation != crate::ir::MutLevel::GlobalMut {
            continue;
        }
        let world_param_count = native
            .signature
            .params
            .iter()
            .filter(|param| is_world_type(&param.ty, world_id))
            .count();
        let world_return_count =
            direct_world_positions(&native.signature.return_type, world_id).len();
        if world_param_count != 1 || world_return_count != 1 {
            return Err(PostconditionError::MalformedNativeSignature { native: *fid });
        }
    }
    Ok(())
}

fn check_impure_signature(
    fid: FunId,
    func: &Function,
    world_id: StructId,
) -> Result<(), PostconditionError> {
    // Existence check: signatures must carry a `world: World` param
    // AND a `World` slot in the return tuple. Stage 4 puts both at
    // the end of the signature it produces; downstream stages may
    // shuffle the relative position (stage 7's loop_extract may
    // capture additional vars after the world slot in params), but the
    // World-typed slots themselves must survive. Use "World appears
    // somewhere in params / return" rather than the stricter "World
    // is last".
    let has_world_param = func
        .signature
        .params
        .iter()
        .any(|p| is_world_type(&p.ty, world_id));
    if !has_world_param {
        return Err(PostconditionError::MalformedSignature { function: fid });
    }
    let return_has_world = match &func.signature.return_type {
        crate::ir::Type::Tuple(items) => items.iter().any(|t| is_world_type(t, world_id)),
        other => is_world_type(other, world_id),
    };
    if !return_has_world {
        return Err(PostconditionError::MalformedSignature { function: fid });
    }
    Ok(())
}

/// Every function that is a logical proof environment rather than an
/// executable one -- directly by [`crate::ir::FunctionKind`], or by descent.
///
/// Checks 2, 3 and 6 are about EXECUTABLE world plumbing, and a `.aborts` /
/// `.ensures` / `.requires` companion is exempt from them because it threads no
/// state: it answers a question about the target, and its exit is an
/// `AbortResult` / `Prop`, not a World.
///
/// Stage 7 then lifts pieces of that same body into `.cont_N` fragments, which
/// carry [`crate::ir::FunctionKind::Synthetic`] and no `target` back-pointer --
/// so the exemption stopped at the split and the identical statements were
/// checked in the fragment and unchecked in the parent. Nothing about the
/// program changed at that split, so the validator's coverage must not change
/// either: the ancestry is recovered by name, exactly as the renderer's
/// typeparam/universe passes recover it (`render::function`,
/// `render::dyn_type_universe`), walking up through `Synthetic` levels and
/// through levels `cont_inline` dropped.
///
/// Measured instance: navi's `dynamic_health_factor_spec.aborts.cont_0.cont_0`
/// binds `dyn_liquidation_threshold_expected`'s returned World slot to a hole
/// because stage 6 eliminated it as dead (nothing downstream of it on the
/// abort side reads World, and the fragment returns an `AbortResult`). That is
/// correct dead-code elimination inside a proof environment, reported as
/// `LingeringUnthreadedCall`.
fn proof_environment_ids(program: &Program) -> std::collections::BTreeSet<FunId> {
    use crate::ir::FunctionKind;
    fn is_logical(kind: &FunctionKind) -> bool {
        matches!(
            kind,
            FunctionKind::Spec { .. } | FunctionKind::Theorem { .. } | FunctionKind::Axiom { .. }
        )
    }
    let mut name_index: std::collections::HashMap<(crate::ir::ModId, &str), FunId> =
        std::collections::HashMap::new();
    for (fid, func) in &program.functions {
        name_index.insert((func.module, func.name.as_str()), *fid);
    }
    let mut ids: std::collections::BTreeSet<FunId> = program
        .functions
        .iter()
        .filter(|(_, func)| is_logical(&func.kind))
        .map(|(fid, _)| *fid)
        .collect();
    for (fid, func) in &program.functions {
        if !matches!(func.kind, FunctionKind::Synthetic) {
            continue;
        }
        let mut base = func.name.as_str();
        while let Some(parent) = crate::ir::names::cont_parent(base) {
            match name_index
                .get(&(func.module, parent))
                .and_then(|pfid| program.functions.get(pfid))
            {
                Some(ancestor) if is_logical(&ancestor.kind) => {
                    ids.insert(*fid);
                    break;
                }
                // A dropped level (`cont_inline`) or another fragment: keep
                // climbing. Anything else settles the question negatively.
                None
                | Some(crate::ir::Function {
                    kind: FunctionKind::Synthetic,
                    ..
                }) => {}
                Some(_) => break,
            }
            base = parent;
        }
    }
    ids
}

fn check_impure_body_calls(
    fid: FunId,
    func: &Function,
    program: &Program,
    world_id: StructId,
) -> Result<(), PostconditionError> {
    walk_block_calls(&func.body, fid, program, world_id)
}

fn check_world_call_argument_types(
    fid: FunId,
    func: &Function,
    program: &Program,
    world_id: StructId,
    var_types: &std::collections::BTreeMap<crate::ir::VarId, crate::ir::Type>,
) -> Result<(), PostconditionError> {
    use crate::ir::visit::{walk_expr_default, Visitor};

    struct Checker<'a> {
        program: &'a Program,
        world_id: StructId,
        var_types: &'a std::collections::BTreeMap<crate::ir::VarId, crate::ir::Type>,
        bad_callee: Option<FunId>,
    }

    impl Visitor for Checker<'_> {
        fn visit_expr(&mut self, expr: &Expr) {
            if self.bad_callee.is_some() {
                return;
            }
            if let Expr::Call { fun, args, .. } = expr {
                if let Some(callee) = self.program.lookup_callee(*fun) {
                    let signature = callee.signature();
                    let world_params: Vec<_> = signature
                        .params
                        .iter()
                        .enumerate()
                        .filter(|(_, param)| is_world_type(&param.ty, self.world_id))
                        .map(|(index, _)| index)
                        .collect();
                    let malformed_global = callee.effects().mutation
                        == crate::ir::MutLevel::GlobalMut
                        && (world_params.is_empty()
                            || !type_carries_world(&signature.return_type, self.world_id));
                    let wrong_argument = world_params.into_iter().any(|index| {
                        let valid = match args.get(index) {
                            Some(Expr::Var(var)) => self
                                .var_types
                                .get(var)
                                .is_some_and(|ty| is_world_type(ty, self.world_id)),
                            _ => false,
                        };
                        !valid
                    });
                    if malformed_global || wrong_argument {
                        self.bad_callee = Some(*fun);
                        return;
                    }
                }
            }
            walk_expr_default(self, expr);
        }
    }

    let mut checker = Checker {
        program,
        world_id,
        var_types,
        bad_callee: None,
    };
    checker.visit_block(&func.body);
    if let Some(callee) = checker.bad_callee {
        Err(PostconditionError::LingeringUnthreadedCall {
            function: fid,
            callee,
        })
    } else {
        Ok(())
    }
}

/// Walk every quantifier body in `func` and reject any Call that can
/// mutate local state or write World. Quantifier bodies
/// (`forall!` / `map!` / etc.) are pure logical predicates: a
/// mutating callee makes no semantic sense, and the renderer would
/// otherwise treat the call as an uninterpreted symbol -- silently
/// producing incorrect verification.
///
/// The check is structural and applies to every function
/// regardless of its own classification.
fn check_quantifier_bodies_are_pure(
    fid: FunId,
    func: &Function,
    program: &Program,
) -> Result<(), PostconditionError> {
    walk_block_for_quantifiers(&func.body, fid, program)
}

fn walk_block_for_quantifiers(
    block: &Block,
    fid: FunId,
    program: &Program,
) -> Result<(), PostconditionError> {
    for stmt in &block.stmts {
        match stmt {
            Stmt::Eval(e) | Stmt::Let { value: e, .. } => {
                walk_expr_for_quantifiers(e, fid, program)?;
            }
        }
    }
    match &block.tail {
        BlockTail::Value(e) => walk_expr_for_quantifiers(e, fid, program)?,
        BlockTail::Abort { code } => walk_expr_for_quantifiers(code, fid, program)?,
        BlockTail::Break { value, .. } => walk_expr_for_quantifiers(value, fid, program)?,
        BlockTail::Continue { value, .. } => walk_expr_for_quantifiers(value, fid, program)?,
        BlockTail::Return(e) => walk_expr_for_quantifiers(e, fid, program)?,
        BlockTail::ReturnFromBlock { value, .. } => walk_expr_for_quantifiers(value, fid, program)?,
    }
    Ok(())
}

fn walk_expr_for_quantifiers(
    expr: &Expr,
    fid: FunId,
    program: &Program,
) -> Result<(), PostconditionError> {
    match expr {
        Expr::Quantifier { body, domain, .. } => {
            // The domain may contain a Call too, but those run
            // OUTSIDE the predicate body and are subject to normal
            // call-augmentation rules. Only the predicate body is
            // strictly pure.
            walk_quant_domain_for_quantifiers(domain, fid, program)?;
            reject_mut_calls_in(body, fid, program)?;
        }
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            walk_expr_for_quantifiers(cond, fid, program)?;
            walk_block_for_quantifiers(then_branch, fid, program)?;
            walk_block_for_quantifiers(else_branch, fid, program)?;
        }
        Expr::Match {
            selector, cases, ..
        } => {
            walk_expr_for_quantifiers(selector, fid, program)?;
            for MatchArm { body, .. } in cases {
                walk_block_for_quantifiers(body, fid, program)?;
            }
        }
        Expr::While {
            header, cond, body, ..
        } => {
            walk_block_for_quantifiers(header, fid, program)?;
            walk_expr_for_quantifiers(cond, fid, program)?;
            walk_block_for_quantifiers(body, fid, program)?;
        }
        Expr::Call { args, .. } => {
            for a in args {
                walk_expr_for_quantifiers(a, fid, program)?;
            }
        }
        Expr::Tuple(items) | Expr::Pack { fields: items, .. } => {
            for item in items {
                walk_expr_for_quantifiers(item, fid, program)?;
            }
        }
        Expr::BinOp { lhs, rhs, .. } => {
            walk_expr_for_quantifiers(lhs, fid, program)?;
            walk_expr_for_quantifiers(rhs, fid, program)?;
        }
        Expr::UnOp { operand, .. } => walk_expr_for_quantifiers(operand, fid, program)?,
        Expr::BitOp(op) => match op {
            crate::ir::BitOp::Extract { operand, .. }
            | crate::ir::BitOp::ZeroExtend { operand, .. }
            | crate::ir::BitOp::SignExtend { operand, .. } => {
                walk_expr_for_quantifiers(operand, fid, program)?;
            }
            crate::ir::BitOp::Concat { high, low } => {
                walk_expr_for_quantifiers(high, fid, program)?;
                walk_expr_for_quantifiers(low, fid, program)?;
            }
        },
        Expr::Field { base, .. }
        | Expr::Unpack { value: base, .. }
        | Expr::ReadRef(base)
        | Expr::ToProp(base)
        | Expr::ToBool(base) => walk_expr_for_quantifiers(base, fid, program)?,
        Expr::WriteRef { reference, value } => {
            walk_expr_for_quantifiers(reference, fid, program)?;
            walk_expr_for_quantifiers(value, fid, program)?;
        }
        Expr::Borrow { step, base } => {
            for operand in step.exprs() {
                walk_expr_for_quantifiers(operand, fid, program)?;
            }
            walk_expr_for_quantifiers(base, fid, program)?;
        }
        Expr::Update { step, base, value } => {
            for operand in step.exprs() {
                walk_expr_for_quantifiers(operand, fid, program)?;
            }
            walk_expr_for_quantifiers(base, fid, program)?;
            walk_expr_for_quantifiers(value, fid, program)?;
        }
        Expr::LabeledBlock { body, .. } => walk_block_for_quantifiers(body, fid, program)?,
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => {}
    }
    Ok(())
}

fn walk_quant_domain_for_quantifiers(
    domain: &crate::ir::QuantDomain,
    fid: FunId,
    program: &Program,
) -> Result<(), PostconditionError> {
    use crate::ir::QuantDomain::*;
    match domain {
        Unbounded => Ok(()),
        Range { start, end } => {
            walk_expr_for_quantifiers(start, fid, program)?;
            walk_expr_for_quantifiers(end, fid, program)
        }
        VecRange { vec, start, end } => {
            walk_expr_for_quantifiers(vec, fid, program)?;
            walk_expr_for_quantifiers(start, fid, program)?;
            walk_expr_for_quantifiers(end, fid, program)
        }
        Collection(e) => walk_expr_for_quantifiers(e, fid, program),
    }
}

fn reject_mut_calls_in_quant_domain(
    domain: &crate::ir::QuantDomain,
    fid: FunId,
    program: &Program,
) -> Result<(), PostconditionError> {
    use crate::ir::QuantDomain::*;
    match domain {
        Unbounded => Ok(()),
        Range { start, end } => {
            reject_mut_calls_in_expr(start, fid, program)?;
            reject_mut_calls_in_expr(end, fid, program)
        }
        VecRange { vec, start, end } => {
            reject_mut_calls_in_expr(vec, fid, program)?;
            reject_mut_calls_in_expr(start, fid, program)?;
            reject_mut_calls_in_expr(end, fid, program)
        }
        Collection(e) => reject_mut_calls_in_expr(e, fid, program),
    }
}

/// Inside a quantifier body, reject any Call whose callee mutates
/// state. Recursively walks the body so a Call buried in a
/// `Tuple` / `Pack` / `BinOp` etc. is caught too. Sub-quantifiers
/// in the body are walked through the same rule (still strict).
fn reject_mut_calls_in(
    block: &Block,
    fid: FunId,
    program: &Program,
) -> Result<(), PostconditionError> {
    for stmt in &block.stmts {
        match stmt {
            Stmt::Eval(e) | Stmt::Let { value: e, .. } => {
                reject_mut_calls_in_expr(e, fid, program)?;
            }
        }
    }
    match &block.tail {
        BlockTail::Value(e) => reject_mut_calls_in_expr(e, fid, program)?,
        BlockTail::Abort { code } => reject_mut_calls_in_expr(code, fid, program)?,
        BlockTail::Break { value, .. } => reject_mut_calls_in_expr(value, fid, program)?,
        BlockTail::Continue { value, .. } => reject_mut_calls_in_expr(value, fid, program)?,
        BlockTail::Return(e) => reject_mut_calls_in_expr(e, fid, program)?,
        BlockTail::ReturnFromBlock { value, .. } => reject_mut_calls_in_expr(value, fid, program)?,
    }
    Ok(())
}

fn reject_mut_calls_in_expr(
    expr: &Expr,
    fid: FunId,
    program: &Program,
) -> Result<(), PostconditionError> {
    if let Expr::Call { fun, .. } = expr {
        if let Some(callee) = program.lookup_callee(*fun) {
            let effects = callee.effects();
            let mutation = effects.mutation;
            if mutation == crate::ir::MutLevel::LocalMut || effects.world_writes {
                return Err(PostconditionError::MutCallInQuantifier {
                    function: fid,
                    callee: *fun,
                    callee_mutation: mutation,
                });
            }
        }
    }
    match expr {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            reject_mut_calls_in_expr(cond, fid, program)?;
            reject_mut_calls_in(then_branch, fid, program)?;
            reject_mut_calls_in(else_branch, fid, program)?;
        }
        Expr::Match {
            selector, cases, ..
        } => {
            reject_mut_calls_in_expr(selector, fid, program)?;
            for MatchArm { body, .. } in cases {
                reject_mut_calls_in(body, fid, program)?;
            }
        }
        Expr::While {
            header, cond, body, ..
        } => {
            reject_mut_calls_in(header, fid, program)?;
            reject_mut_calls_in_expr(cond, fid, program)?;
            reject_mut_calls_in(body, fid, program)?;
        }
        Expr::Quantifier { body, domain, .. } => {
            // Nested quantifier inside a quantifier body. The
            // domain runs as part of the outer body; recurse with
            // the strict rule.
            reject_mut_calls_in_quant_domain(domain, fid, program)?;
            reject_mut_calls_in(body, fid, program)?;
        }
        Expr::Call { args, .. } => {
            for a in args {
                reject_mut_calls_in_expr(a, fid, program)?;
            }
        }
        Expr::Tuple(items) | Expr::Pack { fields: items, .. } => {
            for item in items {
                reject_mut_calls_in_expr(item, fid, program)?;
            }
        }
        Expr::BinOp { lhs, rhs, .. } => {
            reject_mut_calls_in_expr(lhs, fid, program)?;
            reject_mut_calls_in_expr(rhs, fid, program)?;
        }
        Expr::UnOp { operand, .. } => reject_mut_calls_in_expr(operand, fid, program)?,
        Expr::BitOp(op) => match op {
            crate::ir::BitOp::Extract { operand, .. }
            | crate::ir::BitOp::ZeroExtend { operand, .. }
            | crate::ir::BitOp::SignExtend { operand, .. } => {
                reject_mut_calls_in_expr(operand, fid, program)?;
            }
            crate::ir::BitOp::Concat { high, low } => {
                reject_mut_calls_in_expr(high, fid, program)?;
                reject_mut_calls_in_expr(low, fid, program)?;
            }
        },
        Expr::Field { base, .. }
        | Expr::Unpack { value: base, .. }
        | Expr::ReadRef(base)
        | Expr::ToProp(base)
        | Expr::ToBool(base) => reject_mut_calls_in_expr(base, fid, program)?,
        Expr::WriteRef { reference, value } => {
            reject_mut_calls_in_expr(reference, fid, program)?;
            reject_mut_calls_in_expr(value, fid, program)?;
        }
        Expr::Borrow { step, base } => {
            for operand in step.exprs() {
                reject_mut_calls_in_expr(operand, fid, program)?;
            }
            reject_mut_calls_in_expr(base, fid, program)?;
        }
        Expr::Update { step, base, value } => {
            for operand in step.exprs() {
                reject_mut_calls_in_expr(operand, fid, program)?;
            }
            reject_mut_calls_in_expr(base, fid, program)?;
            reject_mut_calls_in_expr(value, fid, program)?;
        }
        Expr::LabeledBlock { body, .. } => reject_mut_calls_in(body, fid, program)?,
        Expr::Var(_)
        | Expr::Const(_)
        | Expr::Unit
        | Expr::BorrowLoc(_)
        | Expr::BorrowGlobal(_)
        | Expr::WriteBack { .. }
        | Expr::IsParent { .. } => {}
    }
    Ok(())
}

fn walk_block_calls(
    block: &Block,
    fid: FunId,
    program: &Program,
    world_id: StructId,
) -> Result<(), PostconditionError> {
    for stmt in &block.stmts {
        walk_stmt_calls(stmt, fid, program, world_id)?;
    }
    walk_tail_calls(&block.tail, fid, program, world_id)
}

fn walk_stmt_calls(
    stmt: &Stmt,
    fid: FunId,
    program: &Program,
    world_id: StructId,
) -> Result<(), PostconditionError> {
    match stmt {
        // Top-level Call positions: check the threading directly,
        // do NOT recurse via walk_expr_calls (which would re-flag
        // the same Call as a buried error).
        Stmt::Eval(Expr::Call { fun, .. }) => {
            if let Some(callee) = program.lookup_callee(*fun) {
                if type_carries_world(&callee.signature().return_type, world_id) {
                    return Err(PostconditionError::LingeringUnthreadedCall {
                        function: fid,
                        callee: *fun,
                    });
                }
            }
            // Calls have no sub-blocks; no further recursion needed.
            Ok(())
        }
        Stmt::Let {
            pattern,
            value: Expr::Call { fun, .. },
        } => {
            if let Some(callee) = program.lookup_callee(*fun) {
                let captures_every_world =
                    direct_world_positions(&callee.signature().return_type, world_id)
                        .into_iter()
                        .all(|index| matches!(pattern.get(index), Some(Some(_))));
                if !captures_every_world {
                    return Err(PostconditionError::LingeringUnthreadedCall {
                        function: fid,
                        callee: *fun,
                    });
                }
            }
            Ok(())
        }
        Stmt::Eval(Expr::WriteBack { world: Some(_), .. }) => {
            Err(PostconditionError::MalformedWorldWriteBack { function: fid })
        }
        Stmt::Let {
            pattern,
            value: Expr::WriteBack { world: Some(_), .. },
        } => {
            if !matches!(pattern.get(1), Some(Some(_))) {
                return Err(PostconditionError::MalformedWorldWriteBack { function: fid });
            }
            Ok(())
        }
        // Non-Call values: recurse into sub-expressions for buried calls that
        // return World. Stage 4 cannot bind their World result from inside a
        // Tuple, Pack, BinOp, or similar compound expression.
        Stmt::Eval(e) => walk_expr_calls(e, fid, program, world_id),
        Stmt::Let { value, .. } => walk_expr_calls(value, fid, program, world_id),
    }
}

fn walk_tail_calls(
    tail: &BlockTail,
    fid: FunId,
    program: &Program,
    world_id: StructId,
) -> Result<(), PostconditionError> {
    match tail {
        BlockTail::Value(e) => walk_tail_expr_calls(e, fid, program, world_id),
        BlockTail::Break { value, .. }
        | BlockTail::Continue { value, .. }
        | BlockTail::Return(value)
        | BlockTail::ReturnFromBlock { value, .. } => {
            walk_tail_expr_calls(value, fid, program, world_id)
        }
        BlockTail::Abort { code } => walk_expr_calls(code, fid, program, world_id),
    }
}

/// Tail-position variant of `walk_expr_calls`. Differs in one place:
/// a `BlockTail::Value(Expr::Call(world_returning, ..))` is the function's
/// own return-value-producing call -- the equivalent of
/// `Stmt::Let { value: Call(impure, ..) }` at the boundary -- so it
/// should be validated at the callee signature's World position, NOT flagged
/// as a buried-in-expression
/// call. Sub-expression positions (If branches, Tuple slots, etc.)
/// fall back to the regular walker which keeps the buried-call
/// strictness.
fn walk_tail_expr_calls(
    expr: &Expr,
    fid: FunId,
    program: &Program,
    world_id: StructId,
) -> Result<(), PostconditionError> {
    match expr {
        // Honor the IR's always-Tuple invariant: a singleton tuple
        // `Tuple([inner])` is a transparent wrapper around `inner`,
        // produced when an augmented return is rendered uniformly
        // even for single-value returns. Treat the inner expression
        // as if it were the direct tail. Without this, a tail call
        // wrapped in `Tuple([Call(impure, ..)])` falls through to
        // the buried-call branch of `walk_expr_calls` and fires
        // `LingeringUnthreadedCall` even though it's a legitimately
        // threaded tail call.
        Expr::Tuple(items) if items.len() == 1 => {
            walk_tail_expr_calls(&items[0], fid, program, world_id)
        }
        Expr::Call { fun, args, .. } => {
            check_tail_position_call(*fun, args, fid, program, world_id)?;
            for a in args {
                walk_expr_calls(a, fid, program, world_id)?;
            }
            Ok(())
        }
        Expr::WriteBack { world: Some(_), .. } => Ok(()),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            walk_expr_calls(cond, fid, program, world_id)?;
            // Each arm is itself a sub-block whose tail is a
            // function exit (since the outer is a tail). Use
            // walk_block_calls' tail handling, which routes to
            // walk_tail_calls.
            walk_block_calls(then_branch, fid, program, world_id)?;
            walk_block_calls(else_branch, fid, program, world_id)
        }
        Expr::Match {
            selector, cases, ..
        } => {
            walk_expr_calls(selector, fid, program, world_id)?;
            for MatchArm { body, .. } in cases {
                walk_block_calls(body, fid, program, world_id)?;
            }
            Ok(())
        }
        _ => walk_expr_calls(expr, fid, program, world_id),
    }
}

/// Validate the structural shape of every declared World argument on a
/// tail-position call. Concrete variable types are checked by
/// `check_world_call_argument_types`.
fn check_tail_position_call(
    callee: FunId,
    args: &[Expr],
    fid: FunId,
    program: &Program,
    world_id: StructId,
) -> Result<(), PostconditionError> {
    let cref = match program.lookup_callee(callee) {
        Some(c) => c,
        None => return Ok(()),
    };
    let world_indices: Vec<_> = cref
        .signature()
        .params
        .iter()
        .enumerate()
        .filter(|(_, param)| is_world_type(&param.ty, world_id))
        .map(|(index, _)| index)
        .collect();
    let malformed_global = cref.effects().mutation == crate::ir::MutLevel::GlobalMut
        && (world_indices.is_empty()
            || !type_carries_world(&cref.signature().return_type, world_id));
    let ok = !malformed_global
        && world_indices
            .into_iter()
            .all(|index| matches!(args.get(index), Some(Expr::Var(_))));
    if !ok {
        return Err(PostconditionError::LingeringUnthreadedCall {
            function: fid,
            callee,
        });
    }
    Ok(())
}

fn walk_expr_calls(
    expr: &Expr,
    fid: FunId,
    program: &Program,
    world_id: StructId,
) -> Result<(), PostconditionError> {
    match expr {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            walk_expr_calls(cond, fid, program, world_id)?;
            walk_block_calls(then_branch, fid, program, world_id)?;
            walk_block_calls(else_branch, fid, program, world_id)?;
        }
        Expr::Match {
            selector, cases, ..
        } => {
            walk_expr_calls(selector, fid, program, world_id)?;
            for MatchArm { body, .. } in cases {
                walk_block_calls(body, fid, program, world_id)?;
            }
        }
        Expr::While {
            header, cond, body, ..
        } => {
            walk_block_calls(header, fid, program, world_id)?;
            walk_expr_calls(cond, fid, program, world_id)?;
            walk_block_calls(body, fid, program, world_id)?;
        }
        // Quantifiers read a fixed World snapshot. Transform D deliberately
        // hoists World-returning reads as `let (value, _) = call(...)`, so the
        // ordinary capture/advance lifecycle does not apply inside the body.
        // Argument types are still checked by the all-expression typed walk,
        // and `check_quantifier_bodies_are_pure` rejects mutating callees.
        Expr::Quantifier { .. } => {}
        Expr::Call { fun, args, .. } => {
            // A Call appearing inside another expression (Tuple, Pack,
            // BinOp, etc.) cannot carry a World result: there is no
            // destructure site at which to advance the threaded token.
            // Stage 4's call_augment rejects these with
            // `CallInExpressionPosition`; if one slips through, the
            // postcondition catches it as a LingeringUnthreadedCall.
            if let Some(callee) = program.lookup_callee(*fun) {
                if type_carries_world(&callee.signature().return_type, world_id) {
                    return Err(PostconditionError::LingeringUnthreadedCall {
                        function: fid,
                        callee: *fun,
                    });
                }
            }
            // Recurse into args -- a Call can have buried Calls in its args.
            for a in args {
                walk_expr_calls(a, fid, program, world_id)?;
            }
        }
        Expr::Tuple(items) | Expr::Pack { fields: items, .. } => {
            for item in items {
                walk_expr_calls(item, fid, program, world_id)?;
            }
        }
        Expr::BinOp { lhs, rhs, .. } => {
            walk_expr_calls(lhs, fid, program, world_id)?;
            walk_expr_calls(rhs, fid, program, world_id)?;
        }
        Expr::UnOp { operand, .. } => walk_expr_calls(operand, fid, program, world_id)?,
        Expr::BitOp(op) => match op {
            crate::ir::BitOp::Extract { operand, .. }
            | crate::ir::BitOp::ZeroExtend { operand, .. }
            | crate::ir::BitOp::SignExtend { operand, .. } => {
                walk_expr_calls(operand, fid, program, world_id)?;
            }
            crate::ir::BitOp::Concat { high, low } => {
                walk_expr_calls(high, fid, program, world_id)?;
                walk_expr_calls(low, fid, program, world_id)?;
            }
        },
        Expr::Field { base, .. }
        | Expr::Unpack { value: base, .. }
        | Expr::ReadRef(base)
        | Expr::ToProp(base)
        | Expr::ToBool(base) => walk_expr_calls(base, fid, program, world_id)?,
        Expr::WriteRef { reference, value } => {
            walk_expr_calls(reference, fid, program, world_id)?;
            walk_expr_calls(value, fid, program, world_id)?;
        }
        Expr::WriteBack { world: Some(_), .. } => {
            return Err(PostconditionError::MalformedWorldWriteBack { function: fid });
        }
        Expr::LabeledBlock { body, .. } => walk_block_calls(body, fid, program, world_id)?,
        _ => {}
    }
    Ok(())
}

fn check_impure_body_tails(
    fid: FunId,
    func: &Function,
    program: &Program,
    world_id: StructId,
    var_types: std::collections::BTreeMap<crate::ir::VarId, crate::ir::Type>,
) -> Result<(), PostconditionError> {
    let type_info = TailTypeInfo {
        var_types,
        world_id,
        return_type: func.signature.return_type.clone(),
        program,
    };
    let mut ok = true;
    walk_block_tails(&func.body, &type_info, /* top_level= */ true, &mut ok);
    if ok {
        Ok(())
    } else {
        Err(PostconditionError::ReturnMissingWorld { function: fid })
    }
}

struct TailTypeInfo<'a> {
    var_types: std::collections::BTreeMap<crate::ir::VarId, crate::ir::Type>,
    world_id: StructId,
    return_type: crate::ir::Type,
    program: &'a Program,
}

fn collect_typed_vars(
    func: &Function,
    program: &Program,
) -> std::collections::BTreeMap<crate::ir::VarId, crate::ir::Type> {
    use crate::ir::analysis::scope::{walk_typed_block, TypedScope, TypedScopeVisitor};
    use crate::ir::analysis::type_of::TypeOfError;
    use std::collections::{BTreeMap, BTreeSet};

    struct Collector {
        types: BTreeMap<crate::ir::VarId, crate::ir::Type>,
        conflicts: BTreeSet<crate::ir::VarId>,
    }

    impl TypedScopeVisitor for Collector {
        type Error = TypeOfError;

        fn visit_expr(&mut self, expr: &Expr, scope: &TypedScope) -> Result<(), TypeOfError> {
            let Expr::Var(var) = expr else {
                return Ok(());
            };
            let Some(ty) = scope.get(var) else {
                self.types.remove(var);
                self.conflicts.insert(var.clone());
                return Ok(());
            };
            if self.conflicts.contains(var) {
                return Ok(());
            }
            match self.types.get(var) {
                Some(previous) if previous != ty => {
                    self.types.remove(var);
                    self.conflicts.insert(var.clone());
                }
                Some(_) => {}
                None => {
                    self.types.insert(var.clone(), ty.clone());
                }
            }
            Ok(())
        }
    }

    fn fallback_typed_vars(
        block: &Block,
        program: &Program,
        initial: &BTreeMap<crate::ir::VarId, crate::ir::Type>,
    ) -> BTreeMap<crate::ir::VarId, crate::ir::Type> {
        use crate::ir::analysis::type_of::{bind_pattern, type_of};
        use crate::ir::visit::{walk_expr_default, walk_stmt_default, Visitor};

        struct RebindingChecker<'a> {
            scope: BTreeMap<crate::ir::VarId, crate::ir::Type>,
            initial: &'a BTreeMap<crate::ir::VarId, crate::ir::Type>,
            types: BTreeMap<crate::ir::VarId, crate::ir::Type>,
            conflicts: BTreeSet<crate::ir::VarId>,
            unsafe_params: BTreeSet<crate::ir::VarId>,
            program: &'a Program,
        }

        impl RebindingChecker<'_> {
            fn visit_branch(
                &mut self,
                block: &Block,
                base: &BTreeMap<crate::ir::VarId, crate::ir::Type>,
            ) -> Option<BTreeMap<crate::ir::VarId, crate::ir::Type>> {
                self.scope = base.clone();
                self.visit_block(block);
                matches!(block.tail, BlockTail::Value(_)).then(|| self.scope.clone())
            }

            fn join_fallthrough_scopes(
                base: &BTreeMap<crate::ir::VarId, crate::ir::Type>,
                mut branches: Vec<BTreeMap<crate::ir::VarId, crate::ir::Type>>,
            ) -> BTreeMap<crate::ir::VarId, crate::ir::Type> {
                let Some(mut joined) = branches.pop() else {
                    return base.clone();
                };
                joined.retain(|var, ty| branches.iter().all(|branch| branch.get(var) == Some(ty)));
                joined
            }

            fn mark_shadowing_binder(&mut self, binder: &crate::ir::VarId) {
                if self.initial.contains_key(binder) {
                    self.unsafe_params.insert(binder.clone());
                }
                self.scope.remove(binder);
            }

            fn record_var(&mut self, var: &crate::ir::VarId) {
                let Some(ty) = self.scope.get(var) else {
                    self.types.remove(var);
                    self.conflicts.insert(var.clone());
                    return;
                };
                if self.conflicts.contains(var) {
                    return;
                }
                match self.types.get(var) {
                    Some(previous) if previous != ty => {
                        self.types.remove(var);
                        self.conflicts.insert(var.clone());
                    }
                    Some(_) => {}
                    None => {
                        self.types.insert(var.clone(), ty.clone());
                    }
                }
            }
        }

        impl Visitor for RebindingChecker<'_> {
            fn visit_stmt(&mut self, stmt: &Stmt) {
                let Stmt::Let { pattern, value } = stmt else {
                    walk_stmt_default(self, stmt);
                    return;
                };
                let value_scope = self.scope.clone();
                self.visit_expr(value);
                let raw_type = type_of(value, &value_scope, self.program).ok();
                let effective_type =
                    crate::render::effective_type_of(value, self.program, &value_scope);
                let bindings = effective_type.into_iter().chain(raw_type).find_map(|ty| {
                    let mut bindings = BTreeMap::new();
                    bind_pattern(pattern, &ty, &mut bindings)
                        .is_ok()
                        .then_some(bindings)
                });
                for var in pattern.iter().flatten() {
                    let rebound_type = bindings.as_ref().and_then(|bindings| bindings.get(var));
                    if let Some(expected) = self.initial.get(var) {
                        if rebound_type != Some(expected) {
                            self.unsafe_params.insert(var.clone());
                        }
                    }
                    match rebound_type {
                        Some(ty) => {
                            self.scope.insert(var.clone(), ty.clone());
                        }
                        None => {
                            self.scope.remove(var);
                        }
                    }
                }
            }

            fn visit_expr(&mut self, expr: &Expr) {
                if let Expr::Var(var) = expr {
                    self.record_var(var);
                    return;
                }
                match expr {
                    Expr::If {
                        cond,
                        then_branch,
                        else_branch,
                    } => {
                        self.visit_expr(cond);
                        let base = self.scope.clone();
                        let branches = [then_branch.as_ref(), else_branch.as_ref()]
                            .into_iter()
                            .filter_map(|branch| self.visit_branch(branch, &base))
                            .collect();
                        self.scope = Self::join_fallthrough_scopes(&base, branches);
                        return;
                    }
                    Expr::Match {
                        struct_id,
                        selector,
                        cases,
                    } => {
                        fn type_args(
                            ty: &crate::ir::Type,
                            struct_id: crate::ir::StructId,
                        ) -> Vec<crate::ir::Type> {
                            match ty {
                                crate::ir::Type::Struct {
                                    struct_id: actual,
                                    type_args,
                                } if *actual == struct_id => type_args.clone(),
                                crate::ir::Type::Reference(inner)
                                | crate::ir::Type::MutableRef { inner, .. } => {
                                    type_args(inner, struct_id)
                                }
                                crate::ir::Type::Tuple(items) if items.len() == 1 => {
                                    type_args(&items[0], struct_id)
                                }
                                _ => Vec::new(),
                            }
                        }

                        let selector_type = type_of(selector, &self.scope, self.program)
                            .ok()
                            .or_else(|| {
                                crate::render::effective_type_of(
                                    selector,
                                    self.program,
                                    &self.scope,
                                )
                            });
                        self.visit_expr(selector);
                        let base = self.scope.clone();
                        let mut branches = Vec::new();
                        for arm in cases {
                            self.scope = base.clone();
                            for binder in &arm.bindings {
                                self.mark_shadowing_binder(binder);
                            }
                            if let Some(variant) = self
                                .program
                                .structs
                                .get(struct_id)
                                .and_then(|structure| structure.variant_by_tag(arm.variant))
                            {
                                let args = selector_type
                                    .as_ref()
                                    .map(|ty| type_args(ty, *struct_id))
                                    .unwrap_or_default();
                                for (binding, field) in arm.bindings.iter().zip(&variant.fields) {
                                    self.scope.insert(
                                        binding.clone(),
                                        crate::ir::analysis::substitute_type_params(
                                            &field.field_type,
                                            &args,
                                        ),
                                    );
                                }
                            }
                            self.visit_block(&arm.body);
                            if matches!(arm.body.tail, BlockTail::Value(_)) {
                                for binding in &arm.bindings {
                                    if let Some(ty) = base.get(binding) {
                                        self.scope.insert(binding.clone(), ty.clone());
                                    } else {
                                        self.scope.remove(binding);
                                    }
                                }
                                branches.push(self.scope.clone());
                            }
                        }
                        self.scope = Self::join_fallthrough_scopes(&base, branches);
                        return;
                    }
                    Expr::While {
                        header,
                        cond,
                        body,
                        iter_locals,
                        ..
                    } => {
                        let base = self.scope.clone();
                        let iter_types: Vec<_> = iter_locals
                            .iter()
                            .map(|(_, init)| type_of(init, &base, self.program).ok())
                            .collect();
                        for (_, init) in iter_locals {
                            self.scope = base.clone();
                            self.visit_expr(init);
                        }
                        self.scope = base.clone();
                        for ((binder, _), ty) in iter_locals.iter().zip(iter_types) {
                            self.mark_shadowing_binder(binder);
                            if let Some(ty) = ty {
                                self.scope.insert(binder.clone(), ty);
                            }
                        }
                        self.visit_block(header);
                        self.visit_expr(cond);
                        self.visit_block(body);
                        self.scope = base;
                        return;
                    }
                    Expr::Quantifier {
                        binder,
                        domain,
                        body,
                        ..
                    } => {
                        let base = self.scope.clone();
                        use crate::ir::QuantDomain;
                        match domain {
                            QuantDomain::Unbounded => {}
                            QuantDomain::Range { start, end } => {
                                self.visit_expr(start);
                                self.visit_expr(end);
                            }
                            QuantDomain::Collection(value) => self.visit_expr(value),
                            QuantDomain::VecRange { vec, start, end } => {
                                self.visit_expr(vec);
                                self.visit_expr(start);
                                self.visit_expr(end);
                            }
                        }
                        self.scope = base.clone();
                        self.mark_shadowing_binder(binder);
                        self.visit_block(body);
                        self.scope = base;
                        return;
                    }
                    Expr::LabeledBlock { body, .. } => {
                        let base = self.scope.clone();
                        self.visit_block(body);
                        self.scope = base;
                        return;
                    }
                    _ => {}
                }
                walk_expr_default(self, expr);
            }
        }

        let mut checker = RebindingChecker {
            scope: initial.clone(),
            initial,
            types: initial.clone(),
            conflicts: BTreeSet::new(),
            unsafe_params: BTreeSet::new(),
            program,
        };
        checker.visit_block(block);
        checker.types.retain(|var, _| {
            !checker.conflicts.contains(var) && !checker.unsafe_params.contains(var)
        });
        checker.types
    }

    let initial: BTreeMap<crate::ir::VarId, crate::ir::Type> = func
        .signature
        .params
        .iter()
        .map(|param| (param.var.clone(), param.ty.clone()))
        .collect();
    let mut collector = Collector {
        types: initial.clone(),
        conflicts: BTreeSet::new(),
    };
    if walk_typed_block(&mut collector, &func.body, initial.clone(), program).is_err() {
        return fallback_typed_vars(&func.body, program, &initial);
    }
    collector.types
}

/// Is this expression a "tail-position" exit that delegates to its
/// arm tails for the actual world-augmented value? Stage 7's
/// asymmetric_arms pass lifts `Stmt::Eval(If/Match)` into the outer
/// block's tail position, moving the previously-outer world-augmented
/// `BlockTail::Value(Tuple([..., Var(world)]))` into one of the arms.
/// After that rewrite, the outer block's tail is `Value(If/Match)`
/// where each arm independently terminates with either an
/// already-world-augmented `Value` or an `Abort`. The stage-4 invariant
/// ("every function exit returns World at its declared slot") still holds,
/// just one level deeper -- the check has to descend through the
/// tail-position If/Match to validate each arm.
fn is_top_level_dispatch(e: &Expr) -> bool {
    matches!(e, Expr::If { .. } | Expr::Match { .. })
}

/// Structural and typed variant of `value_already_world_augmented` for
/// the postcondition check. After stage 5 SSA, every World-threaded call rebinds
/// world to a fresh `world_N` VarId, so the body's tail rarely points at
/// the original world parameter. Accept the explicit
/// `Tuple([..., world_value])` shape after checking the expression at each
/// declared World position, and also a scoped variable whose concrete type carries
/// World at the slot declared by the function return type (as produced by
/// stage 7's return carrier).
fn value_world_shaped(value: &Expr, type_info: &TailTypeInfo<'_>) -> bool {
    match (&type_info.return_type, value) {
        (crate::ir::Type::Tuple(expected), Expr::Tuple(items)) => {
            world_expr_slots_match(expected, items, type_info)
        }
        (_, Expr::Var(var)) => type_info
            .var_types
            .get(var)
            .is_some_and(|actual| world_slots_match(&type_info.return_type, actual, type_info)),
        (expected, value) if is_world_type(expected, type_info.world_id) => {
            expr_yields_world(value, type_info)
        }
        _ => false,
    }
}

fn world_expr_slots_match(
    expected: &[crate::ir::Type],
    actual: &[Expr],
    type_info: &TailTypeInfo<'_>,
) -> bool {
    let mut found_world = false;
    for (index, expected) in expected.iter().enumerate() {
        if !is_world_type(expected, type_info.world_id) {
            continue;
        }
        found_world = true;
        if !actual
            .get(index)
            .is_some_and(|value| expr_yields_world(value, type_info))
        {
            return false;
        }
    }
    found_world
}

fn world_slots_match(
    expected: &crate::ir::Type,
    actual: &crate::ir::Type,
    type_info: &TailTypeInfo<'_>,
) -> bool {
    match (expected, actual) {
        (crate::ir::Type::Tuple(expected), crate::ir::Type::Tuple(actual)) => {
            let mut found_world = false;
            for (index, expected) in expected.iter().enumerate() {
                if !is_world_type(expected, type_info.world_id) {
                    continue;
                }
                found_world = true;
                if !actual
                    .get(index)
                    .is_some_and(|ty| is_world_type(ty, type_info.world_id))
                {
                    return false;
                }
            }
            found_world
        }
        (expected, actual) => {
            is_world_type(expected, type_info.world_id) && is_world_type(actual, type_info.world_id)
        }
    }
}

/// Does `e`, in a World slot declared by the return type, evaluate to the
/// threaded world? The base case is a variable whose concrete type is `World`. A
/// trailing conditional world-read (`*v = ..; if c { ..; world_b } else {
/// world_a }`) lands the world behind an `If`/`Match` whose every arm
/// yields world -- still a correctly-threaded world tail, just selected at
/// runtime (current-lending `borrow_then_repay_on_behalf_scenario` ends in
/// a conditional `get_reserve_underlying_balance` df-read). Accept those by
/// descending into the arms; an aborting arm produces no value, so the
/// world requirement is vacuous there.
fn expr_yields_world(e: &Expr, type_info: &TailTypeInfo<'_>) -> bool {
    match e {
        Expr::Var(var) => type_info
            .var_types
            .get(var)
            .is_some_and(|ty| is_world_type(ty, type_info.world_id)),
        Expr::Call { fun, type_args, .. } => call_return_type(*fun, type_args, type_info)
            .is_some_and(|ty| is_world_type(&ty, type_info.world_id)),
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            block_yields_world(then_branch, type_info) && block_yields_world(else_branch, type_info)
        }
        Expr::Match { cases, .. } => cases
            .iter()
            .all(|MatchArm { body, .. }| block_yields_world(body, type_info)),
        _ => false,
    }
}

fn block_yields_world(block: &Block, type_info: &TailTypeInfo<'_>) -> bool {
    match &block.tail {
        BlockTail::Value(e) => expr_yields_world(e, type_info),
        BlockTail::Abort { .. } => true,
        _ => false,
    }
}

fn call_return_type(
    fun: FunId,
    type_args: &[crate::ir::Type],
    type_info: &TailTypeInfo<'_>,
) -> Option<crate::ir::Type> {
    let callee = type_info.program.lookup_callee(fun)?;
    Some(crate::ir::analysis::substitute_type_params(
        &callee.signature().return_type,
        type_args,
    ))
}

fn call_returns_world_augmented(
    fun: FunId,
    type_args: &[crate::ir::Type],
    type_info: &TailTypeInfo<'_>,
) -> bool {
    call_return_type(fun, type_args, type_info)
        .is_some_and(|actual| world_slots_match(&type_info.return_type, &actual, type_info))
}

fn walk_block_tails(block: &Block, type_info: &TailTypeInfo<'_>, top_level: bool, ok: &mut bool) {
    for stmt in &block.stmts {
        let e = match stmt {
            Stmt::Let { value, .. } => value,
            Stmt::Eval(e) => e,
        };
        walk_expr_tails(e, type_info, ok);
    }
    match &block.tail {
        BlockTail::Return(v) => {
            check_value_augmented_or_descend(v, type_info, ok);
            walk_expr_tails(v, type_info, ok);
        }
        BlockTail::Value(e) if top_level => {
            check_value_augmented_or_descend(e, type_info, ok);
            walk_expr_tails(e, type_info, ok);
        }
        BlockTail::Value(e) => walk_expr_tails(e, type_info, ok),
        BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
            walk_expr_tails(value, type_info, ok);
        }
        BlockTail::Abort { code } => walk_expr_tails(code, type_info, ok),
        BlockTail::ReturnFromBlock { value, .. } => {
            walk_expr_tails(value, type_info, ok);
        }
    }
}

/// Treat `e` as a top-level fall-off / Return value. The base case
/// carries World at the position declared by the function return type; we
/// accept stage-7 asymmetric_arms's lifted form by
/// descending through tail-position `If` / `Match` and validating
/// each arm independently. Each arm's tail must either be
/// world-shaped, abort, dispatch to further arms, OR be a direct
/// Call whose return value is already world-augmented (the
/// stage-7 loop_extract emits `BlockTail::Value(Call(LoopBody, ..))`
/// at the entry of every extracted loop -- the callee's signature
/// has the world-augmented tuple return, so the tail of the call
/// site is correctly world-augmented by delegation).
fn check_value_augmented_or_descend(e: &Expr, type_info: &TailTypeInfo<'_>, ok: &mut bool) {
    if value_world_shaped(e, type_info) {
        return;
    }
    // Honor the IR's always-Tuple invariant: a singleton tuple
    // `Tuple([inner])` is a transparent wrapper around `inner` --
    // descend into the inner expression. Without this, a tail
    // call whose return type is already augmented (e.g.
    // `Tuple([Call])` where the Call returns `Tuple([..., World])`)
    // would fail the shape check, even though it's well-formed.
    if let Expr::Tuple(items) = e {
        if items.len() == 1 {
            check_value_augmented_or_descend(&items[0], type_info, ok);
            return;
        }
    }
    if is_top_level_dispatch(e) {
        check_dispatch_arms(e, type_info, ok);
        return;
    }
    if let Expr::Call { fun, type_args, .. } = e {
        // Tail-position calls delegate the returned world only when their
        // concrete return type actually contains the World slot. The args-side
        // threading is validated independently by `check_tail_position_call`.
        if !call_returns_world_augmented(*fun, type_args, type_info) {
            *ok = false;
        }
        return;
    }
    *ok = false;
}

fn check_dispatch_arms(e: &Expr, type_info: &TailTypeInfo<'_>, ok: &mut bool) {
    match e {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            check_arm_block(then_branch, type_info, ok);
            check_arm_block(else_branch, type_info, ok);
        }
        Expr::Match { cases, .. } => {
            for MatchArm { body, .. } in cases {
                check_arm_block(body, type_info, ok);
            }
        }
        _ => *ok = false,
    }
}

fn check_arm_block(block: &Block, type_info: &TailTypeInfo<'_>, ok: &mut bool) {
    // Walk the arm's body stmts for any Returns (which must be
    // world-augmented).
    for stmt in &block.stmts {
        let e = match stmt {
            Stmt::Let { value, .. } => value,
            Stmt::Eval(e) => e,
        };
        walk_expr_tails(e, type_info, ok);
    }
    match &block.tail {
        // Arm tails are themselves function exits at this point
        // (the surrounding If/Match was lifted to tail position by
        // asymmetric_arms). Reuse the top-level-Value check.
        BlockTail::Value(e) => check_value_augmented_or_descend(e, type_info, ok),
        BlockTail::Return(v) => {
            check_value_augmented_or_descend(v, type_info, ok);
            walk_expr_tails(v, type_info, ok);
        }
        // Aborts terminate without returning a value; no world
        // augmentation required.
        BlockTail::Abort { code } => walk_expr_tails(code, type_info, ok),
        // Break / Continue carry loop state, not function-return
        // values; nothing to check here.
        BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
            walk_expr_tails(value, type_info, ok);
        }
        BlockTail::ReturnFromBlock { value, .. } => {
            walk_expr_tails(value, type_info, ok);
        }
    }
}

fn walk_expr_tails(expr: &Expr, type_info: &TailTypeInfo<'_>, ok: &mut bool) {
    match expr {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            walk_expr_tails(cond, type_info, ok);
            walk_block_tails(then_branch, type_info, false, ok);
            walk_block_tails(else_branch, type_info, false, ok);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            walk_expr_tails(selector, type_info, ok);
            for MatchArm { body, .. } in cases {
                walk_block_tails(body, type_info, false, ok);
            }
        }
        Expr::While {
            header, cond, body, ..
        } => {
            walk_block_tails(header, type_info, false, ok);
            walk_expr_tails(cond, type_info, ok);
            walk_block_tails(body, type_info, false, ok);
        }
        Expr::Quantifier { body, .. } => {
            walk_block_tails(body, type_info, false, ok);
        }
        Expr::LabeledBlock { body, .. } => {
            walk_block_tails(body, type_info, false, ok);
        }
        _ => {}
    }
}

fn check_non_channel_signature(
    fid: FunId,
    func: &Function,
    world_id: StructId,
) -> Result<(), PostconditionError> {
    // Proof environments use World as logical input data. Read-only stage-7
    // helpers may capture the parent's World snapshot while preserving their
    // natural result type. Writers and helpers with a symmetric World ABI are
    // routed through the full channel checks before reaching this function.
    if matches!(
        func.kind,
        crate::ir::FunctionKind::Spec { .. }
            | crate::ir::FunctionKind::LoopBody { .. }
            | crate::ir::FunctionKind::LoopAfter { .. }
            | crate::ir::FunctionKind::Synthetic
            | crate::ir::FunctionKind::Theorem { .. }
            | crate::ir::FunctionKind::Axiom { .. },
    ) {
        return Ok(());
    }
    let has_world_param = func
        .signature
        .params
        .iter()
        .any(|p| is_world_type(&p.ty, world_id));
    let return_carries_world = match &func.signature.return_type {
        crate::ir::Type::Tuple(items) => items.iter().any(|t| is_world_type(t, world_id)),
        other => is_world_type(other, world_id),
    };
    if has_world_param || return_carries_world {
        return Err(PostconditionError::WorldOnPureFunction { function: fid });
    }
    Ok(())
}
