//! Mutation-usage analysis (split from `expr/mod.rs`, R2 of
//! `plans/lean-pipeline/renderer-split.md`).

use crate::ir::{BlockTail, Expr, Program, Stmt};

#[derive(Clone, Copy, PartialEq, Eq)]
enum RenderedBlockMode {
    FunctionBody,
    InnerValue,
    InnerEval,
}

/// Whether value-producing inner-block rendering erases this discarded result.
/// Eval-position blocks preserve the same statements, so mutation analysis must
/// apply this policy only in [`RenderedBlockMode::InnerValue`].
pub(in crate::render) fn is_erased_inner_discard(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Eval(_) => true,
        Stmt::Let { pattern, .. } => pattern.iter().all(Option::is_none),
    }
}

/// Compute the transitive closure: the set of `FunId`s in
/// `program.functions` whose rendered Lean def would textually
/// reference `AnyKey` / `Mutation` (either directly or via
/// transitively-called user functions).
///
/// Fixpoint: start with direct hits in the rendered signature/body, then add
/// functions whose surviving calls target an existing member. The block-mode
/// scan mirrors discard erasure so an IR-only call cannot create a phantom
/// named implicit. Cycles converge because the set grows monotonically.
pub(in crate::render) fn compute_mutation_users(
    program: &Program,
) -> std::collections::BTreeSet<crate::ir::FunId> {
    use std::collections::BTreeSet;
    let mut set: BTreeSet<crate::ir::FunId> = BTreeSet::new();
    // Direct hits: rendered signature OR body contains Mutation.
    for (fid, func) in program.functions.iter() {
        if signature_has_mutable_ref(&func.signature)
            || walk_block_for_mutation(&func.body, Some(program), None)
        {
            set.insert(*fid);
        }
    }
    // Iterate: a function calling any member of `set` joins it.
    loop {
        let snapshot = set.clone();
        let mut grew = false;
        for (fid, func) in program.functions.iter() {
            if snapshot.contains(fid) {
                continue;
            }
            if walk_block_for_mutation(&func.body, Some(program), Some(&snapshot)) {
                set.insert(*fid);
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    set
}

pub(in crate::render) fn walk_block_for_mutation(
    b: &crate::ir::Block,
    program: Option<&Program>,
    transitive_set: Option<&std::collections::BTreeSet<crate::ir::FunId>>,
) -> bool {
    walk_rendered_block_for_mutation(b, program, transitive_set, RenderedBlockMode::FunctionBody)
}

fn walk_rendered_block_for_mutation(
    b: &crate::ir::Block,
    program: Option<&Program>,
    transitive_set: Option<&std::collections::BTreeSet<crate::ir::FunId>>,
    mode: RenderedBlockMode,
) -> bool {
    for s in &b.stmts {
        if mode == RenderedBlockMode::InnerValue && is_erased_inner_discard(s) {
            continue;
        }
        if walk_rendered_stmt_for_mutation(s, program, transitive_set) {
            return true;
        }
    }
    match &b.tail {
        BlockTail::Value(e) if mode == RenderedBlockMode::InnerEval => {
            walk_eval_expr_for_mutation(e, program, transitive_set)
        }
        BlockTail::Value(e) => walk_expr_for_mutation(e, program, transitive_set),
        BlockTail::Return(e) if mode != RenderedBlockMode::InnerEval => {
            walk_expr_for_mutation(e, program, transitive_set)
        }
        BlockTail::ReturnFromBlock { value, .. } if mode == RenderedBlockMode::FunctionBody => {
            walk_expr_for_mutation(value, program, transitive_set)
        }
        BlockTail::Return(_)
        | BlockTail::ReturnFromBlock { .. }
        | BlockTail::Abort { .. }
        | BlockTail::Break { .. }
        | BlockTail::Continue { .. } => false,
    }
}

fn walk_rendered_stmt_for_mutation(
    stmt: &Stmt,
    program: Option<&Program>,
    transitive_set: Option<&std::collections::BTreeSet<crate::ir::FunId>>,
) -> bool {
    match stmt {
        Stmt::Let { value, .. } => walk_expr_for_mutation(value, program, transitive_set),
        Stmt::Eval(expr) => walk_eval_expr_for_mutation(expr, program, transitive_set),
    }
}

fn walk_eval_expr_for_mutation(
    expr: &Expr,
    program: Option<&Program>,
    transitive_set: Option<&std::collections::BTreeSet<crate::ir::FunId>>,
) -> bool {
    if let Expr::If {
        cond,
        then_branch,
        else_branch,
    } = expr
    {
        return walk_expr_for_mutation(cond, program, transitive_set)
            || walk_rendered_block_for_mutation(
                then_branch,
                program,
                transitive_set,
                RenderedBlockMode::InnerEval,
            )
            || walk_rendered_block_for_mutation(
                else_branch,
                program,
                transitive_set,
                RenderedBlockMode::InnerEval,
            );
    }
    walk_expr_for_mutation(expr, program, transitive_set)
}

/// True iff `ty` is the `type_name::TypeName` struct.
pub(in crate::render) fn is_type_name_struct(ty: &crate::ir::Type, program: &Program) -> bool {
    if let crate::ir::Type::Struct { struct_id, .. } = ty {
        if let Some(s) = program.structs.get(struct_id) {
            return s.name == "TypeName"
                && program
                    .modules
                    .get(&s.module_id)
                    .map(|m| m.name == "type_name")
                    .unwrap_or(false);
        }
    }
    false
}

fn type_has_mutable_ref(ty: &crate::ir::Type) -> bool {
    use crate::ir::Type;
    match ty {
        Type::MutableRef { .. } => true,
        Type::Tuple(types) => types.iter().any(type_has_mutable_ref),
        Type::Vector(inner) | Type::Reference(inner) => type_has_mutable_ref(inner),
        Type::Struct { type_args, .. } => type_args.iter().any(type_has_mutable_ref),
        Type::Unit
        | Type::Bool
        | Type::Prop
        | Type::UInt(_)
        | Type::Address
        | Type::TypeParam(_) => false,
    }
}

pub(in crate::render) fn signature_has_mutable_ref(sig: &crate::ir::Signature) -> bool {
    signature_has_mutable_param(sig) || type_has_mutable_ref(&sig.return_type)
}

pub(in crate::render) fn signature_has_mutable_param(sig: &crate::ir::Signature) -> bool {
    sig.params
        .iter()
        .any(|param| type_has_mutable_ref(&param.ty))
}

pub(in crate::render) fn walk_expr_for_mutation(
    e: &Expr,
    program: Option<&Program>,
    transitive_set: Option<&std::collections::BTreeSet<crate::ir::FunId>>,
) -> bool {
    use crate::ir::{BitOp, BorrowNode, QuantDomain};
    match e {
        Expr::Borrow { .. } => true,
        Expr::Update { step, base, value } => {
            step.exprs()
                .any(|__pe| walk_expr_for_mutation(__pe, program, transitive_set))
                || walk_expr_for_mutation(base, program, transitive_set)
                || walk_expr_for_mutation(value, program, transitive_set)
        }
        Expr::IsParent { .. } | Expr::WriteRef { .. } => true,
        Expr::WriteBack { node, .. } => {
            matches!(node, BorrowNode::Reference(_) | BorrowNode::GlobalRoot(_))
        }
        Expr::BorrowGlobal(_) => true,
        Expr::Var(_) | Expr::Const(_) | Expr::Unit | Expr::BorrowLoc(_) => false,
        Expr::ReadRef(v)
        | Expr::Unpack { value: v, .. }
        | Expr::Field { base: v, .. }
        | Expr::ToProp(v)
        | Expr::ToBool(v)
        | Expr::UnOp { operand: v, .. } => walk_expr_for_mutation(v, program, transitive_set),
        Expr::BinOp { lhs, rhs, .. } => {
            walk_expr_for_mutation(lhs, program, transitive_set)
                || walk_expr_for_mutation(rhs, program, transitive_set)
        }
        Expr::BitOp(op) => match op {
            BitOp::Extract { operand, .. }
            | BitOp::ZeroExtend { operand, .. }
            | BitOp::SignExtend { operand, .. } => {
                walk_expr_for_mutation(operand, program, transitive_set)
            }
            BitOp::Concat { high, low } => {
                walk_expr_for_mutation(high, program, transitive_set)
                    || walk_expr_for_mutation(low, program, transitive_set)
            }
        },
        Expr::Call { fun, args, .. } => {
            if let Some(p) = program {
                if let Some(callee) = p.lookup_callee(*fun) {
                    // Native callees don't trigger Mutation emission
                    // at their call sites: the renderer strips
                    // `MutableRef` from native param types (since
                    // hand-written natives take value-form) and the
                    // `Mutation.ofLocal` wrap only fires for
                    // non-native callees with MutableRef params.
                    // Only check user (translated) callees.
                    if !callee.is_native() {
                        if signature_has_mutable_ref(callee.signature()) {
                            return true;
                        }
                        // Transitive: callee's body uses Mutation.
                        if let Some(ts) = transitive_set {
                            if ts.contains(fun) {
                                return true;
                            }
                        }
                    }
                }
            }
            args.iter()
                .any(|a| walk_expr_for_mutation(a, program, transitive_set))
        }
        Expr::Tuple(es) | Expr::Pack { fields: es, .. } => es
            .iter()
            .any(|x| walk_expr_for_mutation(x, program, transitive_set)),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            walk_expr_for_mutation(cond, program, transitive_set)
                || walk_rendered_block_for_mutation(
                    then_branch,
                    program,
                    transitive_set,
                    RenderedBlockMode::InnerValue,
                )
                || walk_rendered_block_for_mutation(
                    else_branch,
                    program,
                    transitive_set,
                    RenderedBlockMode::InnerValue,
                )
        }
        Expr::Match {
            selector, cases, ..
        } => {
            walk_expr_for_mutation(selector, program, transitive_set)
                || cases.iter().any(|c| {
                    walk_rendered_block_for_mutation(
                        &c.body,
                        program,
                        transitive_set,
                        RenderedBlockMode::InnerValue,
                    )
                })
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            header_exit_locals: _,
            live_out: _,
        } => {
            iter_locals
                .iter()
                .any(|(_, init)| walk_expr_for_mutation(init, program, transitive_set))
                || walk_rendered_block_for_mutation(
                    header,
                    program,
                    transitive_set,
                    RenderedBlockMode::InnerValue,
                )
                || walk_expr_for_mutation(cond, program, transitive_set)
                || walk_rendered_block_for_mutation(
                    body,
                    program,
                    transitive_set,
                    RenderedBlockMode::InnerValue,
                )
        }
        Expr::Quantifier { domain, body, .. } => {
            let d = match domain {
                QuantDomain::Unbounded => false,
                QuantDomain::Range { start, end } => {
                    walk_expr_for_mutation(start, program, transitive_set)
                        || walk_expr_for_mutation(end, program, transitive_set)
                }
                QuantDomain::VecRange { vec, start, end } => {
                    walk_expr_for_mutation(vec, program, transitive_set)
                        || walk_expr_for_mutation(start, program, transitive_set)
                        || walk_expr_for_mutation(end, program, transitive_set)
                }
                QuantDomain::Collection(c) => walk_expr_for_mutation(c, program, transitive_set),
            };
            d || walk_rendered_block_for_mutation(
                body,
                program,
                transitive_set,
                RenderedBlockMode::InnerValue,
            )
        }
        Expr::LabeledBlock { .. } => {
            unreachable!("Expr::LabeledBlock should be eliminated by stage 7 helper extraction")
        }
    }
}
