//! Stage 4w -- in-stage WriteBack lowering
//! (`plans/lean-pipeline/writeback-lowering.md`). Runs after stage 4
//! (effects -- `world: Some` markers must be final) and AFTER stage 5
//! (SSA): the lowering clones borrow-site operand expressions (vec
//! indices, map keys) into the writeback position, which is only
//! sound under single-assignment names. Pre-SSA, a loop counter is a
//! rebound name -- the clone would re-resolve to the post-increment
//! version at the writeback site (off-by-one element writes).
//!
//! Scope: field-edge class (S2) + vec/map LEAF edges with statically
//! traceable operands (S3).
//!
//! Rewrites `Stmt::Let { [p2], WriteBack { node, edge, child, world:
//! None } }` where `edge` flattens to Direct/StructField steps only
//! AND the field chain TYPE-CHECKS against the child:
//!
//! - `LocalRoot(p)`: the parent IS the underlying value -- rebuild it
//!   as a value-form `Update{Field}` chain (`path_to_update`).
//! - `Reference(p)`: the parent is a Mutation -- emit the WriteRef
//!   bridge `WriteRef { p, <update chain over ReadRef(p)> }`, which
//!   renders as `Mutation.set p { p.val with .. }` and so preserves
//!   the wrapper (and its runtime borrow path) for escaping refs.
//!
//! The TYPE GATE is load-bearing: skip_list-class writebacks carry a
//! Direct/StructField-looking edge while the parent/child types
//! disagree (parent `Table<K, Node>` vs child `Node`) -- the legacy
//! renderer bridges those through the native-map machinery
//! (`try_render_native_map_writeback` keyed on `borrow_sources`).
//! Walking the chain through the parent's (substituted) field types
//! and requiring an exact match with the child's type keeps exactly
//! the bridge class on the legacy path (S3 territory).
//!
//! Also NOT lowered here: vec/map edges (runtime operands), EnumField
//! (match-based update), `world: Some` (World-routed df hypers), and
//! `SpecGlobalRoot` ghost writebacks.

use std::collections::BTreeMap;

use crate::ir::analysis::type_of::{substitute_type_params, type_of};
use crate::ir::borrow::{BorrowEdge, BorrowNode};
use crate::ir::path::PathStep;
use crate::ir::quant::QuantDomain;
use crate::ir::{Block, BlockTail, Expr, Program, Stmt, Type, VarId};

type Scope = BTreeMap<VarId, Type>;

/// Per-function walk state. (The historical isParent-arm guard was
/// removed 2026-06-12: it existed to keep the byte-exact render text
/// patches matching, and those were deleted once
/// `stage_05_chain_complete` made the coalescing chains real IR --
/// writebacks under IsParent merges now lower like any other.)
struct WalkState {
    scope: Scope,
    /// `v -> (step, base_var)` for Let-bound `Borrow { step, base:
    /// Var(b) }` defs. The child of a vec/map writeback traces back
    /// to the parent through this map; the steps carry the runtime
    /// operands (index / key exprs) the lowering needs -- the
    /// PathStep cutover made the borrow chain itself the source of
    /// truth (no render-side rediscovery).
    borrow_defs: BTreeMap<VarId, (PathStep, VarId)>,
}

impl WalkState {
    fn fork(&self) -> WalkState {
        WalkState {
            scope: self.scope.clone(),
            borrow_defs: self.borrow_defs.clone(),
        }
    }
}

/// Stage entry point.
/// Record `v`'s borrow provenance from its Let value. Direct
/// `Borrow` defs carry (step, base); rebinds (WriteRef bridge,
/// surviving WriteBack, lowered Update spines) inherit; an SSA
/// phi-`If`/`Match` whose every arm tail resolves to the SAME
/// source inherits it too (the stage-side mirror of
/// `collect_borrow_sources`' common-source propagation).
fn record_def(v: &VarId, value: &Expr, st: &mut WalkState, program: &Program) {
    match value {
        Expr::Borrow { step, base } => {
            if let Expr::Var(b) = base.as_ref() {
                st.borrow_defs.insert(v.clone(), (step.clone(), b.clone()));
            }
        }
        Expr::WriteRef { reference, .. } => {
            if let Expr::Var(r) = reference.as_ref() {
                if let Some(d) = st.borrow_defs.get(r).cloned() {
                    st.borrow_defs.insert(v.clone(), d);
                }
            }
        }
        Expr::WriteBack { node, .. } => {
            if let BorrowNode::Reference(r) | BorrowNode::LocalRoot(r) = node {
                if let Some(d) = st.borrow_defs.get(r).cloned() {
                    st.borrow_defs.insert(v.clone(), d);
                }
            }
        }
        Expr::Update { base, .. } => {
            let mut root = base.as_ref();
            while let Expr::Update { base, .. } | Expr::ReadRef(base) = root {
                root = base.as_ref();
            }
            if let Expr::Var(r) = root {
                if let Some(d) = st.borrow_defs.get(r).cloned() {
                    st.borrow_defs.insert(v.clone(), d);
                }
            }
        }
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => {
            let a = block_tail_source(then_branch, st, program);
            let b = block_tail_source(else_branch, st, program);
            if let (Some(a), Some(b)) = (a, b) {
                if a == b {
                    st.borrow_defs.insert(v.clone(), a);
                }
            }
        }
        Expr::Match { cases, .. } => {
            let mut common: Option<(PathStep, VarId)> = None;
            for arm in cases {
                match (block_tail_source(&arm.body, st, program), &common) {
                    (Some(src), None) => common = Some(src),
                    (Some(src), Some(c)) if &src == c => {}
                    _ => return,
                }
            }
            if let Some(src) = common {
                st.borrow_defs.insert(v.clone(), src);
            }
        }
        _ => {}
    }
}

/// Multi-binder augmented-call rebind: stage 3/4 turn
/// `f(&mut a, ..)` into `let (orig.., a2.., world?) = f(a, ..)` --
/// the trailing slots (before a world slot) rebind the `&mut` arg
/// vars IN PARAM ORDER. Inherit each arg's borrow source onto its
/// rebound version (the stage-side mirror of the render's
/// `borrow_mut_derivatives`).
fn record_call_derivatives(
    pattern: &[Option<VarId>],
    value: &Expr,
    st: &mut WalkState,
    program: &Program,
) {
    let Expr::Call { fun, args, .. } = value else {
        return;
    };
    let Some(callee) = program.functions.get(fun) else {
        return;
    };
    let mut slots = pattern.len();
    if callee
        .signature
        .params
        .last()
        .is_some_and(|p| p.var == crate::stage_04_effects::common::world_varid())
    {
        slots = slots.saturating_sub(1);
    }
    let mut mutref_args: Vec<&Expr> = Vec::new();
    for (i, prm) in callee.signature.params.iter().enumerate() {
        if matches!(prm.ty, Type::MutableRef { .. }) {
            if let Some(a) = args.get(i) {
                mutref_args.push(a);
            }
        }
    }
    if mutref_args.is_empty() || mutref_args.len() > slots {
        return;
    }
    let start = slots - mutref_args.len();
    for (k, arg) in mutref_args.iter().enumerate() {
        let Some(Some(v)) = pattern.get(start + k) else {
            continue;
        };
        let Expr::Var(a) = arg else {
            continue;
        };
        if let Some(d) = st.borrow_defs.get(a).cloned() {
            st.borrow_defs.insert(v.clone(), d);
        }
    }
}

/// Resolve a block's `Value(Var(x))` tail to a borrow source,
/// replaying the block's own defs over a local overlay (nested
/// phi-Ifs recurse through `record_def`).
fn block_tail_source(b: &Block, st: &WalkState, program: &Program) -> Option<(PathStep, VarId)> {
    let mut local = st.fork();
    for s in &b.stmts {
        if let Stmt::Let { pattern, value } = s {
            if let [Some(v)] = pattern.as_slice() {
                record_def(v, value, &mut local, program);
            } else if pattern.len() > 1 {
                record_call_derivatives(pattern, value, &mut local, program);
            }
        }
    }
    match &b.tail {
        BlockTail::Value(Expr::Var(x)) => local.borrow_defs.get(x).cloned(),
        _ => None,
    }
}

pub fn run(program: &mut Program) {
    lower_field_writebacks(program);
}

fn lower_field_writebacks(program: &mut Program) {
    let fids: Vec<_> = program.functions.keys().copied().collect();
    for fid in fids {
        let f = program.functions.get_mut(&fid).expect("fid present");
        let mut st = WalkState {
            scope: f
                .signature
                .params
                .iter()
                .map(|p| (p.var.clone(), p.ty.clone()))
                .collect(),
            borrow_defs: Default::default(),
        };
        let mut body = std::mem::replace(
            &mut f.body,
            Block {
                stmts: Vec::new(),
                tail: BlockTail::Value(Expr::Unit),
            },
        );
        lower_block(&mut body, &mut st, program);
        program.functions.get_mut(&fid).expect("fid present").body = body;
    }
}

fn lower_block(b: &mut Block, st: &mut WalkState, program: &Program) {
    for s in b.stmts.iter_mut() {
        match s {
            Stmt::Let { pattern, value } => {
                lower_expr_blocks(value, st, program);
                try_lower_stmt_value(pattern, value, st, program);
                if let [Some(v)] = pattern.as_slice() {
                    record_def(v, value, st, program);
                } else if pattern.len() > 1 {
                    record_call_derivatives(pattern, value, st, program);
                }
                // Extend scope AFTER the rewrite; the lowered form has
                // the same type by construction, and `type_of` knows
                // the lowered shapes better than `WriteBack`.
                if let Ok(ty) = type_of(value, &st.scope, program) {
                    extend_scope(pattern, ty, &mut st.scope);
                }
            }
            Stmt::Eval(e) => lower_expr_blocks(e, st, program),
        }
    }
    lower_tail(&mut b.tail, st, program);
}

fn lower_tail(t: &mut BlockTail, st: &mut WalkState, program: &Program) {
    match t {
        BlockTail::Value(e) => lower_expr_blocks(e, st, program),
        BlockTail::Return(e) => lower_expr_blocks(e, st, program),
        BlockTail::Abort { code } => lower_expr_blocks(code, st, program),
        BlockTail::ReturnFromBlock { value, .. } => lower_expr_blocks(value, st, program),
        BlockTail::Break { value, .. } | BlockTail::Continue { value, .. } => {
            lower_expr_blocks(value, st, program)
        }
    }
}

fn lower_expr_blocks(e: &mut Expr, st: &WalkState, program: &Program) {
    match e {
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            lower_expr_blocks(cond, st, program);
            lower_block(then_branch, &mut st.fork(), program);
            lower_block(else_branch, &mut st.fork(), program);
        }
        Expr::Match {
            selector, cases, ..
        } => {
            lower_expr_blocks(selector, st, program);
            for arm in cases {
                let mut arm_st = st.fork();
                for bnd in &arm.bindings {
                    arm_st.scope.insert(bnd.clone(), Type::Unit);
                }
                lower_block(&mut arm.body, &mut arm_st, program);
            }
        }
        Expr::While {
            header,
            cond,
            body,
            iter_locals,
            ..
        } => {
            let mut s = st.fork();
            for (binder, init) in iter_locals.iter_mut() {
                lower_expr_blocks(init, &s, program);
                if let Ok(ty) = type_of(init, &s.scope, program) {
                    s.scope.insert(binder.clone(), ty);
                }
            }
            lower_block(header, &mut s.fork(), program);
            lower_expr_blocks(cond, &s, program);
            lower_block(body, &mut s, program);
        }
        Expr::Quantifier {
            binder,
            binder_type,
            domain,
            body,
            ..
        } => {
            match domain {
                QuantDomain::Unbounded => {}
                QuantDomain::Range { start, end } => {
                    lower_expr_blocks(start, st, program);
                    lower_expr_blocks(end, st, program);
                }
                QuantDomain::Collection(c) => lower_expr_blocks(c, st, program),
                QuantDomain::VecRange { vec, start, end } => {
                    lower_expr_blocks(vec, st, program);
                    lower_expr_blocks(start, st, program);
                    lower_expr_blocks(end, st, program);
                }
            }
            let mut s = st.fork();
            s.scope.insert(binder.clone(), binder_type.clone());
            lower_block(body, &mut s, program);
        }
        Expr::LabeledBlock { body, .. } => lower_block(body, &mut st.fork(), program),
        // Everything else: no nested Blocks that can hold writeback
        // Lets (Call args etc. are expressions; stage-3 hoisted any
        // statement-position writebacks into Lets already).
        _ => {}
    }
}

fn try_lower_stmt_value(
    pattern: &[Option<VarId>],
    value: &mut Expr,
    st: &WalkState,
    program: &Program,
) {
    if pattern.len() != 1 {
        return;
    }
    let replacement = {
        let Expr::WriteBack {
            node,
            edge,
            child,
            world: None,
        } = &*value
        else {
            return;
        };
        let Some(chain) = lowerable_chain(edge) else {
            return;
        };
        let (parent, is_reference) = match node {
            BorrowNode::LocalRoot(p) => (p, false),
            BorrowNode::Reference(p) => (p, true),
            BorrowNode::GlobalRoot(global) => {
                unreachable!("GlobalRoot({global}) passed the thread_globals/stage-3 boundary")
            }
            BorrowNode::SpecGlobalRoot { .. } => return,
        };
        let Some(parent_ty) = st.scope.get(parent).map(strip_mut) else {
            return;
        };
        let Some(child_ty) = st.scope.get(child).map(strip_mut) else {
            return;
        };
        // Recover the operand-carrying steps. Empty chain (Direct
        // writeback) needs none. Non-empty chains must trace the
        // child's Borrow-def spine back to the parent and MATCH the
        // edge chain -- a broken trace (param child, call rebind,
        // If-merged borrow) is the writeBack*Auto path-recovery
        // class and stays on the legacy render path.
        let all_fields = chain
            .iter()
            .all(|e| matches!(e, BorrowEdge::StructField { .. }));
        let steps: Vec<PathStep> = if chain.is_empty() {
            Vec::new()
        } else if all_fields {
            // Field-only chains carry no runtime operands -- build the
            // steps straight from the edges (S2 behavior; the child
            // need not have a visible Borrow def).
            chain
                .iter()
                .map(|e| {
                    let BorrowEdge::StructField {
                        struct_id,
                        field_index,
                    } = e
                    else {
                        unreachable!("all_fields checked")
                    };
                    PathStep::Field {
                        struct_id: *struct_id,
                        field_index: *field_index,
                    }
                })
                .collect()
        } else {
            let Some(steps) = trace_child_steps(child, parent, st) else {
                return;
            };
            if steps.len() != chain.len()
                || steps
                    .iter()
                    .zip(&chain)
                    .any(|(s, e)| !step_matches_edge(s, e))
            {
                return;
            }
            // vec/map steps only as the LEAF: interior vec/map would
            // need value-form element reads (native-call composition)
            // -- not this slice's class.
            if steps[..steps.len() - 1]
                .iter()
                .any(|s| !matches!(s, PathStep::Field { .. }))
            {
                return;
            }
            if steps.iter().any(|s| {
                matches!(
                    s,
                    PathStep::MapKey {
                        df_value: Some(_),
                        ..
                    } | PathStep::VariantField { .. }
                )
            }) {
                return;
            }
            steps
        };
        // TYPE GATE (generalized): the steps applied to the parent's
        // inner type must land exactly on the child's inner type, and
        // a MapKey leaf must target a supported native map.
        let Some(target_ty) = walk_steps_type(&parent_ty, &steps, program) else {
            return;
        };
        if target_ty != child_ty {
            return;
        }
        let child_val = Expr::ReadRef(Box::new(Expr::Var(child.clone())));
        if is_reference {
            let updated = steps_to_update(
                Expr::ReadRef(Box::new(Expr::Var(parent.clone()))),
                &steps,
                child_val,
            );
            Expr::WriteRef {
                reference: Box::new(Expr::Var(parent.clone())),
                value: Box::new(updated),
            }
        } else {
            steps_to_update(Expr::Var(parent.clone()), &steps, child_val)
        }
    };
    *value = replacement;
}

/// Trace `child`'s Borrow-def spine up to `parent`, returning the
/// steps ROOT-FIRST. `None` when the spine is broken or doesn't
/// reach the parent within a sane depth.
fn trace_child_steps(child: &VarId, parent: &VarId, st: &WalkState) -> Option<Vec<PathStep>> {
    let mut rev: Vec<PathStep> = Vec::new();
    let mut cur = child.clone();
    for _ in 0..32 {
        let (step, base) = st.borrow_defs.get(&cur)?;
        rev.push(step.clone());
        if base == parent {
            rev.reverse();
            return Some(rev);
        }
        cur = base.clone();
    }
    None
}

fn step_matches_edge(s: &PathStep, e: &BorrowEdge) -> bool {
    match (s, e) {
        (
            PathStep::Field {
                struct_id: ss,
                field_index: sf,
            },
            BorrowEdge::StructField {
                struct_id: es,
                field_index: ef,
            },
        ) => ss == es && sf == ef,
        (PathStep::VecIndex(_), BorrowEdge::VecIndex) => true,
        (PathStep::MapKey { .. }, BorrowEdge::MapKey { .. }) => true,
        _ => false,
    }
}

/// Build the nested value-form update for ROOT-FIRST `steps`.
/// Interior steps are guaranteed Field (checked by the caller); the
/// intermediate container reads are plain `Expr::Field` projections.
fn steps_to_update(base: Expr, steps: &[PathStep], inner: Expr) -> Expr {
    match steps.split_first() {
        None => inner,
        Some((step, rest)) => {
            if rest.is_empty() {
                Expr::Update {
                    step: step.clone(),
                    base: Box::new(base),
                    value: Box::new(inner),
                }
            } else {
                let PathStep::Field {
                    struct_id,
                    field_index,
                } = step
                else {
                    unreachable!("interior steps are Field (caller-checked)")
                };
                let read = Expr::Field {
                    struct_id: *struct_id,
                    field_index: *field_index,
                    base: Box::new(base.clone()),
                };
                Expr::Update {
                    step: step.clone(),
                    base: Box::new(base),
                    value: Box::new(steps_to_update(read, rest, inner)),
                }
            }
        }
    }
}

/// Sui native maps with an in-value `set` primitive -- mirrors the
/// render arm's `native_map_set_for` dispatch (object_bag excluded:
/// no `set` native).
fn is_supported_native_map(ty: &Type, program: &Program) -> bool {
    let Type::Struct { struct_id, .. } = ty else {
        return false;
    };
    let Some(s) = program.structs.get(struct_id) else {
        return false;
    };
    let Some(m) = program.modules.get(&s.module_id) else {
        return false;
    };
    if m.package_name != "Sui" {
        return false;
    }
    matches!(
        (m.name.as_str(), s.name.as_str()),
        ("table", "Table")
            | ("vec_map", "VecMap")
            | ("object_table", "ObjectTable")
            | ("bag", "Bag")
    )
}

/// Follow ROOT-FIRST steps through (substituted) types. Field walks
/// the struct field; a VecIndex leaf yields the element type; a
/// MapKey leaf requires a supported native map and yields the step's
/// value type (Bag has no V type-arg; the borrow-recorded V is the
/// contract, same as the legacy native `.set` path).
fn walk_steps_type(start: &Type, steps: &[PathStep], program: &Program) -> Option<Type> {
    let mut cur = start.clone();
    for step in steps {
        match step {
            PathStep::Field {
                struct_id,
                field_index,
            } => {
                let Type::Struct {
                    struct_id: cur_sid,
                    type_args,
                } = &cur
                else {
                    return None;
                };
                if cur_sid != struct_id {
                    return None;
                }
                let s = program.structs.get(struct_id)?;
                let f = s.fields.get(*field_index)?;
                cur = substitute_type_params(&f.field_type, type_args);
            }
            PathStep::VecIndex(_) => {
                let Type::Vector(elem) = &cur else {
                    return None;
                };
                cur = (**elem).clone();
            }
            PathStep::MapKey { value_type, .. } => {
                if !is_supported_native_map(&cur, program) {
                    return None;
                }
                cur = value_type.clone();
            }
            PathStep::VariantField { .. } => return None,
        }
    }
    Some(cur)
}

fn strip_mut(t: &Type) -> Type {
    match t {
        Type::MutableRef { inner, .. } => (**inner).clone(),
        Type::Reference(inner) => (**inner).clone(),
        other => other.clone(),
    }
}

fn extend_scope(pattern: &[Option<VarId>], ty: Type, scope: &mut Scope) {
    if pattern.len() == 1 {
        if let Some(v) = &pattern[0] {
            scope.insert(v.clone(), ty);
        }
        return;
    }
    let elems = match ty {
        Type::Tuple(es) if es.len() == pattern.len() => es,
        _ => return,
    };
    for (slot, elem_ty) in pattern.iter().zip(elems.into_iter()) {
        if let Some(v) = slot {
            scope.insert(v.clone(), elem_ty);
        }
    }
}

/// Flatten `edge` into a root-first chain of lowerable edges
/// (StructField / VecIndex / MapKey; Direct dropped; Hyper
/// flattened). `None` when EnumField appears -- enum updates are
/// match-based and stay on the legacy path.
fn lowerable_chain(edge: &BorrowEdge) -> Option<Vec<BorrowEdge>> {
    fn push(e: &BorrowEdge, out: &mut Vec<BorrowEdge>) -> bool {
        match e {
            BorrowEdge::Direct => true,
            BorrowEdge::StructField { .. } | BorrowEdge::VecIndex | BorrowEdge::MapKey { .. } => {
                out.push(e.clone());
                true
            }
            BorrowEdge::Hyper(es) => es.iter().all(|x| push(x, out)),
            BorrowEdge::EnumField { .. } => false,
        }
    }
    let mut out = Vec::new();
    push(edge, &mut out).then_some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Field, Function, FunctionKind, Module, Param, Signature, Struct};

    fn test_program() -> Program {
        let mut p = Program::default();
        p.modules.insert(
            0,
            Module {
                name: "m".to_string(),
                package_name: "p".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
        p.modules.insert(
            1,
            Module {
                name: "table".to_string(),
                package_name: "Sui".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: true,
            },
        );
        p.modules.insert(
            2,
            Module {
                name: "object_bag".to_string(),
                package_name: "Sui".to_string(),
                address: String::new(),
                required_imports: Vec::new(),
                is_native: true,
            },
        );
        p.structs.insert(
            8,
            Struct {
                module_id: 1,
                name: "Table".to_string(),
                qualified_name: "sui::table::Table".to_string(),
                type_params: vec!["K".to_string(), "V".to_string()],
                fields: vec![],
                variants: None,
                is_native: true,
            },
        );
        p.structs.insert(
            9,
            Struct {
                module_id: 2,
                name: "ObjectBag".to_string(),
                qualified_name: "sui::object_bag::ObjectBag".to_string(),
                type_params: vec![],
                fields: vec![],
                variants: None,
                is_native: true,
            },
        );
        p.structs.insert(
            7,
            Struct {
                module_id: 0,
                name: "S".to_string(),
                qualified_name: "p::m::S".to_string(),
                type_params: vec![],
                fields: vec![
                    Field {
                        name: "a".to_string(),
                        field_type: Type::UInt(64),
                    },
                    Field {
                        name: "b".to_string(),
                        field_type: Type::UInt(8),
                    },
                    Field {
                        name: "items".to_string(),
                        field_type: Type::Vector(Box::new(Type::UInt(8))),
                    },
                ],
                variants: None,
                is_native: false,
            },
        );
        p
    }

    fn s_ty() -> Type {
        Type::Struct {
            struct_id: 7,
            type_args: vec![],
        }
    }

    fn mutref(inner: Type) -> Type {
        Type::MutableRef {
            inner: Box::new(inner.clone()),
            root: Box::new(inner),
        }
    }

    fn wb_fn(prog: &mut Program, node: BorrowNode, edge: BorrowEdge, child_ty: Type) {
        let f = Function {
            module: 0,
            name: "f".to_string(),
            signature: Signature {
                type_params: vec![],
                params: vec![
                    Param {
                        name: "p".to_string(),
                        var: VarId::from("p"),
                        ty: match &node {
                            BorrowNode::Reference(_) => mutref(s_ty()),
                            _ => s_ty(),
                        },
                    },
                    Param {
                        name: "c".to_string(),
                        var: VarId::from("c"),
                        ty: child_ty,
                    },
                ],
                return_type: Type::Unit,
            },
            body: Block {
                stmts: vec![Stmt::Let {
                    pattern: vec![Some(VarId::from("p2"))],
                    value: Expr::WriteBack {
                        node,
                        edge,
                        child: VarId::from("c"),
                        world: None,
                    },
                }],
                tail: BlockTail::Value(Expr::Unit),
            },
            kind: FunctionKind::Source,
            effects: crate::ir::Effects::CONSERVATIVE,
            explicit_pure: false,
        };
        prog.functions.insert(0, f);
    }

    fn lowered_value(prog: &mut Program) -> Expr {
        lower_field_writebacks(prog);
        let Stmt::Let { value, .. } = &prog.functions[&0].body.stmts[0] else {
            panic!("not a let")
        };
        value.clone()
    }

    #[test]
    fn reference_field_writeback_lowers_to_writeref_update() {
        let mut prog = test_program();
        wb_fn(
            &mut prog,
            BorrowNode::Reference(VarId::from("p")),
            BorrowEdge::StructField {
                struct_id: 7,
                field_index: 1,
            },
            mutref(Type::UInt(8)),
        );
        let value = lowered_value(&mut prog);
        let Expr::WriteRef { reference, value } = value else {
            panic!("expected WriteRef bridge, got {value:?}")
        };
        assert!(matches!(*reference, Expr::Var(ref v) if v.as_ref() == "p"));
        assert!(matches!(
            &*value,
            Expr::Update {
                step: crate::ir::path::PathStep::Field {
                    struct_id: 7,
                    field_index: 1
                },
                ..
            }
        ));
    }

    #[test]
    fn localroot_direct_writeback_lowers_to_readref() {
        let mut prog = test_program();
        wb_fn(
            &mut prog,
            BorrowNode::LocalRoot(VarId::from("p")),
            BorrowEdge::Direct,
            mutref(s_ty()),
        );
        let value = lowered_value(&mut prog);
        assert!(matches!(value, Expr::ReadRef(_)), "got {value:?}");
    }

    #[test]
    fn type_mismatched_field_writeback_is_left_alone() {
        let mut prog = test_program();
        // Child claims to be the WHOLE struct while the edge points at
        // field 1 (u8) -- the skip_list bridge shape. Must NOT lower.
        wb_fn(
            &mut prog,
            BorrowNode::Reference(VarId::from("p")),
            BorrowEdge::StructField {
                struct_id: 7,
                field_index: 1,
            },
            mutref(s_ty()),
        );
        let value = lowered_value(&mut prog);
        assert!(matches!(value, Expr::WriteBack { .. }), "got {value:?}");
    }

    #[test]
    fn mapkey_edge_is_not_lowered_in_s2() {
        let mut prog = test_program();
        wb_fn(
            &mut prog,
            BorrowNode::Reference(VarId::from("p")),
            BorrowEdge::MapKey {
                key_type: Type::UInt(64),
                value_type: Type::UInt(8),
            },
            mutref(Type::UInt(8)),
        );
        let value = lowered_value(&mut prog);
        assert!(matches!(value, Expr::WriteBack { .. }));
    }

    fn wb_fn_with_stmts(
        prog: &mut Program,
        params: Vec<Param>,
        stmts: Vec<Stmt>,
        node: BorrowNode,
        edge: BorrowEdge,
    ) {
        let mut all = stmts;
        all.push(Stmt::Let {
            pattern: vec![Some(VarId::from("p2"))],
            value: Expr::WriteBack {
                node,
                edge,
                child: VarId::from("c"),
                world: None,
            },
        });
        let f = Function {
            module: 0,
            name: "f".to_string(),
            signature: Signature {
                type_params: vec![],
                params,
                return_type: Type::Unit,
            },
            body: Block {
                stmts: all,
                tail: BlockTail::Value(Expr::Unit),
            },
            kind: FunctionKind::Source,
            effects: crate::ir::Effects::CONSERVATIVE,
            explicit_pure: false,
        };
        prog.functions.insert(0, f);
    }

    fn pparam(name: &str, ty: Type) -> Param {
        Param {
            name: name.to_string(),
            var: VarId::from(name),
            ty,
        }
    }

    fn borrow_let(v: &str, step: PathStep, base: &str) -> Stmt {
        Stmt::Let {
            pattern: vec![Some(VarId::from(v))],
            value: Expr::Borrow {
                step,
                base: Box::new(Expr::Var(VarId::from(base))),
            },
        }
    }

    fn lowered_wb_value(prog: &mut Program) -> Expr {
        lower_field_writebacks(prog);
        let Stmt::Let { value, .. } = prog.functions[&0].body.stmts.last().unwrap() else {
            panic!("not a let")
        };
        value.clone()
    }

    #[test]
    fn vec_leaf_writeback_lowers_with_traced_index() {
        let mut prog = test_program();
        let vec_ty = Type::Vector(Box::new(Type::UInt(8)));
        wb_fn_with_stmts(
            &mut prog,
            vec![pparam("p", mutref(vec_ty)), pparam("i", Type::UInt(64))],
            vec![borrow_let(
                "c",
                PathStep::VecIndex(Box::new(Expr::Var(VarId::from("i")))),
                "p",
            )],
            BorrowNode::Reference(VarId::from("p")),
            BorrowEdge::VecIndex,
        );
        let v = lowered_wb_value(&mut prog);
        let Expr::WriteRef { value, .. } = v else {
            panic!("expected WriteRef, got {v:?}")
        };
        assert!(
            matches!(&*value, Expr::Update { step: PathStep::VecIndex(i), .. }
            if matches!(&**i, Expr::Var(n) if n.as_ref() == "i"))
        );
    }

    #[test]
    fn hyper_field_then_vec_lowers_to_nested_update() {
        let mut prog = test_program();
        wb_fn_with_stmts(
            &mut prog,
            vec![pparam("p", mutref(s_ty())), pparam("i", Type::UInt(64))],
            vec![
                borrow_let(
                    "m",
                    PathStep::Field {
                        struct_id: 7,
                        field_index: 2,
                    },
                    "p",
                ),
                borrow_let(
                    "c",
                    PathStep::VecIndex(Box::new(Expr::Var(VarId::from("i")))),
                    "m",
                ),
            ],
            BorrowNode::Reference(VarId::from("p")),
            BorrowEdge::Hyper(vec![
                BorrowEdge::StructField {
                    struct_id: 7,
                    field_index: 2,
                },
                BorrowEdge::VecIndex,
            ]),
        );
        let v = lowered_wb_value(&mut prog);
        let Expr::WriteRef { value, .. } = v else {
            panic!("expected WriteRef, got {v:?}")
        };
        let Expr::Update {
            step: PathStep::Field { field_index: 2, .. },
            value: inner,
            ..
        } = &*value
        else {
            panic!("expected outer Field update, got {value:?}")
        };
        assert!(
            matches!(&**inner, Expr::Update { step: PathStep::VecIndex(_), base, .. }
            if matches!(&**base, Expr::Field { field_index: 2, .. }))
        );
    }

    #[test]
    fn map_leaf_on_table_lowers_to_update_mapkey() {
        let mut prog = test_program();
        let table_ty = Type::Struct {
            struct_id: 8,
            type_args: vec![Type::UInt(64), Type::UInt(8)],
        };
        wb_fn_with_stmts(
            &mut prog,
            vec![pparam("p", mutref(table_ty)), pparam("k", Type::UInt(64))],
            vec![borrow_let(
                "c",
                PathStep::MapKey {
                    key: Box::new(Expr::Var(VarId::from("k"))),
                    key_type: Type::UInt(64),
                    value_type: Type::UInt(8),
                    df_value: None,
                },
                "p",
            )],
            BorrowNode::Reference(VarId::from("p")),
            BorrowEdge::MapKey {
                key_type: Type::UInt(64),
                value_type: Type::UInt(8),
            },
        );
        let v = lowered_wb_value(&mut prog);
        let Expr::WriteRef { value, .. } = v else {
            panic!("expected WriteRef, got {v:?}")
        };
        assert!(matches!(
            &*value,
            Expr::Update {
                step: PathStep::MapKey { .. },
                ..
            }
        ));
    }

    #[test]
    fn object_bag_map_writeback_stays() {
        let mut prog = test_program();
        let bag_ty = Type::Struct {
            struct_id: 9,
            type_args: vec![],
        };
        wb_fn_with_stmts(
            &mut prog,
            vec![pparam("p", mutref(bag_ty)), pparam("k", Type::UInt(64))],
            vec![borrow_let(
                "c",
                PathStep::MapKey {
                    key: Box::new(Expr::Var(VarId::from("k"))),
                    key_type: Type::UInt(64),
                    value_type: Type::UInt(8),
                    df_value: None,
                },
                "p",
            )],
            BorrowNode::Reference(VarId::from("p")),
            BorrowEdge::MapKey {
                key_type: Type::UInt(64),
                value_type: Type::UInt(8),
            },
        );
        let v = lowered_wb_value(&mut prog);
        assert!(matches!(v, Expr::WriteBack { .. }), "got {v:?}");
    }

    #[test]
    fn vec_writeback_without_borrow_def_stays() {
        let mut prog = test_program();
        let vec_ty = Type::Vector(Box::new(Type::UInt(8)));
        wb_fn_with_stmts(
            &mut prog,
            vec![
                pparam("p", mutref(vec_ty)),
                pparam("c", mutref(Type::UInt(8))),
            ],
            vec![],
            BorrowNode::Reference(VarId::from("p")),
            BorrowEdge::VecIndex,
        );
        let v = lowered_wb_value(&mut prog);
        assert!(matches!(v, Expr::WriteBack { .. }), "got {v:?}");
    }

    #[test]
    fn interior_vec_step_stays() {
        let mut prog = test_program();
        let vec_of_s = Type::Vector(Box::new(s_ty()));
        wb_fn_with_stmts(
            &mut prog,
            vec![pparam("p", mutref(vec_of_s)), pparam("i", Type::UInt(64))],
            vec![
                borrow_let(
                    "m",
                    PathStep::VecIndex(Box::new(Expr::Var(VarId::from("i")))),
                    "p",
                ),
                borrow_let(
                    "c",
                    PathStep::Field {
                        struct_id: 7,
                        field_index: 0,
                    },
                    "m",
                ),
            ],
            BorrowNode::Reference(VarId::from("p")),
            BorrowEdge::Hyper(vec![
                BorrowEdge::VecIndex,
                BorrowEdge::StructField {
                    struct_id: 7,
                    field_index: 0,
                },
            ]),
        );
        let v = lowered_wb_value(&mut prog);
        assert!(matches!(v, Expr::WriteBack { .. }), "got {v:?}");
    }
}
