//! Path-sensitive validation of the single threaded `World` value.

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::analysis::type_of::bind_pattern;
use crate::ir::analysis::{substitute_type_params, type_of};
use crate::ir::visit::{walk_expr_default, Visitor};
use crate::ir::{
    BitOp, Block, BlockTail, Expr, FunId, Function, FunctionKind, MatchArm, Program, QuantDomain,
    Stmt, StructId, Type, VarId,
};

use super::common::{
    direct_world_positions, function_lifecycle_world_position, is_world_type,
    lifecycle_world_position, type_carries_world,
};
use crate::ir::names::is_aborts_family_name;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WorldFlowError {
    StaleToken,
    MalformedWriteBack,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Token(u32);

#[derive(Debug, Clone, PartialEq, Eq)]
enum ValueFlow {
    Other,
    World(Option<Token>),
    Tuple(Vec<ValueFlow>),
    Enum {
        struct_id: StructId,
        base: Token,
        variants: BTreeMap<usize, VariantFlow>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct VariantFlow {
    current: Token,
    refinable: bool,
    fields: Vec<ValueFlow>,
}

#[derive(Clone)]
struct FlowState {
    types: BTreeMap<VarId, Type>,
    render_types: BTreeMap<VarId, Type>,
    values: BTreeMap<VarId, ValueFlow>,
    current: Token,
}

#[derive(Clone)]
enum LoopWorld {
    None,
    Slot {
        index: usize,
        arity: usize,
        binder: VarId,
    },
    Implicit(VarId),
}

struct LoopFrame {
    world: LoopWorld,
    breaks: Vec<FlowState>,
}

#[derive(Default)]
struct LabeledFrame {
    exits: Vec<(FlowState, ValueFlow)>,
}

enum BlockFlow {
    Value(FlowState, ValueFlow),
    Terminated,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Executable,
    Snapshot,
}

pub(crate) fn check_function(
    function: &Function,
    program: &Program,
    world_id: StructId,
) -> Result<(), WorldFlowError> {
    let abort_family = is_aborts_family_name(&function.name);
    if matches!(
        &function.kind,
        FunctionKind::Spec {
            kind: crate::ir::SpecKind::Requires
                | crate::ir::SpecKind::Ensures
                | crate::ir::SpecKind::Asserts,
            ..
        } | FunctionKind::Theorem { .. }
            | FunctionKind::Axiom { .. }
    ) {
        return Ok(());
    }

    let world_params: Vec<_> = function
        .signature
        .params
        .iter()
        .enumerate()
        .filter(|(_, param)| is_world_type(&param.ty, world_id))
        .map(|(index, _)| index)
        .collect();
    let world_returns = direct_world_positions(&function.signature.return_type, world_id);
    let returns_world = !world_returns.is_empty();
    if world_params.is_empty()
        || (!abort_family
            && world_params.len() > 1
            && !function.effects.world_writes
            && !returns_world)
    {
        return Ok(());
    }
    if world_returns.len() > 1
        || (!abort_family && function.effects.world_writes && world_returns.is_empty())
    {
        return Err(WorldFlowError::StaleToken);
    }
    let channel_position = function_lifecycle_world_position(function, world_id)
        .expect("a World parameter was found above");
    let channel_var = function.signature.params[channel_position].var.clone();

    let entry = Token(0);
    let mut types = BTreeMap::new();
    let mut values = BTreeMap::new();
    for param in &function.signature.params {
        types.insert(param.var.clone(), param.ty.clone());
        let value = if param.var == channel_var {
            ValueFlow::World(Some(entry))
        } else {
            unknown_for_type(&param.ty, world_id)
        };
        record_value(&mut values, param.var.clone(), value);
    }

    let mut checker = Checker {
        function,
        program,
        world_id,
        world_param: channel_var,
        var_target_types: crate::render::rendered_var_target_types(
            &function.body,
            &function.signature.return_type,
        ),
        next_token: 1,
        loops: Vec::new(),
        labeled_blocks: Vec::new(),
    };
    let state = FlowState {
        render_types: types.clone(),
        types,
        values,
        current: entry,
    };
    match checker.check_block(&function.body, state, Mode::Executable, true)? {
        BlockFlow::Value(_, _) | BlockFlow::Terminated => Ok(()),
    }
}

struct Checker<'a> {
    function: &'a Function,
    program: &'a Program,
    world_id: StructId,
    world_param: VarId,
    var_target_types: BTreeMap<VarId, Type>,
    next_token: u32,
    loops: Vec<LoopFrame>,
    labeled_blocks: Vec<LabeledFrame>,
}

impl Checker<'_> {
    fn fresh_token(&mut self) -> Token {
        let token = Token(self.next_token);
        self.next_token += 1;
        token
    }

    fn check_block(
        &mut self,
        block: &Block,
        state: FlowState,
        mode: Mode,
        function_falloff: bool,
    ) -> Result<BlockFlow, WorldFlowError> {
        self.check_block_with_expected(block, state, mode, function_falloff, None)
    }

    fn check_block_with_expected(
        &mut self,
        block: &Block,
        mut state: FlowState,
        mode: Mode,
        function_falloff: bool,
        expected: Option<&Type>,
    ) -> Result<BlockFlow, WorldFlowError> {
        for stmt in &block.stmts {
            let Some(next) = self.check_stmt(stmt, state, mode)? else {
                return Ok(BlockFlow::Terminated);
            };
            state = next;
        }

        match &block.tail {
            BlockTail::Value(value) => {
                let Some((state, value)) =
                    self.check_expr_with_expected(value, state, mode, expected)?
                else {
                    return Ok(BlockFlow::Terminated);
                };
                if function_falloff && mode == Mode::Executable {
                    self.check_function_result(&state, &value)?;
                }
                Ok(BlockFlow::Value(state, value))
            }
            tail => {
                self.check_terminating_tail(tail, state, mode)?;
                Ok(BlockFlow::Terminated)
            }
        }
    }

    /// Handle every block tail that ends the path, shared by the
    /// value-position checker (`check_block_with_expected`) and the
    /// eval-position one (`check_eval_block`).
    ///
    /// The two used to spell this out separately and disagreed in both
    /// directions: the eval copy treated an `abort` tail as a LIVE join
    /// input -- so an aborting `if` arm that had advanced World made the
    /// join mint a fresh token and every later use of the pre-branch token
    /// was reported stale -- while silently dropping the payload of
    /// `return` / `break` / `continue` / labeled-exit tails, which are
    /// exactly the tails that carry a World token away from the path.
    /// Neither surface may model termination on its own.
    fn check_terminating_tail(
        &mut self,
        tail: &BlockTail,
        state: FlowState,
        mode: Mode,
    ) -> Result<(), WorldFlowError> {
        match tail {
            BlockTail::Value(_) => Ok(()),
            BlockTail::Return(value) => {
                if let Some((state, value)) = self.check_expr(value, state, mode)? {
                    if mode == Mode::Executable {
                        self.check_function_result(&state, &value)?;
                    }
                }
                Ok(())
            }
            BlockTail::Abort { code } => {
                let _ = self.check_expr(code, state, mode)?;
                Ok(())
            }
            BlockTail::Break { level, value } => {
                if let Some((state, value)) = self.check_expr(value, state, mode)? {
                    self.record_loop_jump(*level, state, value, false)?;
                }
                Ok(())
            }
            BlockTail::Continue { level, value } => {
                if let Some((state, value)) = self.check_expr(value, state, mode)? {
                    self.record_loop_jump(*level, state, value, true)?;
                }
                Ok(())
            }
            BlockTail::ReturnFromBlock { level, value } => {
                if let Some((state, value)) = self.check_expr(value, state, mode)? {
                    self.record_labeled_exit(*level, state, value);
                }
                Ok(())
            }
        }
    }

    fn check_stmt(
        &mut self,
        stmt: &Stmt,
        state: FlowState,
        mode: Mode,
    ) -> Result<Option<FlowState>, WorldFlowError> {
        match stmt {
            Stmt::Eval(expr) => Ok(self
                .check_eval_expr(expr, state, mode)?
                .map(|(state, _)| state)),
            Stmt::Let { pattern, value } => {
                let value_type = type_of(value, &state.types, self.program).ok();
                let expected = crate::render::rendered_let_target_type(
                    pattern,
                    value,
                    &self.var_target_types,
                    self.program,
                    &state.render_types,
                );
                let rendered_bindings = crate::render::rendered_let_bindings(
                    pattern,
                    value,
                    expected.as_ref(),
                    self.program,
                    &state.render_types,
                );
                let Some((mut state, value_flow)) =
                    self.check_expr_with_expected(value, state, mode, expected.as_ref())?
                else {
                    return Ok(None);
                };
                if let Some(value_type) = &value_type {
                    let _ = bind_pattern(pattern, value_type, &mut state.types);
                }
                for (var, ty) in rendered_bindings {
                    state.render_types.insert(var, ty);
                }
                bind_pattern_flow(
                    pattern,
                    value_type.as_ref(),
                    value_flow,
                    &mut state,
                    self.world_id,
                );
                Ok(Some(state))
            }
        }
    }

    fn check_expr(
        &mut self,
        expr: &Expr,
        state: FlowState,
        mode: Mode,
    ) -> Result<Option<(FlowState, ValueFlow)>, WorldFlowError> {
        self.check_expr_with_expected(expr, state, mode, None)
    }

    fn check_eval_expr(
        &mut self,
        expr: &Expr,
        state: FlowState,
        mode: Mode,
    ) -> Result<Option<(FlowState, ValueFlow)>, WorldFlowError> {
        match expr {
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let Some((state, _)) = self.check_expr(cond, state, mode)? else {
                    return Ok(None);
                };
                let mut live = Vec::new();
                for branch in [then_branch.as_ref(), else_branch.as_ref()] {
                    if let Some(value) = self.check_eval_block(branch, state.clone(), mode)? {
                        live.push(value);
                    }
                }
                self.join_live(&state, live)
            }
            Expr::Match {
                struct_id,
                selector,
                cases,
            } => {
                let selector_type = type_of(selector, &state.types, self.program).ok();
                let type_args = selector_type
                    .as_ref()
                    .and_then(|ty| struct_type_args(ty, *struct_id))
                    .unwrap_or_default();
                let render_type_args = crate::render::rendered_match_selector_type_args(
                    *struct_id,
                    selector,
                    self.program,
                    &state.render_types,
                );
                let Some((state, selector)) = self.check_expr(selector, state, mode)? else {
                    return Ok(None);
                };
                self.check_match(
                    *struct_id,
                    &type_args,
                    &render_type_args,
                    &selector,
                    &state,
                    cases,
                    None,
                    mode,
                    true,
                )
            }
            _ => self.check_expr(expr, state, mode),
        }
    }

    fn check_eval_block(
        &mut self,
        block: &Block,
        mut state: FlowState,
        mode: Mode,
    ) -> Result<Option<(FlowState, ValueFlow)>, WorldFlowError> {
        for stmt in &block.stmts {
            let Some(next) = self.check_stmt(stmt, state, mode)? else {
                return Ok(None);
            };
            state = next;
        }
        match &block.tail {
            BlockTail::Value(value) => self.check_eval_expr(value, state, mode),
            tail => {
                self.check_terminating_tail(tail, state, mode)?;
                Ok(None)
            }
        }
    }

    fn check_expr_with_expected(
        &mut self,
        expr: &Expr,
        state: FlowState,
        mode: Mode,
        expected: Option<&Type>,
    ) -> Result<Option<(FlowState, ValueFlow)>, WorldFlowError> {
        match expr {
            Expr::Var(var) => {
                let flow = state.values.get(var).cloned().unwrap_or_else(|| {
                    state
                        .types
                        .get(var)
                        .map(|ty| unknown_for_type(ty, self.world_id))
                        .unwrap_or(ValueFlow::Other)
                });
                Ok(Some((state, flow)))
            }
            Expr::Const(_)
            | Expr::Unit
            | Expr::BorrowLoc(_)
            | Expr::BorrowGlobal(_)
            | Expr::IsParent { .. } => self.check_other(expr, std::iter::empty(), state, mode),
            Expr::Call {
                fun,
                type_args,
                args,
            } => self.check_call(*fun, type_args, args, state, mode),
            Expr::Tuple(items) => {
                let Some((state, flows)) = self.check_exprs(items, state, mode)? else {
                    return Ok(None);
                };
                Ok(Some((state, tuple_flow(flows))))
            }
            Expr::Pack {
                struct_id,
                variant: Some(variant),
                fields,
                ..
            } => {
                let Some((state, fields)) = self.check_exprs(fields, state, mode)? else {
                    return Ok(None);
                };
                let current = state.current;
                Ok(Some((
                    state,
                    ValueFlow::Enum {
                        struct_id: *struct_id,
                        base: current,
                        variants: BTreeMap::from([(
                            *variant,
                            VariantFlow {
                                current,
                                refinable: true,
                                fields,
                            },
                        )]),
                    },
                )))
            }
            Expr::Pack { fields, .. } => self.check_other(expr, fields, state, mode),
            Expr::BinOp { lhs, rhs, .. } => {
                self.check_other(expr, [lhs.as_ref(), rhs.as_ref()], state, mode)
            }
            Expr::UnOp { operand, .. }
            | Expr::Unpack { value: operand, .. }
            | Expr::Field { base: operand, .. }
            | Expr::ReadRef(operand)
            | Expr::ToProp(operand)
            | Expr::ToBool(operand) => {
                self.check_other(expr, std::iter::once(operand.as_ref()), state, mode)
            }
            Expr::BitOp(op) => {
                let operands: Vec<&Expr> = match op {
                    BitOp::Extract { operand, .. }
                    | BitOp::ZeroExtend { operand, .. }
                    | BitOp::SignExtend { operand, .. } => vec![operand],
                    BitOp::Concat { high, low } => vec![high, low],
                };
                self.check_other(expr, operands, state, mode)
            }
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let Some((state, _)) = self.check_expr(cond, state, mode)? else {
                    return Ok(None);
                };
                self.check_branching(
                    &state,
                    [then_branch.as_ref(), else_branch.as_ref()],
                    expected,
                    mode,
                )
            }
            Expr::Match {
                struct_id,
                selector,
                cases,
            } => {
                let selector_type = type_of(selector, &state.types, self.program).ok();
                let type_args = selector_type
                    .as_ref()
                    .and_then(|ty| struct_type_args(ty, *struct_id))
                    .unwrap_or_default();
                let render_type_args = crate::render::rendered_match_selector_type_args(
                    *struct_id,
                    selector,
                    self.program,
                    &state.render_types,
                );
                let Some((state, selector)) = self.check_expr(selector, state, mode)? else {
                    return Ok(None);
                };
                self.check_match(
                    *struct_id,
                    &type_args,
                    &render_type_args,
                    &selector,
                    &state,
                    cases,
                    expected,
                    mode,
                    false,
                )
            }
            Expr::While {
                header,
                cond,
                body,
                iter_locals,
                header_exit_locals,
                ..
            } => self.check_while(
                header,
                cond,
                body,
                iter_locals,
                header_exit_locals,
                state,
                mode,
                expr,
            ),
            Expr::Borrow { step, base } => self.check_other(
                expr,
                step.exprs().chain(std::iter::once(base.as_ref())),
                state,
                mode,
            ),
            Expr::Update { step, base, value } => self.check_other(
                expr,
                step.exprs()
                    .chain(std::iter::once(base.as_ref()))
                    .chain(std::iter::once(value.as_ref())),
                state,
                mode,
            ),
            Expr::WriteRef { reference, value } => {
                self.check_other(expr, [reference.as_ref(), value.as_ref()], state, mode)
            }
            Expr::WriteBack {
                world: Some(world), ..
            } => self.check_world_writeback(expr, world, state, mode),
            Expr::WriteBack { world: None, .. } => {
                self.check_other(expr, std::iter::empty(), state, mode)
            }
            Expr::Quantifier {
                binder,
                binder_type,
                domain,
                body,
                ..
            } => {
                let Some(state) = self.check_quant_domain(domain, state, mode)? else {
                    return Ok(None);
                };
                let mut snapshot = state.clone();
                snapshot.types.insert(binder.clone(), binder_type.clone());
                snapshot
                    .render_types
                    .insert(binder.clone(), binder_type.clone());
                record_value(
                    &mut snapshot.values,
                    binder.clone(),
                    unknown_for_type(binder_type, self.world_id),
                );
                let _ = self.check_block(body, snapshot, Mode::Snapshot, false)?;
                let flow = unknown_for_expr(expr, &state, self.program, self.world_id);
                Ok(Some((state, flow)))
            }
            Expr::LabeledBlock { body, .. } => {
                let outer = state.clone();
                self.labeled_blocks.push(LabeledFrame::default());
                let natural = self.check_block_with_expected(body, state, mode, false, expected)?;
                let frame = self
                    .labeled_blocks
                    .pop()
                    .expect("labeled-block frame was just pushed");
                let mut exits = frame.exits;
                if let BlockFlow::Value(state, value) = natural {
                    exits.push((state, value));
                }
                self.join_live(&outer, exits)
            }
        }
    }

    fn check_exprs(
        &mut self,
        exprs: &[Expr],
        mut state: FlowState,
        mode: Mode,
    ) -> Result<Option<(FlowState, Vec<ValueFlow>)>, WorldFlowError> {
        let mut values = Vec::with_capacity(exprs.len());
        for expr in exprs {
            let Some((next, value)) = self.check_expr(expr, state, mode)? else {
                return Ok(None);
            };
            state = next;
            values.push(value);
        }
        Ok(Some((state, values)))
    }

    fn check_other<'a>(
        &mut self,
        whole: &Expr,
        operands: impl IntoIterator<Item = &'a Expr>,
        mut state: FlowState,
        mode: Mode,
    ) -> Result<Option<(FlowState, ValueFlow)>, WorldFlowError> {
        for operand in operands {
            let Some((next, _)) = self.check_expr(operand, state, mode)? else {
                return Ok(None);
            };
            state = next;
        }
        let flow = unknown_for_expr(whole, &state, self.program, self.world_id);
        Ok(Some((state, flow)))
    }

    fn check_call(
        &mut self,
        fun: FunId,
        type_args: &[Type],
        args: &[Expr],
        state: FlowState,
        mode: Mode,
    ) -> Result<Option<(FlowState, ValueFlow)>, WorldFlowError> {
        let Some((state, arg_flows)) = self.check_exprs(args, state, mode)? else {
            return Ok(None);
        };
        let Some(callee) = self.program.lookup_callee(fun) else {
            return Ok(Some((state, ValueFlow::Other)));
        };
        let signature = callee.signature();
        let world_params: Vec<_> = signature
            .params
            .iter()
            .enumerate()
            .filter(|(_, param)| is_world_type(&param.ty, self.world_id))
            .map(|(index, _)| index)
            .collect();
        let world_returns = direct_world_positions(&signature.return_type, self.world_id);
        let return_type = substitute_type_params(&signature.return_type, type_args);
        let has_channel = !world_returns.is_empty() || callee.effects().world_writes;
        let is_loop_step = loop_step_struct(&return_type, self.program).is_some();
        let is_abort_family = matches!(
            callee,
            crate::ir::CalleeRef::Translated(function)
                if is_aborts_family_name(&function.name)
        );
        if world_params.is_empty()
            || (world_params.len() > 1 && !has_channel && !is_loop_step && !is_abort_family)
        {
            return Ok(Some((state, unknown_for_type(&return_type, self.world_id))));
        }

        let channel_position = match callee {
            crate::ir::CalleeRef::Translated(function) => {
                function_lifecycle_world_position(function, self.world_id)
            }
            crate::ir::CalleeRef::Native(_) => {
                lifecycle_world_position(&signature.params, self.world_id)
            }
        }
        .expect("a World parameter was found above");
        let input = arg_flows.get(channel_position).and_then(direct_world_token);
        if input != Some(state.current) {
            return Err(WorldFlowError::StaleToken);
        }
        if !has_channel {
            let flow = loop_step_flow(
                &return_type,
                signature,
                &arg_flows,
                self.program,
                self.world_id,
                state.current,
            )
            .unwrap_or_else(|| unknown_for_type(&return_type, self.world_id));
            return Ok(Some((state, flow)));
        }
        if world_returns.len() != 1 {
            return Err(WorldFlowError::StaleToken);
        }
        match mode {
            Mode::Snapshot => {
                let flow = flow_with_world_token(&return_type, world_returns[0], input);
                Ok(Some((state, flow)))
            }
            Mode::Executable => {
                let token = self.fresh_token();
                let mut state = state;
                state.current = token;
                let flow = flow_with_world_token(&return_type, world_returns[0], Some(token));
                Ok(Some((state, flow)))
            }
        }
    }

    fn check_world_writeback(
        &mut self,
        expr: &Expr,
        world: &VarId,
        state: FlowState,
        mode: Mode,
    ) -> Result<Option<(FlowState, ValueFlow)>, WorldFlowError> {
        if mode == Mode::Snapshot {
            return Err(WorldFlowError::StaleToken);
        }
        let input = match state.values.get(world) {
            Some(ValueFlow::World(input)) => *input,
            _ => return Err(WorldFlowError::MalformedWriteBack),
        };
        if input != Some(state.current) {
            return Err(WorldFlowError::StaleToken);
        }
        let token = self.fresh_token();
        let ty = type_of(expr, &state.types, self.program).ok();
        let mut state = state;
        state.current = token;
        let flow = match ty {
            Some(ty) => {
                let positions = direct_world_positions(&ty, self.world_id);
                if positions.len() == 1 {
                    flow_with_world_token(&ty, positions[0], Some(token))
                } else {
                    unknown_for_type(&ty, self.world_id)
                }
            }
            None => ValueFlow::Tuple(vec![ValueFlow::Other, ValueFlow::World(Some(token))]),
        };
        Ok(Some((state, flow)))
    }

    fn check_branching<'a>(
        &mut self,
        outer: &FlowState,
        branches: impl IntoIterator<Item = &'a Block>,
        expected: Option<&Type>,
        mode: Mode,
    ) -> Result<Option<(FlowState, ValueFlow)>, WorldFlowError> {
        let mut live = Vec::new();
        for branch in branches {
            if let BlockFlow::Value(state, value) =
                self.check_block_with_expected(branch, outer.clone(), mode, false, expected)?
            {
                live.push((state, value));
            }
        }
        self.join_live(outer, live)
    }

    fn check_match(
        &mut self,
        struct_id: StructId,
        type_args: &[Type],
        render_type_args: &[Type],
        selector: &ValueFlow,
        outer: &FlowState,
        cases: &[MatchArm],
        expected: Option<&Type>,
        mode: Mode,
        eval_context: bool,
    ) -> Result<Option<(FlowState, ValueFlow)>, WorldFlowError> {
        let known_variants = match selector {
            ValueFlow::Enum {
                struct_id: actual,
                base,
                variants,
            } if *actual == struct_id => Some((*base, variants)),
            _ => None,
        };
        let mut live = Vec::new();
        for arm in cases {
            if known_variants.is_some_and(|(_, variants)| !variants.contains_key(&arm.variant)) {
                continue;
            }
            let mut arm_state = outer.clone();
            let known_variant = known_variants.and_then(|(_, variants)| variants.get(&arm.variant));
            if let Some(variant) = known_variant.filter(|variant| {
                variant.refinable && known_variants.is_some_and(|(base, _)| base == outer.current)
            }) {
                for value in arm_state.values.values_mut() {
                    *value = remap_current(value.clone(), outer.current, variant.current);
                }
                arm_state.current = variant.current;
            }
            for binding in &arm.bindings {
                arm_state.types.remove(binding);
                arm_state.render_types.remove(binding);
                arm_state.values.remove(binding);
            }
            if let Some(variant) = self
                .program
                .structs
                .get(&struct_id)
                .and_then(|structure| structure.variant_by_tag(arm.variant))
            {
                for (index, (binding, field)) in
                    arm.bindings.iter().zip(&variant.fields).enumerate()
                {
                    let ty = substitute_type_params(&field.field_type, type_args);
                    arm_state.types.insert(binding.clone(), ty.clone());
                    arm_state.render_types.insert(
                        binding.clone(),
                        substitute_type_params(&field.field_type, render_type_args),
                    );
                    let value = known_variant
                        .and_then(|variant| variant.fields.get(index))
                        .cloned()
                        .unwrap_or_else(|| unknown_for_type(&ty, self.world_id));
                    record_value(&mut arm_state.values, binding.clone(), value);
                }
            }
            let loop_exit_starts: Vec<usize> =
                self.loops.iter().map(|frame| frame.breaks.len()).collect();
            let labeled_exit_starts: Vec<usize> = self
                .labeled_blocks
                .iter()
                .map(|frame| frame.exits.len())
                .collect();
            let result = if eval_context {
                match self.check_eval_block(&arm.body, arm_state, mode)? {
                    Some((state, value)) => BlockFlow::Value(state, value),
                    None => BlockFlow::Terminated,
                }
            } else {
                self.check_block_with_expected(&arm.body, arm_state, mode, false, expected)?
            };
            for (frame, start) in self.loops.iter_mut().zip(loop_exit_starts) {
                for state in &mut frame.breaks[start..] {
                    restore_match_bindings(outer, state, &arm.bindings);
                }
            }
            for (frame, start) in self.labeled_blocks.iter_mut().zip(labeled_exit_starts) {
                for (state, _) in &mut frame.exits[start..] {
                    restore_match_bindings(outer, state, &arm.bindings);
                }
            }
            if let BlockFlow::Value(mut state, value) = result {
                restore_match_bindings(outer, &mut state, &arm.bindings);
                live.push((state, value));
            }
        }
        self.join_live(outer, live)
    }

    fn join_live(
        &mut self,
        outer: &FlowState,
        live: Vec<(FlowState, ValueFlow)>,
    ) -> Result<Option<(FlowState, ValueFlow)>, WorldFlowError> {
        if live.is_empty() {
            return Ok(None);
        }
        if live.len() == 1 {
            return Ok(live.into_iter().next());
        }

        let currents: Vec<Token> = live.iter().map(|(state, _)| state.current).collect();
        let joined_current = if currents.iter().all(|token| *token == currents[0]) {
            currents[0]
        } else {
            self.fresh_token()
        };
        let mut types = BTreeMap::new();
        let mut keys: BTreeSet<VarId> = outer.types.keys().cloned().collect();
        if let Some((first, _)) = live.first() {
            for key in first.types.keys() {
                if live.iter().all(|(state, _)| state.types.contains_key(key)) {
                    keys.insert(key.clone());
                }
            }
        }
        for key in keys {
            let Some(first) = live[0].0.types.get(&key) else {
                continue;
            };
            if live
                .iter()
                .all(|(state, _)| state.types.get(&key) == Some(first))
            {
                types.insert(key, first.clone());
            }
        }

        let mut render_types = BTreeMap::new();
        let mut render_keys: BTreeSet<VarId> = outer.render_types.keys().cloned().collect();
        if let Some((first, _)) = live.first() {
            for key in first.render_types.keys() {
                if live
                    .iter()
                    .all(|(state, _)| state.render_types.contains_key(key))
                {
                    render_keys.insert(key.clone());
                }
            }
        }
        for key in render_keys {
            let Some(first) = live[0].0.render_types.get(&key) else {
                continue;
            };
            if live
                .iter()
                .all(|(state, _)| state.render_types.get(&key) == Some(first))
            {
                render_types.insert(key, first.clone());
            }
        }

        let mut values = BTreeMap::new();
        for (var, ty) in &types {
            let arm_values: Vec<ValueFlow> = live
                .iter()
                .map(|(state, _)| {
                    state
                        .values
                        .get(var)
                        .cloned()
                        .unwrap_or_else(|| unknown_for_type(ty, self.world_id))
                })
                .collect();
            let merged = self.merge_values(&arm_values, &currents, joined_current);
            record_value(&mut values, var.clone(), merged);
        }

        let result_values: Vec<ValueFlow> = live.iter().map(|(_, value)| value.clone()).collect();
        let result = self.merge_values(&result_values, &currents, joined_current);
        Ok(Some((
            FlowState {
                types,
                render_types,
                values,
                current: joined_current,
            },
            result,
        )))
    }

    fn merge_values(
        &mut self,
        values: &[ValueFlow],
        currents: &[Token],
        joined_current: Token,
    ) -> ValueFlow {
        if values.iter().all(|value| value == &values[0]) {
            return if currents.iter().all(|current| *current == currents[0]) {
                remap_current(values[0].clone(), currents[0], joined_current)
            } else {
                values[0].clone()
            };
        }
        match &values[0] {
            ValueFlow::World(_) if values.iter().all(|v| matches!(v, ValueFlow::World(_))) => {
                let tokens: Vec<Option<Token>> = values
                    .iter()
                    .map(|value| match value {
                        ValueFlow::World(token) => *token,
                        _ => unreachable!(),
                    })
                    .collect();
                if tokens
                    .iter()
                    .zip(currents)
                    .all(|(token, current)| *token == Some(*current))
                {
                    ValueFlow::World(Some(joined_current))
                } else if tokens.iter().any(Option::is_none) {
                    ValueFlow::World(None)
                } else {
                    ValueFlow::World(Some(self.fresh_token()))
                }
            }
            ValueFlow::Tuple(first)
                if values.iter().all(
                    |value| matches!(value, ValueFlow::Tuple(items) if items.len() == first.len()),
                ) =>
            {
                let items = (0..first.len())
                    .map(|index| {
                        let slot_values: Vec<ValueFlow> = values
                            .iter()
                            .map(|value| match value {
                                ValueFlow::Tuple(items) => items[index].clone(),
                                _ => unreachable!(),
                            })
                            .collect();
                        self.merge_values(&slot_values, currents, joined_current)
                    })
                    .collect();
                ValueFlow::Tuple(items)
            }
            ValueFlow::Enum {
                struct_id,
                base: _,
                variants: _,
            } if values.iter().all(
                |value| matches!(value, ValueFlow::Enum { struct_id: actual, .. } if actual == struct_id),
            ) => {
                let mut variant_ids = BTreeSet::new();
                for value in values {
                    let ValueFlow::Enum { variants, .. } = value else {
                        unreachable!()
                    };
                    variant_ids.extend(variants.keys().copied());
                }

                let mut merged_variants = BTreeMap::new();
                for variant in variant_ids {
                    let entries: Vec<_> = values
                        .iter()
                        .zip(currents)
                        .filter_map(|(value, branch_current)| {
                            let ValueFlow::Enum { base, variants, .. } = value else {
                                unreachable!()
                            };
                            variants
                                .get(&variant)
                                .map(|flow| (flow, *base, *branch_current))
                        })
                        .collect();
                    let Some((first, _, _)) = entries.first() else {
                        continue;
                    };
                    if entries
                        .iter()
                        .any(|(entry, _, _)| entry.fields.len() != first.fields.len())
                    {
                        return ValueFlow::Other;
                    }
                    let variant_currents: Vec<_> =
                        entries.iter().map(|(entry, _, _)| entry.current).collect();
                    let variant_current = if variant_currents
                        .iter()
                        .all(|current| *current == variant_currents[0])
                    {
                        variant_currents[0]
                    } else {
                        self.fresh_token()
                    };
                    let fields = (0..first.fields.len())
                        .map(|index| {
                            let field_values: Vec<_> = entries
                                .iter()
                                .map(|(entry, _, _)| entry.fields[index].clone())
                                .collect();
                            self.merge_values(
                                &field_values,
                                &variant_currents,
                                variant_current,
                            )
                        })
                        .collect();
                    merged_variants.insert(
                        variant,
                        VariantFlow {
                            current: variant_current,
                            refinable: entries.iter().all(|(entry, base, branch_current)| {
                                entry.refinable && base == branch_current
                            }),
                            fields,
                        },
                    );
                }
                ValueFlow::Enum {
                    struct_id: *struct_id,
                    base: joined_current,
                    variants: merged_variants,
                }
            }
            _ => ValueFlow::Other,
        }
    }

    fn record_loop_jump(
        &mut self,
        level: u32,
        state: FlowState,
        value: ValueFlow,
        is_continue: bool,
    ) -> Result<(), WorldFlowError> {
        let Some(index) = self.loops.len().checked_sub(level as usize + 1) else {
            return Ok(());
        };
        let world = self.loops[index].world.clone();
        self.require_loop_current(&world, &state, Some(&value))?;
        if !is_continue {
            self.loops[index].breaks.push(state);
        }
        Ok(())
    }

    fn record_labeled_exit(&mut self, level: u32, state: FlowState, value: ValueFlow) {
        let Some(index) = self.labeled_blocks.len().checked_sub(level as usize + 1) else {
            return;
        };
        self.labeled_blocks[index].exits.push((state, value));
    }

    fn require_loop_current(
        &self,
        world: &LoopWorld,
        state: &FlowState,
        payload: Option<&ValueFlow>,
    ) -> Result<(), WorldFlowError> {
        let token = match world {
            LoopWorld::None => return Ok(()),
            LoopWorld::Implicit(var) => state.values.get(var).and_then(direct_world_token),
            LoopWorld::Slot {
                index,
                arity,
                binder,
            } => payload
                .and_then(|value| flow_slot(value, *index, *arity))
                .or_else(|| state.values.get(binder))
                .and_then(direct_world_token),
        };
        if token == Some(state.current) {
            Ok(())
        } else {
            Err(WorldFlowError::StaleToken)
        }
    }

    fn check_while(
        &mut self,
        header: &Block,
        cond: &Expr,
        body: &Block,
        iter_locals: &[(VarId, Expr)],
        header_exit_locals: &[VarId],
        mut outer: FlowState,
        mode: Mode,
        whole_expr: &Expr,
    ) -> Result<Option<(FlowState, ValueFlow)>, WorldFlowError> {
        let mut initial_values = Vec::with_capacity(iter_locals.len());
        let mut initial_types = Vec::with_capacity(iter_locals.len());
        let mut initial_render_types = Vec::with_capacity(iter_locals.len());
        for (_, init) in iter_locals {
            initial_types.push(type_of(init, &outer.types, self.program).ok());
            initial_render_types.push(crate::render::effective_type_of(
                init,
                self.program,
                &outer.render_types,
            ));
            let Some((next, value)) = self.check_expr(init, outer, mode)? else {
                return Ok(None);
            };
            outer = next;
            initial_values.push(value);
        }

        if mode == Mode::Snapshot {
            let _ = self.check_block(header, outer.clone(), mode, false)?;
            let _ = self.check_expr(cond, outer.clone(), mode)?;
            let _ = self.check_block(body, outer.clone(), mode, false)?;
            let flow = unknown_for_expr(whole_expr, &outer, self.program, self.world_id);
            return Ok(Some((outer, flow)));
        }

        let world_slots: Vec<usize> = initial_types
            .iter()
            .enumerate()
            .filter_map(|(index, ty)| {
                ty.as_ref()
                    .is_some_and(|ty| is_world_type(ty, self.world_id))
                    .then_some(index)
            })
            .collect();
        if world_slots.len() > 1 {
            return Err(WorldFlowError::StaleToken);
        }
        if !header_exit_locals.is_empty() && header_exit_locals.len() != iter_locals.len() {
            return Err(WorldFlowError::StaleToken);
        }
        let advances_world = while_advances_world(header, cond, body, self.program, self.world_id);
        if advances_world && !iter_locals.is_empty() && world_slots.is_empty() {
            return Err(WorldFlowError::StaleToken);
        }
        let world = if let Some(index) = world_slots.first().copied() {
            LoopWorld::Slot {
                index,
                arity: iter_locals.len(),
                binder: iter_locals[index].0.clone(),
            }
        } else if iter_locals.is_empty() && advances_world {
            LoopWorld::Implicit(self.world_param.clone())
        } else {
            LoopWorld::None
        };

        let carries_world = !matches!(world, LoopWorld::None);
        let head = carries_world.then(|| self.fresh_token());
        let mut loop_state = outer.clone();
        if let Some(head) = head {
            loop_state.current = head;
        }
        for (index, (binder, _)) in iter_locals.iter().enumerate() {
            if let Some(ty) = &initial_types[index] {
                loop_state.types.insert(binder.clone(), ty.clone());
            }
            if let Some(ty) = &initial_render_types[index] {
                loop_state.render_types.insert(binder.clone(), ty.clone());
            }
            let mut value = initial_values[index].clone();
            if world_slots.first() == Some(&index) {
                let ValueFlow::World(token) = &mut value else {
                    return Err(WorldFlowError::StaleToken);
                };
                if *token != Some(outer.current) {
                    return Err(WorldFlowError::StaleToken);
                }
                *token = head;
            }
            record_value(&mut loop_state.values, binder.clone(), value);
        }
        if matches!(world, LoopWorld::Implicit(_)) {
            self.require_loop_current(&world, &outer, None)?;
            record_value(
                &mut loop_state.values,
                self.world_param.clone(),
                ValueFlow::World(head),
            );
        }

        self.loops.push(LoopFrame {
            world: world.clone(),
            breaks: Vec::new(),
        });
        let mut normal_exit = None;
        if let BlockFlow::Value(header_state, _) =
            self.check_block(header, loop_state, mode, false)?
        {
            if let Some((body_entry, _)) = self.check_expr(cond, header_state, mode)? {
                // The condition is evaluated after the structured header. A
                // header may advance a carried value (especially World), so
                // validate the post-header SSA slot recorded by stage 5, not
                // the iteration-entry binder. Back-edge payload validation
                // continues to use `record_loop_jump` below.
                if let Some(index) = world_slots.first().copied() {
                    let exit_var = header_exit_locals
                        .get(index)
                        .unwrap_or(&iter_locals[index].0);
                    let token = body_entry.values.get(exit_var).and_then(direct_world_token);
                    if token != Some(body_entry.current) {
                        return Err(WorldFlowError::StaleToken);
                    }
                } else {
                    self.require_loop_current(&world, &body_entry, None)?;
                }
                normal_exit = Some(body_entry.clone());
                if let BlockFlow::Value(body_state, body_value) =
                    self.check_block(body, body_entry, mode, false)?
                {
                    self.record_loop_jump(0, body_state, body_value, true)?;
                }
            }
        }
        let frame = self.loops.pop().expect("loop frame was just pushed");

        let mut exits = frame.breaks;
        if let Some(state) = normal_exit {
            exits.push(state);
        }
        if exits.is_empty() {
            return Ok(None);
        }

        if !carries_world {
            let flow = unknown_for_expr(whole_expr, &outer, self.program, self.world_id);
            return Ok(Some((outer, flow)));
        }

        let currents: Vec<Token> = exits.iter().map(|state| state.current).collect();
        let exit = if currents.iter().all(|token| *token == currents[0]) {
            currents[0]
        } else {
            self.fresh_token()
        };
        outer.current = exit;
        if matches!(world, LoopWorld::Implicit(_)) {
            record_value(
                &mut outer.values,
                self.world_param.clone(),
                ValueFlow::World(Some(exit)),
            );
        }
        let result_type = type_of(whole_expr, &outer.types, self.program).ok();
        let flow = match result_type {
            Some(ty) => {
                let positions = direct_world_positions(&ty, self.world_id);
                if positions.len() == 1 {
                    flow_with_world_token(&ty, positions[0], Some(exit))
                } else {
                    unknown_for_type(&ty, self.world_id)
                }
            }
            None => ValueFlow::Other,
        };
        Ok(Some((outer, flow)))
    }

    fn check_quant_domain(
        &mut self,
        domain: &QuantDomain,
        mut state: FlowState,
        mode: Mode,
    ) -> Result<Option<FlowState>, WorldFlowError> {
        let exprs: Vec<&Expr> = match domain {
            QuantDomain::Unbounded => Vec::new(),
            QuantDomain::Range { start, end } => vec![start, end],
            QuantDomain::Collection(value) => vec![value],
            QuantDomain::VecRange { vec, start, end } => vec![vec, start, end],
        };
        for expr in exprs {
            let Some((next, _)) = self.check_expr(expr, state, mode)? else {
                return Ok(None);
            };
            state = next;
        }
        Ok(Some(state))
    }

    fn check_function_result(
        &self,
        state: &FlowState,
        value: &ValueFlow,
    ) -> Result<(), WorldFlowError> {
        if result_carries_current(
            &self.function.signature.return_type,
            value,
            self.world_id,
            state.current,
        ) {
            Ok(())
        } else {
            Err(WorldFlowError::StaleToken)
        }
    }
}

fn unknown_for_type(ty: &Type, world_id: StructId) -> ValueFlow {
    if is_world_type(ty, world_id) {
        ValueFlow::World(None)
    } else {
        match ty {
            Type::Tuple(items) => tuple_flow(
                items
                    .iter()
                    .map(|item| unknown_for_type(item, world_id))
                    .collect(),
            ),
            _ => ValueFlow::Other,
        }
    }
}

fn loop_step_flow(
    return_type: &Type,
    signature: &crate::ir::Signature,
    arg_flows: &[ValueFlow],
    program: &Program,
    world_id: StructId,
    current: Token,
) -> Option<ValueFlow> {
    let (struct_id, type_args, structure) = loop_step_struct(return_type, program)?;
    let variants = structure.variants.as_ref()?;
    let variants = variants
        .iter()
        .map(|variant| {
            let fields = variant
                .fields
                .iter()
                .map(|field| {
                    signature
                        .params
                        .iter()
                        .position(|param| param.var.as_ref() == field.name)
                        .and_then(|index| arg_flows.get(index).cloned())
                        .unwrap_or_else(|| {
                            let ty = substitute_type_params(&field.field_type, type_args);
                            unknown_for_type(&ty, world_id)
                        })
                })
                .collect();
            (
                variant.tag,
                VariantFlow {
                    current,
                    refinable: false,
                    fields,
                },
            )
        })
        .collect();
    Some(ValueFlow::Enum {
        struct_id,
        base: current,
        variants,
    })
}

fn loop_step_struct<'a>(
    return_type: &'a Type,
    program: &'a Program,
) -> Option<(StructId, &'a [Type], &'a crate::ir::Struct)> {
    let Type::Struct {
        struct_id,
        type_args,
    } = return_type
    else {
        return None;
    };
    let structure = program.structs.get(struct_id)?;
    crate::stage_07_dejumps::aborts_defunctionalize::is_loop_step_struct(structure)
        .then_some((*struct_id, type_args, structure))
}

fn unknown_for_expr(
    expr: &Expr,
    state: &FlowState,
    program: &Program,
    world_id: StructId,
) -> ValueFlow {
    type_of(expr, &state.types, program)
        .map(|ty| unknown_for_type(&ty, world_id))
        .unwrap_or(ValueFlow::Other)
}

fn flow_with_world_token(ty: &Type, index: usize, token: Option<Token>) -> ValueFlow {
    match ty {
        Type::Tuple(items) => tuple_flow(
            items
                .iter()
                .enumerate()
                .map(|(slot, ty)| {
                    if slot == index {
                        ValueFlow::World(token)
                    } else {
                        unknown_for_type_without_world(ty)
                    }
                })
                .collect(),
        ),
        _ if index == 0 => ValueFlow::World(token),
        _ => unknown_for_type_without_world(ty),
    }
}

fn direct_world_token(value: &ValueFlow) -> Option<Token> {
    match value {
        ValueFlow::World(token) => *token,
        _ => None,
    }
}

fn tuple_flow(mut items: Vec<ValueFlow>) -> ValueFlow {
    if items.len() == 1 {
        items.pop().expect("singleton flow has one item")
    } else {
        ValueFlow::Tuple(items)
    }
}

fn flow_slot(value: &ValueFlow, index: usize, arity: usize) -> Option<&ValueFlow> {
    if arity == 1 && index == 0 {
        Some(value)
    } else {
        match value {
            ValueFlow::Tuple(values) => values.get(index),
            _ => None,
        }
    }
}

fn while_advances_world(
    header: &Block,
    cond: &Expr,
    body: &Block,
    program: &Program,
    world_id: StructId,
) -> bool {
    let mut probe = WorldAdvanceProbe {
        program,
        world_id,
        found: false,
    };
    probe.visit_block(header);
    probe.visit_expr(cond);
    probe.visit_block(body);
    probe.found
}

struct WorldAdvanceProbe<'a> {
    program: &'a Program,
    world_id: StructId,
    found: bool,
}

impl Visitor for WorldAdvanceProbe<'_> {
    fn visit_expr(&mut self, expr: &Expr) {
        if self.found {
            return;
        }
        match expr {
            Expr::Call { fun, .. } => {
                self.found = self.program.lookup_callee(*fun).is_some_and(|callee| {
                    let signature = callee.signature();
                    signature
                        .params
                        .iter()
                        .any(|param| is_world_type(&param.ty, self.world_id))
                        && (type_carries_world(&signature.return_type, self.world_id)
                            || callee.effects().world_writes)
                });
                if !self.found {
                    walk_expr_default(self, expr);
                }
            }
            Expr::WriteBack { world: Some(_), .. } => self.found = true,
            Expr::Quantifier { domain, .. } => match domain {
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
            },
            _ => walk_expr_default(self, expr),
        }
    }
}

fn record_value(values: &mut BTreeMap<VarId, ValueFlow>, var: VarId, value: ValueFlow) {
    if contains_world(&value) {
        values.insert(var, value);
    } else {
        values.remove(&var);
    }
}

fn contains_world(value: &ValueFlow) -> bool {
    match value {
        ValueFlow::World(_) => true,
        ValueFlow::Tuple(items) => items.iter().any(contains_world),
        ValueFlow::Enum { .. } => true,
        ValueFlow::Other => false,
    }
}

fn remap_current(value: ValueFlow, from: Token, to: Token) -> ValueFlow {
    match value {
        ValueFlow::World(Some(token)) if token == from => ValueFlow::World(Some(to)),
        ValueFlow::Tuple(items) => ValueFlow::Tuple(
            items
                .into_iter()
                .map(|item| remap_current(item, from, to))
                .collect(),
        ),
        ValueFlow::Enum {
            struct_id,
            base,
            variants,
        } => ValueFlow::Enum {
            struct_id,
            base: if base == from { to } else { base },
            variants: variants
                .into_iter()
                .map(|(variant, flow)| {
                    (
                        variant,
                        VariantFlow {
                            current: if flow.current == from {
                                to
                            } else {
                                flow.current
                            },
                            refinable: flow.refinable,
                            fields: flow
                                .fields
                                .into_iter()
                                .map(|field| remap_current(field, from, to))
                                .collect(),
                        },
                    )
                })
                .collect(),
        },
        other => other,
    }
}

fn struct_type_args(ty: &Type, struct_id: StructId) -> Option<Vec<Type>> {
    match ty {
        Type::Struct {
            struct_id: actual,
            type_args,
        } if *actual == struct_id => Some(type_args.clone()),
        Type::Reference(inner) | Type::MutableRef { inner, .. } => {
            struct_type_args(inner, struct_id)
        }
        Type::Tuple(items) if items.len() == 1 => struct_type_args(&items[0], struct_id),
        _ => None,
    }
}

fn bind_pattern_flow(
    pattern: &[Option<VarId>],
    value_type: Option<&Type>,
    value: ValueFlow,
    state: &mut FlowState,
    world_id: StructId,
) {
    if pattern.len() == 1 {
        if let Some(var) = &pattern[0] {
            let value = match (&value, value_type) {
                (ValueFlow::Tuple(items), Some(Type::Tuple(types)))
                    if items.len() == 1 && types.len() == 1 =>
                {
                    items[0].clone()
                }
                _ => value,
            };
            let value = match state
                .types
                .get(var)
                .filter(|ty| contains_world_type(ty, world_id))
            {
                Some(ty) => coerce_unknown_world(value, ty, world_id),
                None => value,
            };
            record_value(&mut state.values, var.clone(), value);
        }
        return;
    }

    let values = match value {
        ValueFlow::Tuple(values) if values.len() == pattern.len() => values,
        _ => value_type
            .and_then(|ty| match ty {
                Type::Tuple(types) if types.len() == pattern.len() => Some(
                    types
                        .iter()
                        .map(|ty| unknown_for_type(ty, world_id))
                        .collect(),
                ),
                _ => None,
            })
            .unwrap_or_else(|| vec![ValueFlow::Other; pattern.len()]),
    };
    for (slot, value) in pattern.iter().zip(values) {
        if let Some(var) = slot {
            let value = match state
                .types
                .get(var)
                .filter(|ty| contains_world_type(ty, world_id))
            {
                Some(ty) => coerce_unknown_world(value, ty, world_id),
                None => value,
            };
            record_value(&mut state.values, var.clone(), value);
        }
    }
}

fn restore_binding<T: Clone>(
    outer: &BTreeMap<VarId, T>,
    inner: &mut BTreeMap<VarId, T>,
    binding: &VarId,
) {
    if let Some(value) = outer.get(binding) {
        inner.insert(binding.clone(), value.clone());
    } else {
        inner.remove(binding);
    }
}

fn restore_match_bindings(outer: &FlowState, state: &mut FlowState, bindings: &[VarId]) {
    for binding in bindings {
        restore_binding(&outer.types, &mut state.types, binding);
        restore_binding(&outer.render_types, &mut state.render_types, binding);
        restore_binding(&outer.values, &mut state.values, binding);
    }
}

fn contains_world_type(ty: &Type, world_id: StructId) -> bool {
    is_world_type(ty, world_id)
        || matches!(ty, Type::Tuple(items) if items.iter().any(|ty| contains_world_type(ty, world_id)))
}

fn coerce_unknown_world(value: ValueFlow, ty: &Type, world_id: StructId) -> ValueFlow {
    match value {
        ValueFlow::Other => unknown_for_type(ty, world_id),
        other => other,
    }
}

fn unknown_for_type_without_world(ty: &Type) -> ValueFlow {
    match ty {
        Type::Tuple(items) => {
            tuple_flow(items.iter().map(unknown_for_type_without_world).collect())
        }
        _ => ValueFlow::Other,
    }
}

fn result_carries_current(
    return_type: &Type,
    value: &ValueFlow,
    world_id: StructId,
    current: Token,
) -> bool {
    if let Type::Tuple(items) = return_type {
        if items.len() == 1 {
            return result_carries_current(&items[0], value, world_id, current);
        }
    }
    let positions = direct_world_positions(return_type, world_id);
    if positions.is_empty() {
        return true;
    }
    let carries = match (return_type, value) {
        (ty, ValueFlow::World(token)) if is_world_type(ty, world_id) => *token == Some(current),
        (Type::Tuple(types), ValueFlow::Tuple(values)) => positions.into_iter().all(|index| {
            types
                .get(index)
                .is_some_and(|ty| is_world_type(ty, world_id))
                && values.get(index).and_then(direct_world_token) == Some(current)
        }),
        _ => false,
    };
    carries
        || matches!(value, ValueFlow::Tuple(values) if values.len() == 1
            && result_carries_current(return_type, &values[0], world_id, current))
}
