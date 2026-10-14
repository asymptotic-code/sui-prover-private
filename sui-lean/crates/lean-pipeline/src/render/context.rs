use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};

use crate::ir::{FunId, Program, StructId};

use super::loop_termination::LoopRenderContext;

pub(crate) struct RenderAnalyses {
    obj_typeparams: HashMap<FunId, Vec<bool>>,
    tycode_typeparams: HashMap<FunId, Vec<bool>>,
    bagu_typeparams: HashMap<FunId, Vec<bool>>,
    anykey_typeparams: HashMap<FunId, Vec<bool>>,
    df_concrete_types: HashMap<FunId, Vec<String>>,
    df_typeparams: HashMap<FunId, BTreeSet<usize>>,
    df_bound: HashSet<FunId>,
    obj_id_concrete_types: HashMap<FunId, Vec<String>>,
    derived_object_key_structs: BTreeSet<String>,
    mutation_users: BTreeSet<FunId>,
    bag_containing_structs: HashSet<StructId>,
}

impl RenderAnalyses {
    fn new(program: &Program) -> Self {
        // The tycode taint reads the obj taint: a user-package param that is
        // object-tainted loses the unconditional `[HasCode TyCode T]` binder,
        // so it must re-acquire one from every callee still demanding it.
        let obj_typeparams = super::obj_type_universe::compute_obj_typeparam_deps(program);
        let tycode_typeparams =
            super::dyn_type_universe::compute_tycode_typeparam_deps(program, &obj_typeparams);
        let df = super::function::compute_df_universe(program);
        Self {
            obj_typeparams,
            tycode_typeparams,
            bagu_typeparams: super::bag_universe::compute_bagu_typeparam_deps(program),
            anykey_typeparams: super::mutation::compute_anykey_typeparam_deps(program),
            df_concrete_types: df.concrete,
            df_typeparams: df.params,
            df_bound: df.bound,
            obj_id_concrete_types: super::function::compute_obj_id_concrete_types(program),
            derived_object_key_structs: super::function::derived_object_key_struct_names(program),
            mutation_users: super::expr::compute_mutation_users(program),
            bag_containing_structs: super::dyn_type_universe::collect_bag_containing_struct_ids(
                program,
            ),
        }
    }
}

pub(crate) struct RenderContext<'p> {
    pub(crate) program: &'p Program,
    analyses: RenderAnalyses,
    pub(crate) loop_termination: LoopRenderContext,
    serialize_skips: RefCell<BTreeSet<(String, String)>>,
}

impl<'p> RenderContext<'p> {
    pub(crate) fn new(program: &'p Program, loop_termination: LoopRenderContext) -> Self {
        Self {
            program,
            analyses: RenderAnalyses::new(program),
            loop_termination,
            serialize_skips: RefCell::new(BTreeSet::new()),
        }
    }

    pub(crate) fn obj_typeparam_needs_constraint(&self, fid: FunId, index: usize) -> bool {
        analysis_bit(&self.analyses.obj_typeparams, fid, index)
    }

    pub(crate) fn tycode_typeparam_needs_constraint(&self, fid: FunId, index: usize) -> bool {
        analysis_bit(&self.analyses.tycode_typeparams, fid, index)
    }

    pub(crate) fn bagu_typeparam_needs_constraint(&self, fid: FunId, index: usize) -> bool {
        analysis_bit(&self.analyses.bagu_typeparams, fid, index)
    }

    pub(crate) fn anykey_typeparam_needs_constraint(&self, fid: FunId, index: usize) -> bool {
        analysis_bit(&self.analyses.anykey_typeparams, fid, index)
    }

    pub(crate) fn df_concrete_types(&self, fid: FunId) -> &[String] {
        self.analyses
            .df_concrete_types
            .get(&fid)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    /// Type params of a lemma function that need `[HasCode __TyU T]` for the
    /// dynamic-field universe, including those inherited along call edges.
    pub(crate) fn df_typeparams(&self, fid: FunId) -> BTreeSet<usize> {
        self.analyses
            .df_typeparams
            .get(&fid)
            .cloned()
            .unwrap_or_default()
    }

    /// True when a lemma function must bind `{__TyU}` for the df universe
    /// (directly, or by calling a df-universe function).
    pub(crate) fn binds_df_universe(&self, fid: FunId) -> bool {
        !self.df_concrete_types(fid).is_empty()
            || !self.df_typeparams(fid).is_empty()
            || self.analyses.df_bound.contains(&fid)
    }

    pub(crate) fn obj_id_concrete_types(&self, fid: FunId) -> &[String] {
        self.analyses
            .obj_id_concrete_types
            .get(&fid)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub(crate) fn is_derived_object_key_struct(&self, qualified_name: &str) -> bool {
        self.analyses
            .derived_object_key_structs
            .contains(qualified_name)
    }

    pub(crate) fn mutation_users(&self) -> &BTreeSet<FunId> {
        &self.analyses.mutation_users
    }

    pub(crate) fn bag_containing_structs(&self) -> &HashSet<StructId> {
        &self.analyses.bag_containing_structs
    }

    pub(crate) fn anykey_typeparam_deps(&self) -> &HashMap<FunId, Vec<bool>> {
        &self.analyses.anykey_typeparams
    }

    pub(crate) fn obj_typeparam_deps(&self) -> &HashMap<FunId, Vec<bool>> {
        &self.analyses.obj_typeparams
    }

    pub(crate) fn bagu_typeparam_deps(&self) -> &HashMap<FunId, Vec<bool>> {
        &self.analyses.bagu_typeparams
    }

    pub(crate) fn log_serialize_skip_once(&self, name: &str, reason: &str) {
        if self
            .serialize_skips
            .borrow_mut()
            .insert((name.to_string(), reason.to_string()))
        {
            eprintln!("[bcs-serialize] keeping [] for `{name}`: {reason}");
        }
    }
}

fn analysis_bit(map: &HashMap<FunId, Vec<bool>>, fid: FunId, index: usize) -> bool {
    map.get(&fid)
        .and_then(|bits| bits.get(index))
        .copied()
        .unwrap_or(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Block, BlockTail, Effects, Expr, Function, FunctionKind, Signature, Type};

    fn generic_function(body: Block) -> Function {
        Function {
            module: 0,
            name: "f".to_string(),
            signature: Signature {
                type_params: vec!["T".to_string()],
                params: Vec::new(),
                return_type: Type::Unit,
            },
            body,
            kind: FunctionKind::Source,
            effects: Effects::PURE,
            explicit_pure: true,
        }
    }

    #[test]
    fn rebuilding_context_at_same_program_address_refreshes_analyses() {
        let mut program = Program::default();
        program.functions.insert(
            0,
            generic_function(Block {
                stmts: Vec::new(),
                tail: BlockTail::Value(Expr::Unit),
            }),
        );

        let first = RenderContext::new(&program, LoopRenderContext::default());
        assert!(!first.anykey_typeparam_needs_constraint(0, 0));
        drop(first);

        program.functions.get_mut(&0).unwrap().body = Block {
            stmts: Vec::new(),
            tail: BlockTail::Value(Expr::Borrow {
                step: crate::ir::path::PathStep::MapKey {
                    key: Box::new(Expr::Unit),
                    key_type: Type::TypeParam(0),
                    value_type: Type::Unit,
                    df_value: None,
                },
                base: Box::new(Expr::Unit),
            }),
        };

        let second = RenderContext::new(&program, LoopRenderContext::default());
        assert!(second.anykey_typeparam_needs_constraint(0, 0));
    }
}
