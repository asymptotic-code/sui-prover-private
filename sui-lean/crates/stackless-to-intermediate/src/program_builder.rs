// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Builds complete TheoremProgram from Move GlobalEnv
//!
//! Uses lazy ID generation - IDs are created on first reference.
//! Single pass creates all definitions and translates function bodies.

use crate::control_flow_reconstruction::{
    early_return, ir_translation, skeleton_recovery, EmitContext, EmitMode,
};
use crate::package_utils::extract_package_name;
use crate::translation::function_translator;
use intermediate_theorem_format::{
    BuildMode, Const, Field, FunctionID, IRNode, Module, Program, Struct, StructID, Type, Variant,
};
use move_model::model::{DatatypeId, FunId, GlobalEnv, ModuleEnv, QualifiedId};
use move_model::symbol::Symbol;
use move_model::ty::Type as MoveType;
use move_stackless_bytecode::dynamic_field_analysis::DynamicFieldInfo;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::function_target_pipeline::{FunctionTargetsHolder, FunctionVariant};
use std::rc::Rc;

pub struct ProgramBuilder<'env> {
    env: &'env GlobalEnv,
    pub program: Program,
    dynamic_field_info: Option<Rc<DynamicFieldInfo>>,
    /// Per-struct raw dynamic field type pairs, preserving TypeParameter entries.
    /// Collected from per-function analysis before union flattens generics to concrete types.
    raw_df_pairs:
        std::collections::HashMap<MoveType, std::collections::BTreeSet<(MoveType, MoveType)>>,
    mode: BuildMode,
    /// Move-level per-native ghost-marker seed (`(K, V)` pairs each
    /// ghost-writing native's spec declares), handed in by the backend via
    /// [`Self::with_ghost_native_seed`]. Converted to IR types at the end
    /// of `build_inner` into `Program::ghost_native_seed`, which the
    /// `ghost_threading` finalize pass consumes. Empty = inert.
    ghost_native_seed: Vec<(QualifiedId<FunId>, Vec<(MoveType, MoveType)>)>,
    /// Stems of the client-provided `def <stem>.loop_hyp` declarations (from
    /// `sources/lean/Termination/`), handed in by the backend via
    /// [`Self::with_loop_hyp_decls`]. A Move `#[spec_only(loop_inv(...))]`
    /// target's loop machinery (the `hinv` hypothesis param, the user-measure
    /// `termination_by`, the entry/precond cascade) is only emitted when the
    /// client actually shipped a matching `loop_hyp` — the generator never
    /// synthesizes those defs. Without this gate a `loop_inv` annotation alone
    /// produces dangling references to `<loop>.loop_hyp` / `<spec>.requires` /
    /// the termination macros. Empty = no client loop_hyps (all `loop_inv`
    /// loops fall back to the plain `sorry`-termination default).
    loop_hyp_decls: std::collections::HashSet<String>,
}

impl<'env> ProgramBuilder<'env> {
    pub fn new(env: &'env GlobalEnv) -> Self {
        Self {
            raw_df_pairs: std::collections::HashMap::new(),
            env,
            program: Program::default(),
            dynamic_field_info: None,
            mode: BuildMode::Spec,
            ghost_native_seed: Vec::new(),
            loop_hyp_decls: std::collections::HashSet::new(),
        }
    }

    /// Supply the client-provided `loop_hyp` declaration stems (see the field
    /// docs). Gates loop-invariant registration so `loop_inv`-annotated loops
    /// without matching client Lean support degrade to the plain loop instead
    /// of emitting dangling references.
    pub fn with_loop_hyp_decls(mut self, decls: std::collections::HashSet<String>) -> Self {
        self.loop_hyp_decls = decls;
        self
    }

    /// Supply the Move-level ghost-native seed (see the field docs).
    pub fn with_ghost_native_seed(
        mut self,
        seed: Vec<(QualifiedId<FunId>, Vec<(MoveType, MoveType)>)>,
    ) -> Self {
        self.ghost_native_seed = seed;
        self
    }

    pub fn env(&self) -> &GlobalEnv {
        self.env
    }

    pub fn struct_id(&mut self, id: QualifiedId<DatatypeId>) -> StructID {
        let struct_id = self.program.structs.id_for_key(id);
        if !self.program.structs.has(struct_id) {
            self.create_struct(id);
        }
        struct_id
    }

    pub fn function_id(&mut self, id: QualifiedId<FunId>) -> FunctionID {
        let fid = self.program.functions.id_for_key(id);
        // Auto-create an opaque stub for any function whose ID is being
        // newly assigned but whose body hasn't been translated yet. This
        // mirrors the `struct_id` pattern (line above) and ensures every
        // ID returned from this method is backed by a Function in
        // `self.program.functions` — so downstream passes (mutable
        // threading, dead-param elimination, etc.) that walk Call nodes
        // and look up the callee can rely on `program.functions.get(fid)`
        // never panicking.
        //
        // Without this, `--test`-mode pruning (`LeanVerificationAnalysisProcessor`
        // filters out tests not matching `--test-filter`, plus their
        // uniquely-needed callees) leaves Calls in retained-function
        // bodies pointing at IDs that were allocated here but never
        // backed by `process_function`'s `create()` — `mutable_threading::
        // returns_mutable_ref(fid, program)` then panics with
        // `Function N should exist`.
        //
        // If `process_function` later runs for this `qualified_id`, it
        // calls `functions.create(...)` which retrieves the same ID via
        // `id_for_key` and overwrites the stub with the real function.
        // So translated functions are never affected; only filtered-out
        // ones keep the stub.
        if !self.program.functions.has(fid) {
            self.create_function_stub(id, fid);
        }
        fid
    }

    /// Create an opaque stub for a referenced-but-not-translated function.
    /// Pulls the signature from the move-model so callers' arg types match;
    /// body is `Inhabited` and the function is marked `is_native = true` so
    /// analyses that already special-case natives (mutable threading, dead
    /// param elimination) treat the stub as opaque.
    fn create_function_stub(&mut self, qualified_id: QualifiedId<FunId>, fid: FunctionID) {
        let func_env = self.env.get_function(qualified_id);
        let module_id = self.program.modules.id_for_key(qualified_id.module_id);
        if !self.program.modules.has(module_id) {
            self.create_module(&func_env.module_env);
        }
        let name = self.symbol_str(func_env.get_name()).to_string();
        let type_params: Vec<String> = func_env
            .get_type_parameters()
            .iter()
            .map(|tp| self.symbol_str(tp.0).to_string())
            .collect();
        let parameters: Vec<intermediate_theorem_format::Parameter> = func_env
            .get_parameters()
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let n = self.symbol_str(p.0).to_string();
                intermediate_theorem_format::Parameter {
                    name: n.clone(),
                    param_type: self.convert_type(&p.1),
                    ssa_value: format!("$t{}", i).into(),
                }
            })
            .collect();
        let return_types: Vec<intermediate_theorem_format::Type> = func_env
            .get_return_types()
            .iter()
            .map(|t| self.convert_type(t))
            .collect();
        let return_type = match return_types.len() {
            0 => intermediate_theorem_format::Type::Tuple(vec![]),
            1 => return_types.into_iter().next().unwrap(),
            _ => intermediate_theorem_format::Type::Tuple(return_types),
        };
        self.program.functions.insert(
            fid,
            intermediate_theorem_format::Function {
                module_id,
                name,
                signature: intermediate_theorem_format::FunctionSignature {
                    type_params,
                    parameters,
                    proof_params: Vec::new(),
                    return_type,
                },
                body: intermediate_theorem_format::IRNode::Inhabited,
                theorem: None,
                is_native: true,
                mutual_group_id: None,
                test_expectation: None,
                is_uninterpreted: false,
            },
        );
    }

    pub fn build(self, targets: &'env FunctionTargetsHolder) -> Program {
        self.build_with_mode(targets, BuildMode::Spec)
    }

    /// Build a Program with the test-mode option-shape `.aborts`
    /// finalization. Bodies are still translated in `EmitMode::Body` (so
    /// `IRNode::Abort` is preserved inline); finalization runs the regular
    /// pipeline plus `inject_arithmetic_aborts` and `compose_callee_aborts_option`.
    pub fn build_for_test(self, targets: &'env FunctionTargetsHolder) -> Program {
        self.build_for_test_with_hook(targets, |_| {})
    }

    pub fn build_with_mode(self, targets: &'env FunctionTargetsHolder, mode: BuildMode) -> Program {
        self.build_with_mode_and_hook(targets, mode, |_| {})
    }

    /// Like [`Self::build_with_mode`] but runs `pre_finalize` between
    /// the IR translation pass and `Program::finalize_with_mode`.
    /// Lets the caller mutate the `Program` (e.g. augment struct
    /// definitions to match hand-written native overrides) before the
    /// passes that consume those struct definitions run.
    pub fn build_with_mode_and_hook<F>(
        mut self,
        targets: &'env FunctionTargetsHolder,
        mode: BuildMode,
        pre_finalize: F,
    ) -> Program
    where
        F: FnOnce(&mut Program),
    {
        self.mode = mode;
        self.build_inner(targets);
        pre_finalize(&mut self.program);
        self.program.finalize_with_mode(mode);
        self.program
    }

    /// Test-mode counterpart of [`Self::build_with_mode_and_hook`].
    pub fn build_for_test_with_hook<F>(
        mut self,
        targets: &'env FunctionTargetsHolder,
        pre_finalize: F,
    ) -> Program
    where
        F: FnOnce(&mut Program),
    {
        self.mode = BuildMode::Test;
        self.build_inner(targets);
        pre_finalize(&mut self.program);
        self.program.finalize_for_test();
        self.program
    }

    /// Translate every targeted module/function into IR. Stops short of
    /// `Program::finalize_*` so callers can choose between Spec/Test
    /// finalization. Reuses `self.mode` set by the caller.
    fn build_inner(&mut self, targets: &'env FunctionTargetsHolder) {
        let mode = self.mode;
        // Gather DynamicFieldInfo from ALL functions (not just specs) so we know
        // which structs use dynamic fields and what types they store.
        // We collect per-function info to preserve TypeParameter entries, then
        // also build the combined union for backward compatibility.
        let all_fun_ids: Vec<_> = self
            .env
            .get_modules()
            .flat_map(|module_env| {
                module_env
                    .get_functions()
                    .map(|func_env| func_env.get_qualified_id())
                    .collect::<Vec<_>>()
            })
            .collect();

        // Collect per-function raw (uninstantiated) dynamic field type pairs.
        // This preserves TypeParameter(N) references that get lost in iter_union
        // when callers instantiate callees' info with concrete types.
        let mut raw_df_pairs: std::collections::HashMap<
            MoveType,
            std::collections::BTreeSet<(MoveType, MoveType)>,
        > = std::collections::HashMap::new();
        for fun_id in &all_fun_ids {
            if let Some(data) = targets.get_data(fun_id, &FunctionVariant::Baseline) {
                if let Some(info) = data.annotations.get::<DynamicFieldInfo>() {
                    for (struct_type, entries) in info.dynamic_fields() {
                        let pair_set = raw_df_pairs.entry(struct_type.clone()).or_default();
                        for entry in entries {
                            if let Some((k, v)) = entry.as_name_value() {
                                pair_set.insert((k.clone(), v.clone()));
                            }
                        }
                    }
                }
            }
        }

        self.raw_df_pairs = raw_df_pairs;

        let combined_info = DynamicFieldInfo::iter_union(all_fun_ids.iter().filter_map(|fun_id| {
            targets
                .get_data(fun_id, &FunctionVariant::Baseline)
                .and_then(|data| data.annotations.get::<DynamicFieldInfo>().cloned())
        }));
        self.dynamic_field_info = Some(Rc::new(combined_info));

        // Pre-pass: register loop-invariant functions so the while-helper emitter
        // (invoked during create_function below) can look up the invariant for a
        // loop's target by name. Must run before any target is translated because
        // a loop_inv and its target may live in either order / either module.
        for module_env in self.env.get_modules() {
            for func_env in module_env.get_functions() {
                // loop_inv functions are `#[spec_only]` and have no Baseline
                // target, so do NOT gate on get_target_opt here.
                if let Some(target_name) = loop_inv_target_name(&func_env) {
                    // Only honor the `loop_inv` annotation when the client
                    // actually shipped a `def <target>.while_*.loop_hyp` (the
                    // generator never synthesizes the loop_hyp/termination
                    // machinery). Without a matching client decl, registering
                    // the invariant would emit dangling references to
                    // `<loop>.loop_hyp` / `<target>_spec.requires` / the
                    // termination macros; instead we skip registration so the
                    // loop renders as a plain recursive helper with the default
                    // `sorry`-termination, exactly like an unannotated loop.
                    let prefix = format!("{}.while_", target_name);
                    let has_client_loop_hyp =
                        self.loop_hyp_decls.iter().any(|s| s.starts_with(&prefix));
                    if has_client_loop_hyp {
                        let inv_id = self
                            .program
                            .functions
                            .id_for_key(func_env.get_qualified_id());
                        self.program.loop_invariants.insert(target_name, inv_id);
                    } else {
                        eprintln!(
                            "⚠️  loop_inv on `{}`: no client `sources/lean/Termination/` \
                             `loop_hyp` shipped — loop falls back to sorry-termination \
                             (annotation is inert; provide `def {}.while_0.loop_hyp` + \
                             termination measure to activate it)",
                            target_name, target_name
                        );
                    }
                }
            }
        }

        for module_env in self.env.get_modules() {
            let has_targets = module_env.get_functions().any(|func_env| {
                targets
                    .get_target_opt(&func_env, &FunctionVariant::Baseline)
                    .is_some()
            });
            if !has_targets {
                continue;
            }

            self.create_module(&module_env);

            for func_env in module_env.get_functions() {
                if let Some(target) = targets.get_target_opt(&func_env, &FunctionVariant::Baseline)
                {
                    self.create_function(target);
                }
            }
        }

        // Convert the Move-level ghost-native seed into IR types. Done
        // after translation so seeded natives that were translated keep
        // their real IDs; pruned ones get an opaque native stub via
        // `function_id`. Marker structs are interned by `convert_type`.
        let seed = std::mem::take(&mut self.ghost_native_seed);
        for (native_qid, pairs) in seed {
            let fid = self.function_id(native_qid);
            let mut markers: Vec<(Type, Type)> = Vec::with_capacity(pairs.len());
            for (k, v) in &pairs {
                let k_ir = self.convert_type(k);
                let v_ir = self.convert_type(v);
                markers.push((k_ir, v_ir));
            }
            if !markers.is_empty() {
                self.program.ghost_native_seed.insert(fid, markers);
            }
        }
    }

    fn create_module(&mut self, module_env: &ModuleEnv) {
        self.program.modules.create(
            module_env.get_id(),
            Module {
                name: self.symbol_str(module_env.get_name().name()).to_string(),
                package_name: extract_package_name(self.env, module_env),
                required_imports: Vec::new(),
                is_native: false,
            },
        );
    }

    fn create_struct(&mut self, qualified_id: QualifiedId<DatatypeId>) {
        let module_env = self.env.get_module(qualified_id.module_id);
        let struct_symbol = qualified_id.id.symbol();

        let module_id = self.program.modules.id_for_key(qualified_id.module_id);
        if !self.program.modules.has(module_id) {
            self.create_module(&module_env);
        }

        // Register a placeholder before recursing into field types to break cycles
        // (e.g., a struct with a field of its own type).
        let name = self.env.symbol_pool().string(struct_symbol).to_string();
        self.program.structs.create(
            qualified_id,
            Struct {
                module_id,
                name: name.clone(),
                qualified_name: String::new(),
                type_params: Vec::new(),
                fields: Vec::new(),
                mutual_group_id: None,
                variants: None,
            },
        );

        // DatatypeId can refer to either a struct or an enum
        // Try to find as struct first, then fall back to enum
        let Some(move_struct) = module_env.find_struct(struct_symbol) else {
            // Check if it's an enum
            if let Some(move_enum) = module_env.find_enum(struct_symbol) {
                // Collect all variants with their fields
                let variants: Vec<Variant> = move_enum
                    .get_variants()
                    .map(|v| {
                        let variant_name = self.symbol_str(v.get_name()).to_string();
                        let tag = v.get_tag();
                        let fields: Vec<Field> = v
                            .get_fields()
                            .map(|f| Field {
                                name: self.symbol_str(f.get_name()).to_string(),
                                field_type: self.convert_type(&f.get_type()),
                            })
                            .collect();
                        Variant {
                            name: variant_name,
                            tag,
                            fields,
                        }
                    })
                    .collect();

                let struct_id = self.program.structs.id_for_key(qualified_id);
                *self.program.structs.get_mut(struct_id) = Struct {
                    module_id,
                    name: name.clone(),
                    qualified_name: format!("{}::{}", module_env.get_full_name_str(), name),
                    type_params: move_enum
                        .get_type_parameters()
                        .iter()
                        .map(|p| self.symbol_str(p.0))
                        .collect(),
                    fields: vec![],
                    mutual_group_id: None,
                    variants: Some(variants),
                };
                return;
            }
            panic!("Struct not found: {:?}", qualified_id);
        };

        let mut fields: Vec<Field> = move_struct
            .get_fields()
            .map(|f| Field {
                name: self.symbol_str(f.get_name()).to_string(),
                field_type: self.convert_type(&f.get_type()),
            })
            .collect();

        // Add ghost dynamic_fields for each (key, value) type pair used in
        // dynamic field operations on this struct. Uses raw per-function analysis
        // data which preserves TypeParameter references (the combined union resolves
        // them to concrete types from call sites, losing generic info).
        let struct_type = MoveType::Datatype(
            qualified_id.module_id,
            qualified_id.id,
            move_struct
                .get_type_parameters()
                .iter()
                .enumerate()
                .map(|(i, _)| MoveType::TypeParameter(i as u16))
                .collect(),
        );
        let num_struct_params = move_struct.get_type_parameters().len();
        let struct_name = self.symbol_str(move_struct.get_name());
        let module_name = self.symbol_str(module_env.get_name().name());
        let mut ghost_pairs: Vec<(MoveType, MoveType)> = self
            .raw_df_pairs
            .get(&struct_type)
            .map(|pairs| pairs.iter().cloned().collect())
            .unwrap_or_default();

        // Sui framework containers that wrap Dynamic_field but whose functions
        // are removed by VerificationAnalysisProcessor before DynamicFieldAnalysis
        // runs.  Table<K,V> maps K -> V via dynamic fields; inject the ghost pair
        // so the rewriting pass can convert their bodies to TypedMap operations.
        let is_table_special =
            num_struct_params == 2 && &*module_name == "table" && &*struct_name == "Table";
        if ghost_pairs.is_empty() && is_table_special {
            ghost_pairs.push((MoveType::TypeParameter(0), MoveType::TypeParameter(1)));
        }

        // Skip if the struct is non-generic but the module has generic functions
        // (concrete type from monomorphic analysis doesn't represent all usages).
        // Pairs that are fully concrete (no TypeParameter references anywhere)
        // are still safe to add — the analysis recorded the usage at a concrete
        // call site, so the pair is unambiguously the right (K, V) for this
        // struct.
        let has_extra_type_params = num_struct_params == 0
            && module_env
                .get_functions()
                .any(|func_env| func_env.get_type_parameter_count() > num_struct_params);

        // Skip framework-module structs by default. `dynamic_field::*` calls on
        // framework types (e.g. `&mut UID`, `&mut Bag`, `Table`) bubble those
        // structs into `raw_df_pairs` even though we'd never want to extend
        // them with project-style `dynamic_fields_*` ghost fields — the
        // framework types are modeled by hand-written `lemmas/natives/` Lean
        // files whose static imports would break if SCC merging swallowed
        // the modified struct's module into a different file. Identified by
        // standard framework addresses (0x1 = MoveStdlib, 0x2 = Sui
        // framework, 0x3 = Sui system, 0xdee9 = DeepBook).
        //
        // Exception: `table::Table` is a framework type whose hand-written
        // native struct already declares a `dynamic_fields : List (K × V)`
        // field (see `lemmas/natives/Sui/TableNatives.lean`). The IR struct
        // generation must add a matching ghost field or `Table.mk` call
        // sites pass too few args.
        let is_framework_module = {
            let addr_hex = format!("{:x}", module_env.get_name().addr());
            matches!(addr_hex.as_str(), "1" | "2" | "3" | "dee9")
        };
        let skip_for_framework = is_framework_module && !is_table_special;

        // Add one ghost field per (key, value) type pair.
        for (i, (name_type, value_type)) in ghost_pairs.iter().enumerate() {
            let name_ir = self.convert_type(name_type);
            let value_ir = self.convert_type(value_type);
            let ghost_type = Type::Vector(Box::new(Type::Tuple(vec![name_ir, value_ir])));
            let max_idx = ghost_type
                .max_type_param_index()
                .map(|i| i as usize + 1)
                .unwrap_or(0);
            if max_idx > num_struct_params {
                continue;
            }
            // Skip framework-module structs (with the Table exception).
            if skip_for_framework {
                continue;
            }
            // Only skip when the pair carries a TypeParameter reference (which
            // would be ambiguous across instantiations under
            // `has_extra_type_params`). Fully concrete pairs are always safe.
            let pair_uses_type_params = ghost_type.max_type_param_index().is_some();
            if has_extra_type_params && pair_uses_type_params {
                continue;
            }
            let field_name = if ghost_pairs.len() == 1 {
                "dynamic_fields".to_string()
            } else {
                format!("dynamic_fields_{}", i)
            };
            fields.push(Field {
                name: field_name,
                field_type: ghost_type,
            });
        }

        let struct_id = self.program.structs.id_for_key(qualified_id);
        *self.program.structs.get_mut(struct_id) = Struct {
            module_id,
            name: self.symbol_str(move_struct.get_name()).to_string(),
            qualified_name: move_struct.get_full_name_str(),
            type_params: move_struct
                .get_type_parameters()
                .iter()
                .map(|p| self.symbol_str(p.0))
                .collect(),
            fields,
            mutual_group_id: None,
            variants: None,
        };
    }

    fn create_function(&mut self, target: FunctionTarget<'_>) {
        let qualified_id = target.func_env.get_qualified_id();

        // Build variables and signature early so EmitContext can use them for while loops
        let variables = function_translator::build_variables(self, &target);
        let mut signature = function_translator::build_signature(self, target.func_env, &target);
        let func_name = self.symbol_str(target.func_env.get_name()).to_string();

        // Spec-only functions are logical assertions, not computations.
        // Promote Bool return type to Prop so forall/exists produce real propositions
        // and && becomes ∧ (via the lift_bool_tails_to_prop pass).
        if signature.return_type == Type::Bool && is_spec_only_loop_inv(target.func_env) {
            signature.return_type = Type::Prop;
        }
        let module_id = self
            .program
            .modules
            .id_for_key(target.func_env.module_env.get_id());

        let (body, aborts) = if target.func_env.is_native() || target.get_bytecode().is_empty() {
            // Native functions keep sorry body but never abort
            (IRNode::default(), IRNode::Const(Const::Bool(false)))
        } else {
            let should_probe = std::env::var("PROBE_CFG")
                .map(|v| v == "1" || v == func_name)
                .unwrap_or(false);
            if should_probe {
                eprintln!("PROBE_CFG ===== function: {} =====", func_name);
                std::env::set_var("PROBE_CFG_ACTIVE", "1");
            }
            let skel = skeleton_recovery::recover(&target);
            let structure = ir_translation::translate(&skel, &target, self);
            if should_probe {
                std::env::remove_var("PROBE_CFG_ACTIVE");
                eprintln!("PROBE_CFG structure={:#?}", structure);
            }

            // Pass 1: emit body (return value)
            let preserve_aborts = matches!(self.mode, BuildMode::Test);
            let mut body_ctx = EmitContext::new_with_options(
                &mut self.program,
                module_id,
                func_name.clone(),
                &signature,
                variables.clone(),
                EmitMode::Body,
                preserve_aborts,
            );
            let body = early_return::emit(&mut body_ctx, &structure);

            // Pass 2: emit aborts (Bool)
            let mut aborts_ctx = EmitContext::new(
                &mut self.program,
                module_id,
                func_name.clone(),
                &signature,
                variables.clone(),
                EmitMode::Aborts,
            );
            let aborts = early_return::emit(&mut aborts_ctx, &structure);

            (body, aborts)
        };

        let functions =
            function_translator::build_function(self, &target, variables, signature, body, aborts);

        let mut iter = functions.into_iter();
        let main_func = iter
            .next()
            .expect("build_function must produce at least one function");
        self.program.functions.create(qualified_id, main_func);
        for func in iter {
            self.program.functions.add(func);
        }
    }

    pub fn convert_type(&mut self, ty: &MoveType) -> Type {
        use move_model::ty::PrimitiveType;
        match ty {
            MoveType::Primitive(PrimitiveType::Bool) => Type::Bool,
            MoveType::Primitive(PrimitiveType::U8) => Type::UInt(8),
            MoveType::Primitive(PrimitiveType::U16) => Type::UInt(16),
            MoveType::Primitive(PrimitiveType::U32) => Type::UInt(32),
            MoveType::Primitive(PrimitiveType::U64) => Type::UInt(64),
            MoveType::Primitive(PrimitiveType::U128) => Type::UInt(128),
            MoveType::Primitive(PrimitiveType::U256) => Type::UInt(256),
            MoveType::Primitive(PrimitiveType::Address | PrimitiveType::Signer) => Type::Address,
            MoveType::Datatype(mid, sid, args) => {
                let qualified_id = mid.qualified(*sid);
                self.convert_datatype(qualified_id, args)
            }
            MoveType::Vector(t) => Type::Vector(Box::new(self.convert_type(t))),
            MoveType::Reference(is_mutable, t) => {
                let inner = Box::new(self.convert_type(t));
                if *is_mutable {
                    // State type is unknown at conversion time; filled in by finalize()
                    Type::MutableReference(inner.clone(), inner)
                } else {
                    Type::Reference(inner)
                }
            }
            MoveType::TypeParameter(idx) => Type::TypeParameter(*idx),
            MoveType::Tuple(ts) => Type::Tuple(ts.iter().map(|t| self.convert_type(t)).collect()),
            _ => unreachable!("Unsupported type: {:?}", ty),
        }
    }

    /// Convert a datatype (struct or enum) to TheoremType
    fn convert_datatype(
        &mut self,
        qualified_id: QualifiedId<DatatypeId>,
        args: &[MoveType],
    ) -> Type {
        let module_env = self.env.get_module(qualified_id.module_id);
        let symbol = qualified_id.id.symbol();

        // Create the struct type (this handles enums gracefully by creating a dummy struct)
        Type::Struct {
            struct_id: self.struct_id(qualified_id),
            type_args: args.iter().map(|a| self.convert_type(a)).collect(),
        }
    }

    pub(crate) fn symbol_str(&self, sym: Symbol) -> Rc<String> {
        self.env.symbol_pool().string(sym)
    }
}

/// Check if a function is a spec_only loop invariant (#[spec_only(loop_inv(...))]).
/// These are logical assertions that may contain forall!/exists! and should return Prop.
fn is_spec_only_loop_inv(func_env: &move_model::model::FunctionEnv) -> bool {
    use move_compiler::shared::known_attributes::{
        AttributeKind_, KnownAttribute, VerificationAttribute,
    };
    if let Some(attr) = func_env
        .get_toplevel_attributes()
        .get_(&AttributeKind_::SpecOnly)
    {
        if let KnownAttribute::Verification(VerificationAttribute::SpecOnly { loop_inv, .. }) =
            &attr.value
        {
            return loop_inv.is_some();
        }
    }
    false
}

/// For a `#[spec_only(loop_inv(target=...))]` function, return the bare name of
/// the target function whose loop this invariant guards (the last `::` segment
/// of the attribute's `target` ModuleAccess). `None` if the function carries no
/// loop_inv attribute.
fn loop_inv_target_name(func_env: &move_model::model::FunctionEnv) -> Option<String> {
    use move_compiler::shared::known_attributes::{
        AttributeKind_, KnownAttribute, VerificationAttribute,
    };
    let attr = func_env
        .get_toplevel_attributes()
        .get_(&AttributeKind_::SpecOnly)?;
    if let KnownAttribute::Verification(VerificationAttribute::SpecOnly { loop_inv, .. }) =
        &attr.value
    {
        let info = loop_inv.as_ref()?;
        let full = info.target.to_string();
        // ModuleAccess renders as `module::function` (or just `function`);
        // the while-helper emitter keys off the bare target function name.
        let bare = full.rsplit("::").next().unwrap_or(full.as_str());
        return Some(bare.to_string());
    }
    None
}
