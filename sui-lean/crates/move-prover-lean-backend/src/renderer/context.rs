// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Rendering context - shared state during IR rendering

use super::lean_writer::LeanWriter;
use intermediate_theorem_format::{FunctionID, ModuleID, Program, TempId};
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Write;

/// Rendering context - holds everything needed during rendering
pub struct RenderCtx<'a, W: Write> {
    pub program: &'a Program,
    pub current_module_id: ModuleID,
    pub current_module_namespace: Option<&'a str>,
    pub type_params: Option<&'a [String]>,
    pub writer: LeanWriter<W>,
    /// When set, MutableReference(T, _) renders as Mutable (T) <state_var> instead of using the stored state type.
    /// Used when rendering function parameter types that are &mut (where state is a type variable).
    pub mutable_state_var: Option<String>,
    /// Module IDs that have been merged into the current module (for merged impl+spec modules).
    /// Calls to functions in these modules should not be namespace-qualified.
    pub merged_module_ids: HashSet<ModuleID>,
    /// Mutual group ID of the current function (if any), plus parameter names.
    /// Used to detect all-fixed recursive calls and wrap an argument in `id`.
    pub mutual_group_info: Option<(usize, Vec<String>)>,
    /// Temporary overrides for variable rendering. When set, Var(name) renders as the
    /// override string instead of the escaped name.
    pub var_overrides: HashMap<TempId, String>,
    /// The escaped name of the function currently being rendered.
    pub current_function_name: String,
    /// The `FunctionID` of the function currently being rendered. ID-keyed (not
    /// name-keyed) so the callee-`requires` PRECOND render path can distinguish a
    /// threaded caller from a same-named cross-module twin (the `render.rs:360`
    /// collision the precond set was made ID-keyed to avoid).
    pub current_function_id: Option<FunctionID>,
    /// Escaped parameter names of the function currently being rendered.
    /// The loop-invariant entry cascade passes them to the user `loop_entry`
    /// lemma when discharging the entry call.
    pub current_function_params: Vec<String>,
    /// When rendering a branch of a dependent `if h : cond` introduced for a
    /// loop-invariant entry call, holds `h`'s name so the entry call can pass it
    /// to the `loop_entry` lemma. Counter disambiguates nested dependent ifs.
    pub entry_hyp: Option<String>,
    pub entry_hyp_counter: usize,
    /// Escaped names of all functions in the current mutual group (if any).
    /// Used to detect when a call to a non-mutual function would be misinterpreted
    /// as field access on a mutual-group function (e.g., `while_0.after` parsed as
    /// `(while_0).after` when `while_0` is in the mutual block).
    pub mutual_group_func_names: Vec<String>,
    /// Temps holding a `Mutable` borrowed from `dynamic_object_field::borrow_mut`
    /// (native, UID-anchored). A `WriteBackEdge::Field` whose child is in this set
    /// must keep the `{ parent with id := Mutable.apply child }` form and NOT be
    /// collapsed to `Mutable.apply child`. Populated per function before its body
    /// is rendered.
    pub object_field_borrow_children: HashSet<TempId>,
}

impl<'a, W: Write> RenderCtx<'a, W> {
    pub fn new(
        program: &'a Program,
        current_module_id: ModuleID,
        current_module_namespace: Option<&'a str>,
        writer: LeanWriter<W>,
        merged_module_ids: HashSet<ModuleID>,
    ) -> Self {
        Self {
            program,
            current_module_id,
            current_module_namespace,
            type_params: None,
            writer,
            mutable_state_var: None,
            merged_module_ids,
            mutual_group_info: None,
            var_overrides: HashMap::new(),
            current_function_name: String::new(),
            current_function_id: None,
            current_function_params: Vec::new(),
            entry_hyp: None,
            entry_hyp_counter: 0,
            mutual_group_func_names: Vec::new(),
            object_field_borrow_children: HashSet::new(),
        }
    }

    /// Set the current function's type parameters for rendering
    pub fn with_type_params(&mut self, type_params: &'a [String]) {
        self.type_params = Some(type_params);
    }

    /// Write a string to the writer
    pub fn write(&mut self, s: &str) {
        self.writer.write(s);
    }

    /// Write a line to the writer
    pub fn line(&mut self, s: &str) {
        self.writer.line(s);
    }

    /// Write a newline
    pub fn newline(&mut self) {
        self.writer.newline();
    }

    /// Increase indentation. If `newline` is true, writes a newline before indenting.
    pub fn indent(&mut self, newline: bool) {
        self.writer.indent(newline);
    }

    /// Decrease indentation. If `newline` is true, writes a newline after dedenting.
    pub fn dedent(&mut self, newline: bool) {
        self.writer.dedent(newline);
    }

    /// Check if in inline mode
    pub fn is_inline(&self) -> bool {
        self.writer.is_inline()
    }

    /// Write items with a separator, using a render function
    pub fn sep_with<I, T, F>(&mut self, separator: &str, items: I, mut render: F)
    where
        I: IntoIterator<Item = T>,
        F: FnMut(&mut Self, T),
    {
        let mut first = true;
        for item in items {
            if !first {
                self.write(separator);
            }
            first = false;
            render(self, item);
        }
    }

    /// Write a tuple-like structure: empty→empty_val, single→element, multiple→`(a, b, c)`
    pub fn tuple<I, T, F>(&mut self, items: I, empty_val: &str, mut render: F)
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
        F: FnMut(&mut Self, T),
    {
        let iter = items.into_iter();
        let len = iter.len();
        match len {
            0 => self.write(empty_val),
            1 => {
                for item in iter {
                    render(self, item);
                }
            }
            _ => {
                self.write("(");
                self.sep_with(", ", iter, &mut render);
                self.write(")");
            }
        }
    }

    /// Get the underlying writer
    pub fn into_writer(self) -> LeanWriter<W> {
        self.writer
    }
}
