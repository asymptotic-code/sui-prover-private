// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Variable Registry - type information for IR nodes
//!
//! Variables are identified by TempId (string names like "$t0", "x", etc.)

use crate::data::structure::StructID;
use crate::data::types::{TempId, Type};
use crate::{IRNode, Program};
use std::collections::BTreeMap;

/// Maps variable names (TempId) to their types.
/// Holds a reference to the Program for looking up function return types
/// and struct field types when registering variables from IR nodes.
#[derive(Clone)]
pub struct VariableRegistry<'a> {
    variables: BTreeMap<TempId, Type>,
    program: &'a Program,
}

impl<'a> VariableRegistry<'a> {
    pub fn new(variables: BTreeMap<TempId, Type>, program: &'a Program) -> Self {
        Self { variables, program }
    }

    /// Get the type for a variable by name. Panics if not found.
    pub fn get_type(&self, name: &str) -> &Type {
        self.variables.get(name).unwrap_or_else(|| {
            panic!(
                "Variable '{}' not found in registry. Available: {:?}",
                name,
                self.variables.keys().collect::<Vec<_>>()
            )
        })
    }

    /// Register a variable with its type
    pub fn register(&mut self, name: TempId, ty: Type) {
        self.variables.insert(name, ty);
    }

    /// Check if a variable is registered
    pub fn contains(&self, name: &str) -> bool {
        self.variables.contains_key(name)
    }

    /// Iterate over all variables (name, type)
    pub fn iter(&self) -> impl Iterator<Item = (&TempId, &Type)> {
        self.variables.iter()
    }

    pub fn len(&self) -> usize {
        self.variables.len()
    }

    /// Check if a name is a temp variable (starts with '$')
    pub fn is_temp(name: &str) -> bool {
        name.starts_with('$')
    }

    /// Register variables from a pattern + value type.
    /// Single pattern: register directly. Tuple pattern: destructure element types.
    pub fn register_pattern(&mut self, pattern: &[TempId], val_type: Type) {
        if pattern.is_empty() {
            return;
        }
        if pattern.len() == 1 {
            self.variables.insert(pattern[0].clone(), val_type);
        } else if let Type::Tuple(elem_types) = &val_type {
            assert_eq!(
                pattern.len(),
                elem_types.len(),
                "Pattern arity {} does not match tuple arity {} — pattern={:?} val_type={:?}",
                pattern.len(),
                elem_types.len(),
                pattern,
                val_type,
            );
            for (name, ty) in pattern.iter().zip(elem_types.iter()) {
                self.variables.insert(name.clone(), ty.clone());
            }
        } else {
            panic!(
                "Multi-element pattern {:?} bound to non-Tuple type {:?}",
                pattern, val_type
            );
        }
    }

    /// Extend the registry with a Let's pattern bindings, computing the value
    /// type in the CURRENT scope (without the new pattern in scope yet).
    /// The caller is responsible for ensuring the value only references
    /// variables already in scope — this is the incremental-scope contract
    /// that top-down traversals in analysis passes rely on.
    pub fn add_node(&mut self, node: &IRNode) {
        let IRNode::Let { pattern, value, .. } = node else {
            return;
        };
        if pattern.is_empty() {
            return;
        }
        let val_type = value.get_type(self);
        self.register_pattern(pattern, val_type);
    }

    pub fn function_return_type(&self, base_id: usize) -> &Type {
        &self.program.functions.get(&base_id).signature.return_type
    }

    pub fn struct_field_type(&self, struct_id: StructID, field_index: usize) -> &Type {
        let s = self.program.structs.get(struct_id);
        &s.fields
            .get(field_index)
            .unwrap_or_else(|| panic!("Field {} not found in struct {}", field_index, s.name))
            .field_type
    }

    pub fn struct_fields_tuple(&self, struct_id: StructID) -> Type {
        let s = self.program.structs.get(struct_id);
        Type::Tuple(s.fields.iter().map(|f| f.field_type.clone()).collect())
    }

    pub fn program(&self) -> &Program {
        self.program
    }
}
