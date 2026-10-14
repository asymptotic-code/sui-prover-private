// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Struct IR data structures

use crate::data::types::Type;
use crate::data::Dependable;
use crate::ModuleID;
use move_model::model::{DatatypeId, QualifiedId};
use std::rc::Rc;

/// Unique identifier for a struct in the program
pub type StructID = usize;

#[derive(Debug, Clone)]
pub struct Struct {
    pub module_id: ModuleID,
    pub name: String,
    pub qualified_name: String,
    pub type_params: Vec<Rc<String>>,
    pub fields: Vec<Field>,
    pub mutual_group_id: Option<usize>,
    /// For enums: the variants. None for regular structs.
    pub variants: Option<Vec<Variant>>,
}

#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub field_type: Type,
}

/// An enum variant with its fields
#[derive(Debug, Clone)]
pub struct Variant {
    pub name: String,
    pub tag: usize,
    pub fields: Vec<Field>,
}

impl Dependable for Struct {
    type Id = StructID;
    type MoveKey = QualifiedId<DatatypeId>;

    fn dependencies(&self) -> impl Iterator<Item = Self::Id> {
        // Include dependencies from both struct fields and enum variant fields
        let field_deps = self
            .fields
            .iter()
            .flat_map(|field| field.field_type.struct_ids());
        let variant_deps = self
            .variants
            .iter()
            .flatten()
            .flat_map(|variant| variant.fields.iter())
            .flat_map(|field| field.field_type.struct_ids());
        field_deps.chain(variant_deps)
    }

    fn with_recursion_info(mut self, mutual_group_id: Option<usize>, _is_recursive: bool) -> Self {
        self.mutual_group_id = mutual_group_id;
        self
    }

    fn get_mutual_group_id(&self) -> Option<usize> {
        self.mutual_group_id
    }
}
