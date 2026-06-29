// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Spec type conversion system
//!
//! This pass generates conversion functions for types that have spec representations.
//! For example, I32 (implementation) can have Int (spec) as its spec representation.
//!
//! The system works by:
//! 1. Finding struct types that should have spec representations (e.g., I32, I128)
//! 2. Generating conversion functions (axioms) that user can later prove
//! 3. Registering these conversions in the Program's ConversionRegistry

use crate::Program;

/// Generate conversion functions for types that need spec representations
pub fn generate_spec_type_conversions(program: &mut Program) {
    // Register int_ops conversion functions that already exist
    // These are native functions from the int_ops module
    register_int_ops_conversions(program);
}

/// Register int_ops conversion functions in the conversion registry
fn register_int_ops_conversions(_program: &mut Program) {
    // No conversions to register - Move doesn't have built-in signed integer types.
    // I32/I128 are library types that handle their own conversions if needed.
}
