// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Intermediate Theorem Format (TheoremIR)

pub mod analysis;
pub mod data;
pub mod utils;

pub use analysis::optimize;
pub use analysis::remove_dead_code;
pub use analysis::{validate_program, ValidationError};
pub use data::functions::{
    Function, FunctionID, FunctionSignature, Parameter, ProofParam, ProofParamType, TestExpectation,
};
pub use data::ir::{AbortSource, BinOp, BitOp, Const, IRNode, QuantifierKind, UnOp, WriteBackEdge};
pub use data::structure::{Field, Struct, Variant};
pub use data::types::{TempId, Type};
pub use data::variables::VariableRegistry;
pub use data::{BuildMode, LoopInvHyp, Module, Program};
pub use data::{ModuleID, StructID};
