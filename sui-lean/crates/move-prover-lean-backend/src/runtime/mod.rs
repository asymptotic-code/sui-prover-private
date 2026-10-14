// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Runtime execution of Lean/Lake

pub mod lake_wrapper;

pub use lake_wrapper::{
    resolve_audit_lake_executable, resolve_audit_lean_executable, run_audit_lake_command,
    run_audit_lean_command, run_lake_build, run_lake_build_targets, run_lake_command,
};
