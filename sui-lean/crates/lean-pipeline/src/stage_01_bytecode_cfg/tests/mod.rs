//! Stage-1 fixtures, grouped by what they exercise.
//!
//! Helpers are minimal on purpose: `cfg(builder)` runs the structurer
//! and `root(cfg)` extracts the root region. Each fixture file uses
//! pattern matching on `Region` directly; the IR is small enough that
//! `assert_matches!`-style coverage is more readable than snapshot-based
//! coverage.

#![cfg(test)]

mod break_continue;
mod control_flow;
mod loops;
mod reject;

use super::structurer;
use super::test_support::BytecodeBuilder;
use super::{BytecodeCfg, Region, Stage1Error};

/// Run the structurer on `builder`'s output. Returns the produced
/// `BytecodeCfg` or the structurer's error.
pub(crate) fn cfg_from(builder: BytecodeBuilder) -> Result<BytecodeCfg, Stage1Error> {
    let code = builder.finish();
    structurer::run_from_code(&code)
}

/// Convenience: panic on error and unwrap the root region.
pub(crate) fn root_of(builder: BytecodeBuilder) -> Region {
    cfg_from(builder).expect("structurer should succeed").root
}
