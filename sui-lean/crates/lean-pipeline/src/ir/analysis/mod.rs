//! IR-level analyses and transformations shared across stages.
//!
//! - `scope`     -- scope-tracking traversals (binding discipline):
//!   the set-flavor `ScopeObserver`/`ScopeWalker` and the typed
//!   `TypedScopeVisitor`/`TypedScopeMutVisitor`. `free_vars` and the
//!   stage-10 / baseline typed passes sit on top of these.
//! - `free_vars` -- compute free variables of a `Block` or `Expr`.
//! - `type_of`   -- infer the `Type` of an `Expr` in a scope.
//! - `extract`   -- lift a `Block` into its own `Function`.
//!
//! These primitives sit one level above the raw IR data shapes
//! (`expr.rs`, `function.rs`, ...) and one level below stage-specific
//! transformations. Stage 7 (loops + continuations extraction) is the
//! main consumer.

pub mod extract;
pub mod free_vars;
pub mod scope;
pub mod type_of;

pub use extract::{extract_block, ExtractError, ExtractSpec};
pub use free_vars::{free_vars, free_vars_of_expr};
pub use type_of::{block_value_type, substitute_type_params, type_of, TypeOfError};
