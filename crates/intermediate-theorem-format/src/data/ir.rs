// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Unified Intermediate Representation (IR) for TheoremIR
//!
//! This module provides a single recursive type that represents all program constructs.
//! In a functional language like Lean, everything is an expression - a "block" is just
//! nested let bindings, and "statements" are just expressions with effects.
//!
//! ## Design Principles
//!
//! 1. **Single recursive type**: No separate Statement/Expression/Block types
//! 2. **Simple traversal**: `children()`, `map()`, `fold()` work uniformly

use crate::data::structure::StructID;
use crate::data::types::{TempId, Type};
use crate::data::variables::VariableRegistry;
use crate::FunctionID;
use ethnum::U256;
use num::BigUint;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fmt::{Display, Formatter};
use std::rc::Rc;
use std::{fmt, mem};

/// Traverse child IR nodes of an IR expression.
/// Uses tt for actions to expand inline, avoiding closure lifetime issues.
/// Pass `as_ir_ref` for immutable access, `as_ir_mut` for mutable access.
macro_rules! traverse_ir {
    ($target:expr, $deref:ident, |$value:ident| $action:expr) => {
        match $target {
            IRNode::Var(_) | IRNode::Const(_) => {}
            IRNode::BinOp { lhs, rhs, .. } => {
                let $value = lhs.$deref();
                $action;
                let $value = rhs.$deref();
                $action;
            }
            IRNode::UnOp { operand, .. } => {
                let $value = operand.$deref();
                $action;
            }
            IRNode::BitOp(bit_op) => match bit_op {
                BitOp::Extract { operand, .. } => {
                    let $value = operand.$deref();
                    $action;
                }
                BitOp::Concat { high, low } => {
                    let $value = high.$deref();
                    $action;
                    let $value = low.$deref();
                    $action;
                }
                BitOp::ZeroExtend { operand, .. } | BitOp::SignExtend { operand, .. } => {
                    let $value = operand.$deref();
                    $action;
                }
            },
            IRNode::Call { args, .. } => {
                for $value in args {
                    $action;
                }
            }
            IRNode::Pack { fields, .. } => {
                for $value in fields {
                    $action;
                }
            }
            IRNode::Field { base, .. } => {
                let $value = base.$deref();
                $action;
            }
            IRNode::Unpack { value, .. } => {
                let $value = value.$deref();
                $action;
            }
            IRNode::Tuple(elems) => {
                for $value in elems {
                    $action;
                }
            }
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let $value = cond.$deref();
                $action;
                let $value = then_branch.$deref();
                $action;
                let $value = else_branch.$deref();
                $action;
            }
            IRNode::Match {
                scrutinee, cases, ..
            } => {
                let $value = scrutinee.$deref();
                $action;
                for (_, _, body) in cases {
                    let $value = body;
                    $action;
                }
            }
            IRNode::Let { value, body, .. } => {
                let $value = value.$deref();
                $action;
                let $value = body.$deref();
                $action;
            }
            IRNode::UpdateField { base, value, .. } => {
                let $value = base.$deref();
                $action;
                let $value = value.$deref();
                $action;
            }
            IRNode::UpdateVec { base, index, value } => {
                let $value = base.$deref();
                $action;
                let $value = index.$deref();
                $action;
                let $value = value.$deref();
                $action;
            }
            IRNode::MutableBorrow {
                val_expr,
                reconstruct_expr,
                ..
            } => {
                let $value = val_expr.$deref();
                $action;
                let $value = reconstruct_expr.$deref();
                $action;
            }
            IRNode::ReadRef(inner) => {
                let $value = inner.$deref();
                $action;
            }
            IRNode::WriteRef { reference, value } => {
                let $value = reference.$deref();
                $action;
                let $value = value.$deref();
                $action;
            }
            IRNode::Quantifier {
                callback,
                collection,
                range,
                ..
            } => {
                let $value = callback.$deref();
                $action;
                if let Some(coll) = collection {
                    let $value = coll.$deref();
                    $action;
                }
                if let Some((start, end)) = range {
                    let $value = start.$deref();
                    $action;
                    let $value = end.$deref();
                    $action;
                }
            }

            IRNode::ToProp(inner) => {
                let $value = inner.$deref();
                $action;
            }
            IRNode::ToBool(inner) => {
                let $value = inner.$deref();
                $action;
            }
            IRNode::OptionSome(inner) => {
                let $value = inner.$deref();
                $action;
            }
            IRNode::OptionNone
            | IRNode::Inhabited
            | IRNode::WriteBack { .. }
            | IRNode::MutableCompose { .. } => {}
            IRNode::Abort { code } => {
                if let Some(code) = code {
                    let $value = code.$deref();
                    $action;
                }
            }
            IRNode::MoveAbortValue { code, .. } => {
                let $value = code.$deref();
                $action;
            }
            IRNode::MatchOption {
                scrutinee,
                some_branch,
                none_branch,
                ..
            } => {
                let $value = scrutinee.$deref();
                $action;
                let $value = some_branch.$deref();
                $action;
                let $value = none_branch.$deref();
                $action;
            }
            IRNode::ArithOverflowCheck { lhs, rhs, .. } => {
                let $value = lhs.$deref();
                $action;
                let $value = rhs.$deref();
                $action;
            }
        }
    };
}

// ============================================================================
// Core IR Type
// ============================================================================

/// The unified IR type. Everything is an expression.
#[derive(Debug, Clone, PartialEq)]
pub enum IRNode {
    // === Atoms ===
    /// Variable reference by name
    Var(TempId),

    /// Constant value
    Const(Const),

    // === Compound Expressions ===
    /// Binary operation: lhs op rhs
    BinOp {
        op: BinOp,
        lhs: Box<IRNode>,
        rhs: Box<IRNode>,
    },

    /// Unary operation: op operand
    UnOp { op: UnOp, operand: Box<IRNode> },

    /// Bit-level operation (extract, concat, extend)
    BitOp(BitOp),

    /// Function call: function(args)
    Call {
        function: FunctionID,
        type_args: Vec<Type>,
        args: Vec<IRNode>,
    },

    /// Struct/enum construction: StructName { fields... } or EnumName.Variant { fields... }
    Pack {
        struct_id: StructID,
        type_args: Vec<Type>,
        fields: Vec<IRNode>,
        /// For enum variant packing, the variant index. None for regular struct packing.
        variant_index: Option<usize>,
    },

    /// Field access: struct.field
    Field {
        struct_id: StructID,
        field_index: usize,
        base: Box<IRNode>,
    },

    /// Struct/enum destructuring: let (f1, f2, ...) = struct
    Unpack {
        struct_id: StructID,
        value: Box<IRNode>,
        /// For enum variant unpacking, the variant index (None for regular structs)
        variant_index: Option<usize>,
    },

    /// Tuple: (a, b, c) or unit ()
    Tuple(Vec<IRNode>),

    /// Let binding: let pattern = value in body
    Let {
        /// Variable names to bind (empty = wildcard, single = simple, multiple = tuple)
        pattern: Vec<TempId>,
        /// The value being bound
        value: Box<IRNode>,
        /// The body where the binding is in scope
        body: Box<IRNode>,
    },

    // === Control Flow (all produce values) ===
    /// Conditional: if cond then t else e
    If {
        cond: Box<IRNode>,
        then_branch: Box<IRNode>,
        else_branch: Box<IRNode>,
    },

    /// Match on enum variant: match scrutinee with cases
    /// Used for pattern matching on Move enums (VariantSwitch bytecode)
    Match {
        scrutinee: Box<IRNode>,
        cases: Vec<(usize, Vec<TempId>, IRNode)>,
    },

    // === Effects ===
    /// Field update: { struct with field = value }
    UpdateField {
        base: Box<IRNode>,
        struct_id: StructID,
        field_index: usize,
        value: Box<IRNode>,
    },

    /// Vector element update: vec.set(index, value)
    UpdateVec {
        base: Box<IRNode>,
        index: Box<IRNode>,
        value: Box<IRNode>,
    },

    /// Mutable borrow: creates a Mutable { val, reconstruct } wrapper
    /// val_expr: the expression to get the borrowed value
    /// reconstruct_param: the parameter name for the reconstruct lambda
    /// reconstruct_expr: expression that rebuilds the parent with the new value
    /// state_type: the type of the parent state being reconstructed
    MutableBorrow {
        val_expr: Box<IRNode>,
        reconstruct_param: TempId,
        reconstruct_expr: Box<IRNode>,
        state_type: Type,
    },

    /// Read through a mutable reference: ref.val
    ReadRef(Box<IRNode>),

    /// Write through a mutable reference: ref.reconstruct(value)
    WriteRef {
        reference: Box<IRNode>,
        value: Box<IRNode>,
    },

    // === Quantifiers / Collection Operations ===
    /// Quantifier or collection operation from Move spec macros.
    /// Translates to Lean helpers like spec_forall, spec_any, spec_find_index, etc.
    Quantifier {
        kind: QuantifierKind,
        /// The callback function (already translated as an IR Call node with placeholder args).
        /// This is a call to the callback where the lambda parameter position contains
        /// Var("__qi") as a placeholder.
        callback: Box<IRNode>,
        /// Name of the lambda parameter (bound variable)
        lambda_param: TempId,
        /// Type of the lambda parameter
        lambda_type: Type,
        /// For vector-based: the vector expression. None for non-vector (Forall/Exists).
        collection: Option<Box<IRNode>>,
        /// For range-based: (start, end) expressions
        range: Option<(Box<IRNode>, Box<IRNode>)>,
    },

    // === Type Coercions ===
    /// Convert Bool to Prop: lifts a computational boolean to a proposition
    /// Rendered as: (expr = true) in Lean
    ToProp(Box<IRNode>),

    /// Convert Prop to Bool: requires Decidable, converts proposition to boolean
    /// Rendered as: decide expr in Lean
    ToBool(Box<IRNode>),

    // === Option encoding (for while-loop early return) ===
    /// Option.some value: wraps a value in Some for early return encoding
    OptionSome(Box<IRNode>),
    /// Option.none: represents no early return
    OptionNone,
    /// Match on Option: match scrutinee with | some binding => some_branch | none => none_branch
    MatchOption {
        scrutinee: Box<IRNode>,
        binding: TempId,
        some_branch: Box<IRNode>,
        none_branch: Box<IRNode>,
    },

    /// Placeholder for phi variables that are only defined in one branch.
    /// Renders as `default` in Lean (requires `Inhabited` instance).
    Inhabited,

    /// Abort path: Move `abort` was called.
    ///
    /// `code` is the integer abort code (typically a `Var` referencing a u64 temp,
    /// or a `Const::UInt`). The Spec render path discards the code and emits
    /// `sorry` (the existing proof-side semantics). The Exec render path will
    /// instead emit `MoveAbort.raiseAssert <code>` so test execution can
    /// observe the actual abort code.
    ///
    /// `code` may be `None` for compiler-synthesised abort sites that have no
    /// source-level code temp (e.g. some early-return-elimination edges where
    /// the abort is reached through a Boolean predicate but the original code
    /// was already consumed). Renderers should treat `None` like the legacy
    /// behaviour: `sorry` in Spec mode, `MoveAbort.raiseAssert 0` in Exec mode.
    Abort { code: Option<Box<IRNode>> },

    /// Write-back from a child mutable borrow to its parent.
    /// Translated from `Operation::WriteBack(BorrowNode, BorrowEdge)` in
    /// the Move bytecode. The `edge` carries the upstream borrow path so
    /// the renderer can reconstruct the parent correctly:
    /// - `WriteBackEdge::Direct`: legacy form. Render as `Mutable.set
    ///   parent (Mutable.apply child)` / `Mutable.apply child` / etc.
    ///   based on parent / child Mutable-ness.
    /// - `WriteBackEdge::Field { struct_id, field_index }`: render as
    ///   `{ parent with <field> := Mutable.apply child }` (or `child` if
    ///   plain). Used for dynamic-field-on-Sui-object cases where the
    ///   child borrow's outer is a struct field of the parent.
    WriteBack {
        child: TempId,
        parent: TempId,
        edge: WriteBackEdge,
    },

    /// Compose two Mutable write-back chains.
    /// Rendered as `Mutable.compose inner outer`.
    /// `inner : Mutable V Mid`, `outer : Mutable Mid Top` → `Mutable V Top`
    MutableCompose { inner: TempId, outer: TempId },

    /// Construct a `MoveAbort { source := <source>, code := <code> }` literal.
    /// Used by the test-mode `.aborts` lowering, where `.aborts` returns
    /// `Option MoveAbort` and the runtime driver inspects the verdict.
    /// `code` is an integer-typed expression; the renderer wraps it with
    /// `.toNat` to match the `Nat` field type.
    MoveAbortValue {
        source: AbortSource,
        code: Box<IRNode>,
    },

    /// Bool-valued check whether a Move arithmetic op would abort. Lowered
    /// by the renderer to a `BoundedNat` prelude helper:
    /// - `BinOp::Add` -> `BoundedNat.add_overflows`
    /// - `BinOp::Sub` -> `BoundedNat.sub_underflows`
    /// - `BinOp::Mul` -> `BoundedNat.mul_overflows`
    ///
    /// Emitted only by `inject_arithmetic_aborts`; never produced by
    /// translation. Other arithmetic-abort conditions (div-by-zero,
    /// shift-width, narrowing-cast) are expressible inline via comparisons
    /// against bound-derived constants and don't need a dedicated node.
    ArithOverflowCheck {
        op: BinOp,
        lhs: Box<IRNode>,
        rhs: Box<IRNode>,
    },
}

/// Source tag for a `MoveAbort` value. Mirrors the Lean
/// `MoveAbort.AbortSource` inductive in `Prelude/MoveAbort.lean`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbortSource {
    /// Move-source `assert!(_, code)` failure.
    UserAssert,
    /// Implicit arithmetic abort (overflow, div-by-zero, narrowing cast).
    Arithmetic,
}

/// How a child borrow's `WriteBack` reaches its parent. Mirrors the subset
/// of upstream `move_stackless_bytecode::stackless_bytecode::BorrowEdge` we
/// can act on at render time. The renderer dispatches on this to produce
/// the correct reconstruction:
///
/// - `Direct`: the legacy form. Parent and child are at the same level
///   (no field reconstruction needed). Renderer falls back to the existing
///   `Mutable.apply` / `Mutable.set` logic based on parent / child types.
///
/// - `Field { struct_id, field_index }`: the child's `Mutable.apply` result
///   is the new value of `parent.<field>`. Renderer emits
///   `{ parent with <field> := Mutable.apply child }` (or `child` if plain).
///   This is what fixes the dynamic-field-on-Sui-object cases (Reserve,
///   Asset, Pending_values, etc.) where the upstream WriteBack carries a
///   `Hyper([DynamicField, Index])` edge that, after the lean-backend's
///   dynamic-field rewriting, collapses to "update parent's `id` field
///   with the new UID".
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WriteBackEdge {
    Direct,
    Field {
        struct_id: StructID,
        field_index: usize,
    },
}

impl Default for WriteBackEdge {
    fn default() -> Self {
        WriteBackEdge::Direct
    }
}

/// Constant values
#[derive(Debug, Clone, PartialEq)]
pub enum Const {
    Bool(bool),
    UInt {
        bits: usize,
        value: U256,
    },
    Address(BigUint),
    /// Vector constant with element type and values
    Vector {
        elem_type: Type,
        elems: Vec<Const>,
    },
}

impl Display for Const {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Const::Bool(b) => write!(f, "{}", if *b { "true" } else { "false" }),
            Const::UInt { value, .. } => write!(f, "{}", value),
            Const::Address(addr) => write!(f, "{}", addr),
            Const::Vector { elems, .. } => {
                write!(f, "[")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", e)?;
                }
                write!(f, "]")
            }
        }
    }
}

/// Binary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    // Logical
    And,
    Or,
    // Comparison
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
}

impl BinOp {
    /// Returns true if this is a comparison operator (Lt, Le, Gt, Ge)
    /// Note: Eq and Neq are not included as they use BEq in Lean
    pub fn is_comparison(&self) -> bool {
        matches!(self, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
    }
}

/// Quantifier / collection operation kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantifierKind {
    Forall,
    Exists,
    Any,
    AnyRange,
    All,
    AllRange,
    FindIndex,
    FindIndexRange,
    RangeMap,
    Map,
    MapRange,
    Filter,
    FilterRange,
    Count,
    CountRange,
    Find,
    FindRange,
    FindIndices,
    FindIndicesRange,
    SumMap,
    SumMapRange,
    RangeCount,
    RangeSumMap,
}

/// Unary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not,
    BitNot,
    /// Cast to unsigned integer with specified bit width (8, 16, 32, 64, 128, 256)
    Cast(u32),
}

/// Bit-level operations (extract, concat, extend)
#[derive(Debug, Clone, PartialEq)]
pub enum BitOp {
    /// Extract bits [high:low] from operand
    Extract {
        high: u32,
        low: u32,
        operand: Box<IRNode>,
    },
    /// Concatenate high and low bitvectors
    Concat { high: Box<IRNode>, low: Box<IRNode> },
    /// Zero-extend by n bits
    ZeroExtend { bits: u32, operand: Box<IRNode> },
    /// Sign-extend by n bits
    SignExtend { bits: u32, operand: Box<IRNode> },
}

impl Default for IRNode {
    fn default() -> Self {
        IRNode::Tuple(vec![])
    }
}

impl IRNode {
    /// Create a unit value ()
    pub fn unit() -> IRNode {
        IRNode::Tuple(vec![])
    }

    /// Get references to all nodes (including itself) recursively in this IR tree
    /// Uses iterative approach with explicit stack to avoid stack overflow
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a IRNode> + 'a {
        let mut result = Vec::new();
        let mut stack = vec![self];

        while let Some(node) = stack.pop() {
            result.push(node);
            traverse_ir!(node, as_ir_ref, |child| stack.push(child));
        }

        result.into_iter()
    }

    /// Get references to direct children (depth 1) of this IR node
    pub fn iter_children<'a>(&'a self) -> impl Iterator<Item = &'a IRNode> + 'a {
        let mut result = Vec::new();
        traverse_ir!(self, as_ir_ref, |child| result.push(child));
        result.into_iter()
    }

    /// Transform only the DIRECT children (depth 1) of this node, replacing
    /// each with `f(child)`. Does NOT recurse — `f` is responsible for any
    /// deeper traversal. Use this when a top-down walk already dispatches on
    /// node kind and must not double-visit subtrees (the recursive `map`
    /// would walk every descendant *and* let the closure re-walk them).
    pub fn map_direct_children<F: FnMut(IRNode) -> IRNode>(mut self, mut f: F) -> IRNode {
        traverse_ir!(&mut self, as_ir_mut, |child| {
            let taken = mem::take(child);
            *child = f(taken);
        });
        self
    }

    /// Transform this IR recursively (bottom-up: children first, then parent)
    /// Uses an explicit work stack to avoid stack overflow on deep structures.
    pub fn map<F: FnMut(IRNode) -> IRNode>(self, f: &mut F) -> IRNode {
        // Work items for the stack-based traversal
        enum Work {
            // Process this node - will push children and a Rebuild work item
            Process(IRNode),
            // Rebuild this node from processed children
            Rebuild { node: IRNode, num_children: usize },
        }

        let mut work_stack = vec![Work::Process(self)];
        let mut result_stack: Vec<IRNode> = Vec::new();

        while let Some(work) = work_stack.pop() {
            match work {
                Work::Process(mut node) => {
                    // Count and collect children
                    let mut children = Vec::new();
                    traverse_ir!(&mut node, as_ir_mut, |value| {
                        children.push(mem::take(value));
                    });

                    // Push rebuild task (will execute after children are processed)
                    work_stack.push(Work::Rebuild {
                        node,
                        num_children: children.len(),
                    });

                    // Push children to be processed (reverse order so first is processed first)
                    for child in children.into_iter().rev() {
                        work_stack.push(Work::Process(child));
                    }
                }
                Work::Rebuild {
                    mut node,
                    num_children,
                } => {
                    // Pop processed children from result stack
                    let children: Vec<IRNode> = result_stack
                        .drain(result_stack.len() - num_children..)
                        .collect();

                    // Put children back into the node
                    let mut child_iter = children.into_iter();
                    traverse_ir!(&mut node, as_ir_mut, |value| {
                        *value = child_iter.next().expect("child count mismatch");
                    });

                    // Apply the transform function and push result
                    result_stack.push(f(node));
                }
            }
        }

        result_stack.pop().expect("empty result stack")
    }

    /// Fold over all IRNodes into a given structure
    pub fn fold<T, F>(&self, init: T, f: F) -> T
    where
        F: FnMut(T, &IRNode) -> T,
    {
        self.iter().fold(init, f)
    }

    /// Transform this IR top-down: apply f to each node first, then recurse
    /// into the RESULT's children. This means f can restructure a subtree and
    /// the children of the new structure will be further processed.
    ///
    /// Same signature as map() but top-down order.
    pub fn map_top_down<F: FnMut(IRNode) -> IRNode>(self, f: &mut F) -> IRNode {
        enum Work {
            Transform(IRNode),
            Rebuild { node: IRNode, num_children: usize },
        }

        let mut work_stack = vec![Work::Transform(self)];
        let mut result_stack: Vec<IRNode> = Vec::new();

        while let Some(work) = work_stack.pop() {
            match work {
                Work::Transform(node) => {
                    // Apply transform FIRST (top-down)
                    let mut transformed = f(node);

                    // Then recurse into the transformed node's children
                    let mut children = Vec::new();
                    traverse_ir!(&mut transformed, as_ir_mut, |value| {
                        children.push(mem::take(value));
                    });

                    work_stack.push(Work::Rebuild {
                        node: transformed,
                        num_children: children.len(),
                    });

                    for child in children.into_iter().rev() {
                        work_stack.push(Work::Transform(child));
                    }
                }
                Work::Rebuild {
                    mut node,
                    num_children,
                } => {
                    let children: Vec<IRNode> = result_stack
                        .drain(result_stack.len() - num_children..)
                        .collect();

                    let mut child_iter = children.into_iter();
                    traverse_ir!(&mut node, as_ir_mut, |value| {
                        *value = child_iter.next().expect("child count mismatch");
                    });

                    result_stack.push(node);
                }
            }
        }

        result_stack.pop().expect("empty result stack")
    }

    /// Check if this is an atomic expression (doesn't need parens when used as arg)
    pub fn is_atomic(&self) -> bool {
        matches!(self, IRNode::Var(_) | IRNode::Const(_) | IRNode::Tuple(_))
    }

    /// Extract and collect values from matching nodes in the IR tree
    /// The extractor function returns Some(T) for nodes that should be collected.
    pub fn extract<T, F>(&self, extractor: F) -> Vec<T>
    where
        F: Fn(&IRNode) -> Option<T>,
    {
        self.iter().filter_map(extractor).collect()
    }

    /// Collect all variable names used (read) in this IR tree.
    /// Excludes MutableBorrow reconstruct_param names since those are binders, not uses.
    pub fn used_vars(&self) -> impl Iterator<Item = &TempId> {
        let mut binder_params: Vec<&TempId> = Vec::new();
        for node in self.iter() {
            if let IRNode::MutableBorrow {
                reconstruct_param, ..
            } = node
            {
                binder_params.push(reconstruct_param);
            }
        }
        self.iter().flat_map(move |node| match node {
            IRNode::Var(name) if !binder_params.contains(&name) => vec![name].into_iter(),
            // WriteBack/MutableCompose store TempId strings, not IRNode children,
            // so iter()/iter_children() don't see them. Yield them explicitly.
            IRNode::WriteBack { child, parent, .. }
            | IRNode::MutableCompose {
                inner: child,
                outer: parent,
            } => vec![child, parent].into_iter(),
            _ => vec![].into_iter(),
        })
    }

    /// Collect all variable names defined (bound) in this IR tree
    pub fn defined_vars(&self) -> impl Iterator<Item = &TempId> {
        self.iter().flat_map(|node| match node {
            IRNode::Let { pattern, .. } => pattern.iter(),
            _ => [].iter(),
        })
    }

    /// Compute free variables - variables that are used before they are defined.
    /// This properly handles Let binding scope: a variable is free if it appears
    /// in a position where it hasn't been bound by an enclosing Let yet.
    pub fn free_vars(&self) -> BTreeSet<TempId> {
        let mut free = BTreeSet::new();
        let mut bound = BTreeSet::new();
        self.collect_free_vars(&mut free, &mut bound);
        free
    }

    /// Collect variables bound in the top-level sequential Let chain only.
    /// Does NOT descend into If/Match branches — only follows the straight-line
    /// `let x = ... in <body>` spine. This gives the variables that are truly
    /// in scope after this code runs, excluding branch-scoped temporaries.
    pub fn sequential_bindings(&self) -> BTreeSet<TempId> {
        let mut result = BTreeSet::new();
        let mut node = self;
        loop {
            match node {
                IRNode::Let { pattern, body, .. } => {
                    for v in pattern {
                        if v.as_ref() != "_" {
                            result.insert(v.clone());
                        }
                    }
                    node = body;
                }
                _ => break,
            }
        }
        result
    }

    /// Collect all variables that are bound (defined) anywhere in this expression.
    /// This includes variables in Let patterns, Match case bindings, etc.
    pub fn bindings(&self) -> BTreeSet<TempId> {
        let mut result = BTreeSet::new();
        self.collect_bindings(&mut result);
        result
    }

    /// Collect ALL variable references in this expression, ignoring binding scope.
    /// Unlike free_vars(), this includes ALL Var nodes regardless of whether they're bound.
    /// This is useful for detecting if a variable is used anywhere in the expression.
    pub fn all_var_refs(&self) -> BTreeSet<TempId> {
        let mut refs = BTreeSet::new();
        self.collect_all_var_refs(&mut refs);
        refs
    }

    fn collect_all_var_refs(&self, refs: &mut BTreeSet<TempId>) {
        match self {
            IRNode::Var(name) => {
                refs.insert(name.clone());
            }
            _ => {
                for child in self.iter_children() {
                    child.collect_all_var_refs(refs);
                }
            }
        }
    }

    fn collect_bindings(&self, bindings: &mut BTreeSet<TempId>) {
        match self {
            IRNode::Let {
                pattern,
                value,
                body,
            } => {
                for v in pattern {
                    if v.as_ref() != "_" {
                        bindings.insert(v.clone());
                    }
                }
                value.collect_bindings(bindings);
                body.collect_bindings(bindings);
            }
            IRNode::Match { scrutinee, cases } => {
                scrutinee.collect_bindings(bindings);
                for (_, case_bindings, body) in cases {
                    for v in case_bindings {
                        if v.as_ref() != "_" {
                            bindings.insert(v.clone());
                        }
                    }
                    body.collect_bindings(bindings);
                }
            }
            IRNode::MutableBorrow {
                val_expr,
                reconstruct_expr,
                ..
            } => {
                val_expr.collect_bindings(bindings);
                reconstruct_expr.collect_bindings(bindings);
            }
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => {
                cond.collect_bindings(bindings);
                then_branch.collect_bindings(bindings);
                else_branch.collect_bindings(bindings);
            }
            _ => {
                for child in self.iter_children() {
                    child.collect_bindings(bindings);
                }
            }
        }
    }

    /// Find variables that are unconditionally bound at the start of this expression
    /// before any branch or loop. These variables are always computed fresh at the
    /// start of each iteration, so they don't need initial values from outside.
    ///
    /// A variable qualifies as an "early binding" if:
    /// 1. It's defined at the start of the expression (before any If/Match/control flow)
    /// 2. Its definition value doesn't read the variable itself (no self-reference)
    pub fn early_bindings(&self, loop_params: &BTreeSet<TempId>) -> BTreeSet<TempId> {
        let mut early = BTreeSet::new();
        self.collect_early_bindings(&mut early, loop_params);
        early
    }

    /// Collect early bindings. Returns true if we should continue collecting.
    fn collect_early_bindings(
        &self,
        early: &mut BTreeSet<TempId>,
        loop_params: &BTreeSet<TempId>,
    ) -> bool {
        match self {
            // Let with non-empty pattern: binds variables, then continue
            IRNode::Let {
                pattern,
                value,
                body,
            } if !pattern.is_empty() => {
                // Check if the value reads any variables that:
                // 1. Are not loop parameters (external inputs)
                // 2. Are not already collected as early bindings
                // 3. Are not being defined by this very Let
                let value_free = value.free_vars();
                let pattern_set: BTreeSet<_> = pattern.iter().cloned().collect();
                let reads_problematic = value_free.iter().any(|v| {
                    !loop_params.contains(v) && !early.contains(v) && !pattern_set.contains(v)
                });
                if reads_problematic {
                    // This binding reads a variable that's not available yet
                    return false;
                }
                // Safe to add this binding - but only if it's not shadowing a loop parameter!
                // If a variable is in loop_params, it's a real loop variable that needs to be
                // passed in, even if it's re-assigned inside the loop.
                for v in pattern {
                    if v.as_ref() != "_" && !loop_params.contains(v) {
                        early.insert(v.clone());
                    }
                }
                body.collect_early_bindings(early, loop_params)
            }
            // Empty pattern Let is sequencing - continue collecting
            IRNode::Let {
                pattern,
                value,
                body,
            } if pattern.is_empty() => {
                // Process value first, then body
                let value_continued = value.collect_early_bindings(early, loop_params);
                if value_continued {
                    body.collect_early_bindings(early, loop_params)
                } else {
                    false
                }
            }
            // Unit/Const are OK - no reads, continue
            IRNode::Tuple(elems) if elems.is_empty() => true,
            IRNode::Const(_) => true,
            // If/Match/other control flow: stop collecting (not unconditional)
            _ => false,
        }
    }

    pub fn collect_free_vars(&self, free: &mut BTreeSet<TempId>, bound: &mut BTreeSet<TempId>) {
        match self {
            IRNode::Var(name) => {
                if !bound.contains(name) {
                    free.insert(name.clone());
                }
            }
            IRNode::Let {
                pattern,
                value,
                body,
            } => {
                if pattern.is_empty() {
                    // Empty pattern Let (created by IRNode::assign) is a sequencing construct.
                    // Bindings from value propagate to body - this is how we sequence
                    // statements while maintaining scope.
                    // We DON'T restore bound set after value because we want bindings to persist.
                    value.collect_free_vars(free, bound);
                    body.collect_free_vars(free, bound);
                } else {
                    // Non-empty pattern Let: evaluate value, bind pattern, evaluate body.
                    value.collect_free_vars(free, bound);
                    // Pattern variables are bound for the body
                    for v in pattern {
                        bound.insert(v.clone());
                    }
                    body.collect_free_vars(free, bound);
                    // DON'T restore - in our IR, let bindings persist through sequencing.
                    // The IR uses Let { pattern: [], value: ..., body: ... } to sequence
                    // statements, and bindings from value should persist to body.
                    // If body is Tuple([]), this is a "statement" let that's just for binding.
                }
            }
            IRNode::MutableBorrow {
                val_expr,
                reconstruct_param,
                reconstruct_expr,
                ..
            } => {
                val_expr.collect_free_vars(free, bound);
                // reconstruct_param is a binder for reconstruct_expr
                let was_bound = bound.contains(reconstruct_param);
                bound.insert(reconstruct_param.clone());
                reconstruct_expr.collect_free_vars(free, bound);
                if !was_bound {
                    bound.remove(reconstruct_param);
                }
            }
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => {
                cond.collect_free_vars(free, bound);
                // IMPORTANT: Each branch must use its own copy of bound, because bindings
                // in one branch should NOT affect the other branch. A variable defined in
                // the then_branch is NOT bound in the else_branch.
                let bound_before_if = bound.clone();
                let mut then_bound = bound.clone();
                let mut else_bound = bound.clone();
                then_branch.collect_free_vars(free, &mut then_bound);
                else_branch.collect_free_vars(free, &mut else_bound);
                // After the If, keep original bindings plus any NEW bindings from BOTH branches.
                // A variable is only reliably bound after an If if it was bound before OR
                // it was defined in both branches.
                let new_in_both: BTreeSet<_> = then_bound
                    .intersection(&else_bound)
                    .filter(|v| !bound_before_if.contains(*v))
                    .cloned()
                    .collect();
                bound.extend(new_in_both);
            }
            IRNode::Match { scrutinee, cases } => {
                scrutinee.collect_free_vars(free, bound);
                // IMPORTANT: Each case must use its own copy of bound, similar to If branches.
                // Bindings from one case should NOT affect other cases.
                let bound_before_match = bound.clone();
                let mut case_bounds: Vec<BTreeSet<TempId>> = Vec::new();
                for (_, bindings, body) in cases {
                    let mut case_bound = bound.clone();
                    // Add case bindings to this case's bound set
                    for v in bindings {
                        case_bound.insert(v.clone());
                    }
                    body.collect_free_vars(free, &mut case_bound);
                    // Remove case bindings (they're local to this case)
                    for v in bindings {
                        case_bound.remove(v);
                    }
                    case_bounds.push(case_bound);
                }
                // After the Match, add variables that were defined in ALL cases
                if !case_bounds.is_empty() {
                    let mut common: BTreeSet<_> = case_bounds[0].clone();
                    for cb in case_bounds.iter().skip(1) {
                        common = common.intersection(cb).cloned().collect();
                    }
                    let new_in_all: BTreeSet<_> = common
                        .into_iter()
                        .filter(|v| !bound_before_match.contains(v))
                        .collect();
                    bound.extend(new_in_all);
                }
            }
            IRNode::Call { args, .. } => {
                for arg in args {
                    arg.collect_free_vars(free, bound);
                }
            }
            IRNode::BinOp { lhs, rhs, .. } => {
                lhs.collect_free_vars(free, bound);
                rhs.collect_free_vars(free, bound);
            }
            IRNode::UnOp { operand, .. } => {
                operand.collect_free_vars(free, bound);
            }
            IRNode::Tuple(exprs) => {
                for e in exprs {
                    e.collect_free_vars(free, bound);
                }
            }
            IRNode::Pack { fields, .. } => {
                for e in fields {
                    e.collect_free_vars(free, bound);
                }
            }
            IRNode::Field { base, .. } => {
                base.collect_free_vars(free, bound);
            }
            IRNode::Unpack { value, .. } => {
                value.collect_free_vars(free, bound);
            }
            IRNode::UpdateField { base, value, .. } => {
                base.collect_free_vars(free, bound);
                value.collect_free_vars(free, bound);
            }
            IRNode::UpdateVec { base, index, value } => {
                base.collect_free_vars(free, bound);
                index.collect_free_vars(free, bound);
                value.collect_free_vars(free, bound);
            }
            IRNode::ReadRef(inner) => {
                inner.collect_free_vars(free, bound);
            }
            IRNode::WriteRef { reference, value } => {
                reference.collect_free_vars(free, bound);
                value.collect_free_vars(free, bound);
            }
            IRNode::Quantifier {
                callback,
                lambda_param,
                collection,
                range,
                ..
            } => {
                let was_bound = bound.contains(lambda_param);
                bound.insert(lambda_param.clone());
                callback.collect_free_vars(free, bound);
                if !was_bound {
                    bound.remove(lambda_param);
                }
                if let Some(coll) = collection {
                    coll.collect_free_vars(free, bound);
                }
                if let Some((start, end)) = range {
                    start.collect_free_vars(free, bound);
                    end.collect_free_vars(free, bound);
                }
            }
            IRNode::BitOp(op) => match op {
                BitOp::Extract { operand, .. }
                | BitOp::ZeroExtend { operand, .. }
                | BitOp::SignExtend { operand, .. } => {
                    operand.collect_free_vars(free, bound);
                }
                BitOp::Concat { high, low } => {
                    high.collect_free_vars(free, bound);
                    low.collect_free_vars(free, bound);
                }
            },
            IRNode::ToProp(inner) | IRNode::ToBool(inner) | IRNode::OptionSome(inner) => {
                inner.collect_free_vars(free, bound);
            }
            IRNode::MatchOption {
                scrutinee,
                binding,
                some_branch,
                none_branch,
            } => {
                scrutinee.collect_free_vars(free, bound);
                // binding is a binder for some_branch
                let was_bound = bound.contains(binding);
                bound.insert(binding.clone());
                some_branch.collect_free_vars(free, bound);
                if !was_bound {
                    bound.remove(binding);
                }
                none_branch.collect_free_vars(free, bound);
            }
            IRNode::WriteBack { child, parent, .. } => {
                if !bound.contains(child) {
                    free.insert(child.clone());
                }
                if !bound.contains(parent) {
                    free.insert(parent.clone());
                }
            }
            IRNode::MutableCompose { inner, outer } => {
                if !bound.contains(inner) {
                    free.insert(inner.clone());
                }
                if !bound.contains(outer) {
                    free.insert(outer.clone());
                }
            }
            // Terminal nodes with no sub-expressions
            IRNode::Const(_) | IRNode::OptionNone | IRNode::Inhabited => {}
            IRNode::Abort { code } => {
                if let Some(code) = code {
                    code.collect_free_vars(free, bound);
                }
            }
            IRNode::MoveAbortValue { code, .. } => {
                code.collect_free_vars(free, bound);
            }
            IRNode::ArithOverflowCheck { lhs, rhs, .. } => {
                lhs.collect_free_vars(free, bound);
                rhs.collect_free_vars(free, bound);
            }
        }
    }

    /// Collect all function calls
    pub fn calls(&self) -> impl Iterator<Item = FunctionID> + '_ {
        self.iter().filter_map(|node| match node {
            IRNode::Call { function, .. } => Some(*function),
            _ => None,
        })
    }

    /// Substitute variables according to a mapping
    pub fn substitute_vars(self, subs: &BTreeMap<String, String>) -> IRNode {
        self.map(&mut |node| match node {
            IRNode::Var(name) => {
                let name_str: &str = &name;
                if let Some(new_name) = subs.get(name_str) {
                    IRNode::Var(Rc::from(new_name.as_str()))
                } else {
                    IRNode::Var(name)
                }
            }
            IRNode::Let {
                pattern,
                value,
                body,
            } => {
                // Also substitute variable names in let patterns
                let pattern = pattern
                    .into_iter()
                    .map(|v| {
                        let v_str: &str = &v;
                        if let Some(new_name) = subs.get(v_str) {
                            Rc::from(new_name.as_str())
                        } else {
                            v
                        }
                    })
                    .collect();
                IRNode::Let {
                    pattern,
                    value,
                    body,
                }
            }
            other => other,
        })
    }

    /// Extract top-level variable names from a tuple/var expression
    pub fn extract_top_level_vars(&self) -> Vec<&TempId> {
        match self {
            IRNode::Var(name) => vec![name],
            IRNode::Tuple(elems) => elems
                .iter()
                .flat_map(|e| e.extract_top_level_vars())
                .collect(),
            _ => vec![],
        }
    }

    /// Collect all struct IDs referenced in Pack, Unpack, Field, UpdateField operations
    pub fn iter_struct_references(&self) -> impl Iterator<Item = StructID> + '_ {
        self.iter().filter_map(|node| match node {
            IRNode::Pack { struct_id, .. }
            | IRNode::Unpack { struct_id, .. }
            | IRNode::Field { struct_id, .. }
            | IRNode::UpdateField { struct_id, .. } => Some(*struct_id),
            _ => None,
        })
    }

    /// Collect all struct IDs referenced in type positions (type arguments)
    pub fn iter_type_struct_ids(&self) -> impl Iterator<Item = StructID> + '_ {
        self.iter()
            .filter_map(|node| match node {
                IRNode::Pack { type_args, .. } | IRNode::Call { type_args, .. } => {
                    Some(type_args.iter())
                }
                _ => None,
            })
            .flatten()
            .flat_map(|ty| ty.struct_ids())
    }

    /// Get the type of this IR expression using the type context.
    /// Panics if a variable is not found in the registry or if the node
    /// has no meaningful type (Abort, Inhabited, etc.).
    pub fn get_type(&self, reg: &VariableRegistry) -> Type {
        match self {
            IRNode::Var(name) => reg.get_type(name).clone(),

            IRNode::Const(c) => match c {
                Const::Bool(_) => Type::Bool,
                Const::UInt { bits, .. } => Type::UInt(*bits as u32),
                Const::Address(_) => Type::Address,
                Const::Vector { elem_type, .. } => Type::Vector(Box::new(elem_type.clone())),
            },

            IRNode::BinOp { op, lhs, rhs } => match op {
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => Type::Bool,
                BinOp::Eq | BinOp::Neq => Type::Bool,
                BinOp::And | BinOp::Or => {
                    let lhs_prop = matches!(lhs.get_type(reg), Type::Prop);
                    let rhs_prop = matches!(rhs.get_type(reg), Type::Prop);
                    if lhs_prop || rhs_prop {
                        Type::Prop
                    } else {
                        Type::Bool
                    }
                }
                BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Mod
                | BinOp::BitAnd
                | BinOp::BitOr
                | BinOp::BitXor
                | BinOp::Shl
                | BinOp::Shr => lhs.get_type(reg),
            },

            IRNode::UnOp { op, operand } => match op {
                // `!` over a Bool stays Bool; over a Prop operand (e.g. a
                // negated quantifier) it is logical negation `¬`, a Prop.
                UnOp::Not => {
                    if matches!(operand.get_type(reg), Type::Prop) {
                        Type::Prop
                    } else {
                        Type::Bool
                    }
                }
                UnOp::BitNot => operand.get_type(reg),
                UnOp::Cast(bits) => Type::UInt(*bits),
            },

            IRNode::BitOp(bit_op) => match bit_op {
                BitOp::Extract { high, low, .. } => Type::UInt(high - low + 1),
                BitOp::Concat { high, low } => {
                    let high_type = high.get_type(reg);
                    let low_type = low.get_type(reg);
                    match (high_type, low_type) {
                        (Type::UInt(h), Type::UInt(l)) => Type::UInt(h + l),
                        _ => panic!("BitOp::Concat expects UInt operands"),
                    }
                }
                BitOp::ZeroExtend { bits, operand } | BitOp::SignExtend { bits, operand } => {
                    let op_type = operand.get_type(reg);
                    match op_type {
                        Type::UInt(orig_bits) => Type::UInt(orig_bits + bits),
                        _ => panic!("BitOp extend expects UInt operand"),
                    }
                }
            },

            IRNode::Call {
                function,
                type_args,
                ..
            } => {
                let ret_type = reg.function_return_type(*function).clone();
                if type_args.is_empty() {
                    ret_type
                } else {
                    ret_type.substitute_type_params(type_args)
                }
            }

            IRNode::Pack {
                struct_id,
                type_args,
                ..
            } => Type::Struct {
                struct_id: *struct_id,
                type_args: type_args.clone(),
            },

            IRNode::Field {
                struct_id,
                field_index,
                ..
            } => reg.struct_field_type(*struct_id, *field_index).clone(),

            IRNode::Unpack {
                struct_id,
                variant_index,
                ..
            } => {
                let s = reg.program().structs.get(*struct_id);
                if let Some(vi) = variant_index {
                    let variant = s
                        .variants
                        .as_ref()
                        .expect("Unpack with variant_index on non-enum struct")
                        .iter()
                        .find(|v| v.tag == *vi)
                        .expect("Variant not found");
                    Type::Tuple(
                        variant
                            .fields
                            .iter()
                            .map(|f| f.field_type.clone())
                            .collect(),
                    )
                } else {
                    reg.struct_fields_tuple(*struct_id)
                }
            }

            IRNode::Tuple(elems) => Type::Tuple(elems.iter().map(|e| e.get_type(reg)).collect()),

            IRNode::Let {
                pattern,
                value,
                body,
            } => {
                let mut tmp = reg.clone();
                let val_type = value.get_type(&tmp);
                tmp.register_pattern(pattern, val_type);
                body.get_type(&tmp)
            }

            IRNode::If { then_branch, .. } => then_branch.get_type(reg),

            IRNode::Match { scrutinee, cases } => {
                let (tag, bindings, body) =
                    cases.first().expect("Match must have at least one case");
                // Peel off references to reach the underlying struct type.
                let scrutinee_ty = match scrutinee.get_type(reg) {
                    Type::Reference(inner) => *inner,
                    Type::MutableReference(val, _) => *val,
                    other => other,
                };
                let Type::Struct {
                    struct_id,
                    type_args,
                } = scrutinee_ty
                else {
                    panic!(
                        "Match scrutinee must have Struct type, got {:?}",
                        scrutinee_ty
                    );
                };
                let s = reg.program().structs.get(struct_id);
                let variant = s
                    .variants
                    .as_ref()
                    .expect("Match on non-enum struct")
                    .iter()
                    .find(|v| v.tag == *tag)
                    .expect("Variant not found for Match tag");
                let mut inner = reg.clone();
                for (name, field) in bindings.iter().zip(variant.fields.iter()) {
                    let ty = field.field_type.clone().substitute_type_params(&type_args);
                    inner.register(name.clone(), ty);
                }
                body.get_type(&inner)
            }

            IRNode::UpdateField { base, .. } => base.get_type(reg),
            IRNode::UpdateVec { base, .. } => base.get_type(reg),

            IRNode::MutableBorrow {
                val_expr,
                state_type,
                ..
            } => {
                let val_type = val_expr.get_type(reg);
                Type::MutableReference(Box::new(val_type), Box::new(state_type.clone()))
            }

            IRNode::ReadRef(inner) => {
                let inner_type = inner.get_type(reg);
                match inner_type {
                    Type::MutableReference(val_type, _) => *val_type,
                    _ => inner_type,
                }
            }

            IRNode::WriteRef { reference, .. } => {
                // WriteRef renders as `Mutable.set ref val` in Lean, which
                // returns the same `Mutable α State` type as the reference
                // — NOT the bare State type. Returning `state` here would
                // mis-type any `let X := WriteRef { ref: Var(X), val }`
                // rebind as the bare struct, stripping `Mutable.val` from
                // every later field access on X (e.g. surfacing as
                // `Mutable.<field>` errors at lake-build time when an
                // outer If wraps the WriteRef as its terminal).
                reference.get_type(reg)
            }

            IRNode::Quantifier {
                kind,
                callback,
                lambda_param,
                lambda_type,
                ..
            } => {
                // The callback references `lambda_param`; bring it into scope.
                let callback_type = || {
                    let mut inner = reg.clone();
                    inner.register(lambda_param.clone(), lambda_type.clone());
                    callback.get_type(&inner)
                };
                match kind {
                    // `forall!`/`exists!` quantify over an entire type and are
                    // therefore logical propositions, not computable booleans
                    // (no `Decidable (∀ x, ..)` short of explosive enumeration
                    // or classical choice). They are `Prop` and render as native
                    // Lean `∀`/`∃`. There is NO opaque `spec_forall`/`spec_exists`
                    // fallback: a `bool` predicate whose body is logical is
                    // promoted to `Prop` (`infer_prop_returns`), and all boolean
                    // structure in a Prop function (`&&`/`||`/`!`/`if`) renders
                    // as the corresponding Prop connective. A quantifier left in
                    // a genuine computable-Bool position is a hard error.
                    QuantifierKind::Forall | QuantifierKind::Exists => Type::Prop,
                    QuantifierKind::Any
                    | QuantifierKind::AnyRange
                    | QuantifierKind::All
                    | QuantifierKind::AllRange => Type::Bool,
                    QuantifierKind::FindIndex | QuantifierKind::FindIndexRange => callback_type(),
                    QuantifierKind::Count
                    | QuantifierKind::CountRange
                    | QuantifierKind::RangeCount => Type::UInt(64),
                    QuantifierKind::SumMap
                    | QuantifierKind::SumMapRange
                    | QuantifierKind::RangeSumMap => callback_type(),
                    QuantifierKind::RangeMap
                    | QuantifierKind::Map
                    | QuantifierKind::MapRange
                    | QuantifierKind::Filter
                    | QuantifierKind::FilterRange
                    | QuantifierKind::Find
                    | QuantifierKind::FindRange
                    | QuantifierKind::FindIndices
                    | QuantifierKind::FindIndicesRange => Type::Vector(Box::new(callback_type())),
                }
            }

            IRNode::ToProp(_) => Type::Prop,
            IRNode::ToBool(_) => Type::Bool,
            IRNode::ArithOverflowCheck { .. } => Type::Bool,
            IRNode::WriteBack { .. } => Type::Tuple(vec![]),

            IRNode::MutableCompose { inner, outer } => {
                let inner_type = IRNode::Var(inner.clone()).get_type(reg);
                let outer_type = IRNode::Var(outer.clone()).get_type(reg);
                match (&inner_type, &outer_type) {
                    (Type::MutableReference(val, _), Type::MutableReference(_, state)) => {
                        Type::MutableReference(val.clone(), state.clone())
                    }
                    (Type::MutableReference(val, _), _) => {
                        Type::MutableReference(val.clone(), Box::new(outer_type))
                    }
                    _ => inner_type,
                }
            }

            IRNode::OptionSome(_)
            | IRNode::OptionNone
            | IRNode::MatchOption { .. }
            | IRNode::Inhabited
            | IRNode::Abort { .. }
            | IRNode::MoveAbortValue { .. } => {
                panic!(
                    "get_type called on node with no meaningful type: {:?}",
                    self
                )
            }
        }
    }

    /// Chain two IR nodes: evaluates `first` then `second`.
    ///
    /// Bindings from `first` are in scope for `second`. Produces a flat Let
    /// spine by appending `second` at the tail of `first`'s body chain (the
    /// trailing `()` node). This ensures all Let-bound variables stay on the
    /// body spine and are visible to `sequential_bindings()`.
    ///
    /// Skips the wrapping if either side is unit `()`.
    pub fn assign(first: IRNode, second: IRNode) -> IRNode {
        if matches!(&first, IRNode::Tuple(elems) if elems.is_empty()) {
            return second;
        }
        if matches!(&second, IRNode::Tuple(elems) if elems.is_empty()) {
            return first;
        }
        // Walk first's body chain to find the trailing () and replace it with second.
        // This keeps all Let bindings on the body spine.
        fn append_at_tail(node: IRNode, tail: IRNode) -> IRNode {
            match node {
                IRNode::Let {
                    pattern,
                    value,
                    body,
                } if matches!(*body, IRNode::Tuple(ref elems) if elems.is_empty()) => IRNode::Let {
                    pattern,
                    value,
                    body: Box::new(tail),
                },
                IRNode::Let {
                    pattern,
                    value,
                    body,
                } => IRNode::Let {
                    pattern,
                    value,
                    body: Box::new(append_at_tail(*body, tail)),
                },
                // first is not a Let chain — wrap with empty pattern
                other => IRNode::Let {
                    pattern: vec![],
                    value: Box::new(other),
                    body: Box::new(tail),
                },
            }
        }
        append_at_tail(first, second)
    }
}

/// This helps with the conversion for the macro
trait AsIRRef<'a> {
    fn as_ir_ref(&'a self) -> &'a IRNode;
}

impl<'a> AsIRRef<'a> for Box<IRNode> {
    fn as_ir_ref(&'a self) -> &'a IRNode {
        self.as_ref()
    }
}

impl<'a> AsIRRef<'a> for IRNode {
    fn as_ir_ref(&'a self) -> &'a IRNode {
        self
    }
}

trait AsIRMut<'a> {
    fn as_ir_mut(&'a mut self) -> &'a mut IRNode;
}

impl<'a> AsIRMut<'a> for Box<IRNode> {
    fn as_ir_mut(&'a mut self) -> &'a mut IRNode {
        self.as_mut()
    }
}

impl<'a> AsIRMut<'a> for IRNode {
    fn as_ir_mut(&'a mut self) -> &'a mut IRNode {
        self
    }
}
