// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Functional helpers for common rendering patterns

use intermediate_theorem_format::IRNode;
use std::rc::Rc;

/// Construct a variable tuple from names
pub fn var_tuple(vars: &[String]) -> IRNode {
    match vars {
        [] => IRNode::Tuple(vec![]),
        [single] => IRNode::Var(Rc::from(single.as_str())),
        multiple => IRNode::Tuple(
            multiple
                .iter()
                .map(|v| IRNode::Var(Rc::from(v.as_str())))
                .collect(),
        ),
    }
}
