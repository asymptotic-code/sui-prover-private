//! DSL for hand-building `Vec<Bytecode>` fixtures. See
//! `plans/lean-pipeline/testing-strategy.md` "Stage 1's bytecode fixtures".
//!
//! Labels are string-named: the first reference (via `branch` / `jump` /
//! `variant_switch` / `label`) allocates a `Label(u16)`; subsequent
//! references resolve to the same id. Forward references are fine.
//! `label(name)` both emits `Bytecode::Label` and records the binding;
//! double-defining panics, and [`BytecodeBuilder::finish`] panics on
//! any reference that was never defined.
//!
//! AttrIds and Labels are allocated sequentially from 0, so the same
//! script produces byte-identical output across runs.

#![cfg(test)]

use move_stackless_bytecode::ast::TempIndex;
use move_stackless_bytecode::stackless_bytecode::{
    AbortAction, AssignKind, AttrId, Bytecode, Constant, Label, Operation,
};
use std::collections::{HashMap, HashSet};

/// DSL for assembling `Vec<Bytecode>` fixtures.
#[derive(Default)]
pub struct BytecodeBuilder {
    code: Vec<Bytecode>,
    next_attr: u16,
    labels: HashMap<String, Label>,
    next_label: u16,
    defined_labels: HashSet<String>,
}

impl BytecodeBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    fn fresh_attr(&mut self) -> AttrId {
        let id = AttrId::new(self.next_attr as usize);
        self.next_attr = self
            .next_attr
            .checked_add(1)
            .expect("BytecodeBuilder: AttrId overflowed u16; fixture is too large");
        id
    }

    /// Resolve (and allocate, if first reference) the `Label` for `name`.
    fn label_id(&mut self, name: &str) -> Label {
        if let Some(&existing) = self.labels.get(name) {
            return existing;
        }
        let id = Label::new(self.next_label as usize);
        self.next_label = self
            .next_label
            .checked_add(1)
            .expect("BytecodeBuilder: Label overflowed u16; fixture is too large");
        self.labels.insert(name.to_string(), id);
        id
    }

    /// Emit `Bytecode::Label(name)` and define the binding.
    /// Panics if `name` was already defined.
    pub fn label(mut self, name: &str) -> Self {
        if !self.defined_labels.insert(name.to_string()) {
            panic!("BytecodeBuilder: label {name:?} defined twice");
        }
        let attr = self.fresh_attr();
        let id = self.label_id(name);
        self.code.push(Bytecode::Label(attr, id));
        self
    }

    /// Emit `Bytecode::Jump(target)`.
    pub fn jump(mut self, target: &str) -> Self {
        let attr = self.fresh_attr();
        let id = self.label_id(target);
        self.code.push(Bytecode::Jump(attr, id));
        self
    }

    /// Emit `Bytecode::Branch(then_label, else_label, cond)`.
    pub fn branch(mut self, cond: TempIndex, then: &str, els: &str) -> Self {
        let attr = self.fresh_attr();
        let then_id = self.label_id(then);
        let else_id = self.label_id(els);
        self.code
            .push(Bytecode::Branch(attr, then_id, else_id, cond));
        self
    }

    pub fn ret(mut self, temps: &[TempIndex]) -> Self {
        let attr = self.fresh_attr();
        self.code.push(Bytecode::Ret(attr, temps.to_vec()));
        self
    }

    pub fn abort(mut self, code_temp: TempIndex) -> Self {
        let attr = self.fresh_attr();
        self.code.push(Bytecode::Abort(attr, code_temp));
        self
    }

    /// Emit `Bytecode::VariantSwitch(scrut, [labels])`.
    pub fn variant_switch(mut self, scrut: TempIndex, labels: &[&str]) -> Self {
        let attr = self.fresh_attr();
        let resolved: Vec<Label> = labels.iter().map(|n| self.label_id(n)).collect();
        self.code
            .push(Bytecode::VariantSwitch(attr, scrut, resolved));
        self
    }

    pub fn nop(mut self) -> Self {
        let attr = self.fresh_attr();
        self.code.push(Bytecode::Nop(attr));
        self
    }

    pub fn load(mut self, dst: TempIndex, c: Constant) -> Self {
        let attr = self.fresh_attr();
        self.code.push(Bytecode::Load(attr, dst, c));
        self
    }

    pub fn load_bool(self, dst: TempIndex, b: bool) -> Self {
        self.load(dst, Constant::Bool(b))
    }

    pub fn load_u64(self, dst: TempIndex, n: u64) -> Self {
        self.load(dst, Constant::U64(n))
    }

    pub fn assign(mut self, dst: TempIndex, src: TempIndex, kind: AssignKind) -> Self {
        let attr = self.fresh_attr();
        self.code.push(Bytecode::Assign(attr, dst, src, kind));
        self
    }

    pub fn copy(self, dst: TempIndex, src: TempIndex) -> Self {
        self.assign(dst, src, AssignKind::Copy)
    }

    /// `assign(dst, src, AssignKind::Move)` -- `move` is a reserved keyword.
    pub fn move_(self, dst: TempIndex, src: TempIndex) -> Self {
        self.assign(dst, src, AssignKind::Move)
    }

    pub fn store(self, dst: TempIndex, src: TempIndex) -> Self {
        self.assign(dst, src, AssignKind::Store)
    }

    /// Emit `Bytecode::Call(dsts, op, srcs, None)` -- non-aborting.
    pub fn call(mut self, dsts: &[TempIndex], op: Operation, srcs: &[TempIndex]) -> Self {
        let attr = self.fresh_attr();
        self.code
            .push(Bytecode::Call(attr, dsts.to_vec(), op, srcs.to_vec(), None));
        self
    }

    /// Emit `Bytecode::Call(dsts, op, srcs, Some(AbortAction::Check))`.
    /// Models aborting arithmetic / narrowing-cast / etc. The
    /// `=false` and `=true` `StacklessControlFlowGraph`s partition
    /// basic blocks differently around these Calls (see
    /// `loops::translate_loops`); regression tests for the
    /// loop-id-translation fix should use this.
    pub fn call_aborting(mut self, dsts: &[TempIndex], op: Operation, srcs: &[TempIndex]) -> Self {
        let attr = self.fresh_attr();
        self.code.push(Bytecode::Call(
            attr,
            dsts.to_vec(),
            op,
            srcs.to_vec(),
            Some(AbortAction::Check),
        ));
        self
    }

    /// Finish and return the `Vec<Bytecode>`. Panics if any referenced
    /// label was never defined (clearer than letting upstream's CFG
    /// builder ICE on the dangling reference).
    pub fn finish(self) -> Vec<Bytecode> {
        let mut dangling: Vec<&str> = self
            .labels
            .keys()
            .map(String::as_str)
            .filter(|name| !self.defined_labels.contains(*name))
            .collect();
        if !dangling.is_empty() {
            dangling.sort();
            panic!(
                "BytecodeBuilder: label(s) referenced but never defined: {}",
                dangling.join(", ")
            );
        }
        self.code
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn label_index_of(bc: &Bytecode) -> Option<usize> {
        match bc {
            Bytecode::Label(_, l) => Some(l.as_usize()),
            _ => None,
        }
    }

    #[test]
    fn empty_builder_returns_empty_vec() {
        let code = BytecodeBuilder::new().finish();
        assert!(code.is_empty());
    }

    #[test]
    fn linear_emits_in_order() {
        let code = BytecodeBuilder::new()
            .load_u64(0, 7)
            .copy(1, 0)
            .ret(&[1])
            .finish();
        assert_eq!(code.len(), 3);
        assert!(matches!(code[0], Bytecode::Load(_, 0, Constant::U64(7))));
        assert!(matches!(
            code[1],
            Bytecode::Assign(_, 1, 0, AssignKind::Copy)
        ));
        assert!(matches!(&code[2], Bytecode::Ret(_, t) if t.as_slice() == [1]));
    }

    #[test]
    fn auto_attr_ids_are_sequential() {
        let code = BytecodeBuilder::new().nop().nop().nop().finish();
        let attrs: Vec<usize> = code
            .iter()
            .map(|b| match b {
                Bytecode::Nop(a) => a.as_usize(),
                _ => unreachable!(),
            })
            .collect();
        assert_eq!(attrs, vec![0, 1, 2]);
    }

    #[test]
    fn forward_label_resolves_at_finish() {
        let code = BytecodeBuilder::new()
            .jump("end")
            .label("end")
            .ret(&[])
            .finish();
        let jumped_to = match &code[0] {
            Bytecode::Jump(_, l) => l.as_usize(),
            _ => panic!("expected Jump"),
        };
        let defined_at = label_index_of(&code[1]).expect("expected Label");
        assert_eq!(jumped_to, defined_at);
    }

    #[test]
    fn branch_uses_named_labels() {
        let code = BytecodeBuilder::new()
            .branch(0, "then", "else_arm")
            .label("then")
            .ret(&[])
            .label("else_arm")
            .ret(&[])
            .finish();
        let (then_l, else_l, cond) = match &code[0] {
            Bytecode::Branch(_, t, e, c) => (t.as_usize(), e.as_usize(), *c),
            _ => panic!("expected Branch"),
        };
        assert_eq!(cond, 0);
        assert_eq!(then_l, label_index_of(&code[1]).unwrap());
        assert_eq!(else_l, label_index_of(&code[3]).unwrap());
        assert_ne!(then_l, else_l);
    }

    #[test]
    fn variant_switch_with_three_arms_resolves_each_label() {
        let code = BytecodeBuilder::new()
            .variant_switch(0, &["a", "b", "c"])
            .label("a")
            .ret(&[])
            .label("b")
            .ret(&[])
            .label("c")
            .ret(&[])
            .finish();
        let labels = match &code[0] {
            Bytecode::VariantSwitch(_, scrut, ls) => {
                assert_eq!(*scrut, 0);
                ls.iter().map(|l| l.as_usize()).collect::<Vec<_>>()
            }
            _ => panic!("expected VariantSwitch"),
        };
        let label_a = label_index_of(&code[1]).unwrap();
        let label_b = label_index_of(&code[3]).unwrap();
        let label_c = label_index_of(&code[5]).unwrap();
        assert_eq!(labels, vec![label_a, label_b, label_c]);
    }

    #[test]
    fn shared_forward_reference_is_same_label() {
        // Two jumps to "end" must resolve to the same Label.
        let code = BytecodeBuilder::new()
            .jump("end")
            .jump("end")
            .label("end")
            .ret(&[])
            .finish();
        let l0 = match &code[0] {
            Bytecode::Jump(_, l) => l.as_usize(),
            _ => panic!(),
        };
        let l1 = match &code[1] {
            Bytecode::Jump(_, l) => l.as_usize(),
            _ => panic!(),
        };
        assert_eq!(l0, l1);
        assert_eq!(l0, label_index_of(&code[2]).unwrap());
    }

    #[test]
    fn abort_emits_with_code_temp() {
        let code = BytecodeBuilder::new().abort(42).finish();
        assert_eq!(code.len(), 1);
        assert!(matches!(code[0], Bytecode::Abort(_, 42)));
    }

    #[test]
    #[should_panic(expected = "label \"a\" defined twice")]
    fn redefining_label_panics() {
        let _ = BytecodeBuilder::new().label("a").label("a");
    }

    #[test]
    #[should_panic(expected = "label(s) referenced but never defined: missing")]
    fn dangling_forward_reference_panics_at_finish() {
        let _ = BytecodeBuilder::new().jump("missing").finish();
    }

    #[test]
    #[should_panic(expected = "label(s) referenced but never defined: a, b")]
    fn multiple_dangling_references_listed_sorted() {
        let _ = BytecodeBuilder::new().branch(0, "b", "a").finish();
    }
}
