// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Estimate of AY's executor admission charge for an emitted CHC VC.
//!
//! `ChcProblem::validate()` (reached through `query_obligations()`, i.e. before
//! any per-property slice is cut and before AY's own transforms run) pushes
//! every clause constraint and every predicate-application argument of the
//! WHOLE problem as roots into ONE `DatatypeDeclarationCollector`
//! (`ay-chc/src/smt/executor_adapter/logic_detection.rs`,
//! `collect_uninterpreted_function_declarations_for_problem`). The collector
//! charges, per variable OCCURRENCE, the size of the variable's sort tree and
//! its name length, and caps the totals. A problem over a cap is rejected with
//! `datatype declaration resource limit exceeded: <resource>` /
//! `executor expression resource limit exceeded: <resource>`, which the driver
//! files as `ChcParseError` — no solver ever runs.
//!
//! The numbers here mirror that accounting closely enough to decide whether an
//! emitted VC would be admitted. They are an estimate: AY parses the emitted
//! text, and the parse tree differs from the encoder's `Expr` tree in details
//! that do not matter at the scale of the caps (nested `and` chains, marker
//! nodes). The caps are AY's private constants, copied here with their names;
//! re-check them on every AY pin bump.

use std::collections::{HashMap, HashSet};

use ay_bindings::{Expr, ExprValue, Sort, SortInner};

use crate::chc::ChcVc;

/// `MAX_DT_SORT_NODES` in AY's `logic_detection.rs`.
pub const AY_MAX_DT_SORT_NODES: usize = 32_768;
/// `MAX_DT_EXPR_NODES` in AY's `logic_detection.rs`.
pub const AY_MAX_DT_EXPR_NODES: usize = 131_072;
/// `MAX_EXECUTOR_EXPR_ROOTS` in AY's `logic_detection.rs` (= `MAX_DT_EXPR_NODES`).
pub const AY_MAX_EXECUTOR_EXPR_ROOTS: usize = 131_072;
/// `MAX_EXECUTOR_SURFACE_NAME_BYTES` in AY's `logic_detection.rs` (= `MAX_DT_NAME_BYTES`).
pub const AY_MAX_EXECUTOR_SURFACE_NAME_BYTES: usize = 1024 * 1024;

/// What AY's executor admission would charge for a VC.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AyAdmissionEstimate {
    /// Expression roots: one per clause constraint conjunction plus one per
    /// predicate-application argument (body and head).
    pub expr_roots: usize,
    /// Expression nodes visited across every root.
    pub expr_nodes: usize,
    /// Sort-tree nodes charged for every variable occurrence, every function
    /// application's return sort, and every constant array's index sort. A
    /// datatype's selector sorts are expanded once per datatype.
    pub sort_nodes: usize,
    /// Surface name bytes: variable and function names per occurrence, plus
    /// datatype, constructor and selector names once per datatype.
    pub name_bytes: usize,
}

impl AyAdmissionEstimate {
    /// The first AY resource this estimate exceeds, named as AY names it in
    /// its rejection message, or `None` when the VC should be admitted.
    #[must_use]
    pub fn first_exceeded(&self) -> Option<&'static str> {
        if self.expr_roots > AY_MAX_EXECUTOR_EXPR_ROOTS {
            Some("expression roots")
        } else if self.sort_nodes > AY_MAX_DT_SORT_NODES {
            Some("datatype sort nodes")
        } else if self.expr_nodes > AY_MAX_DT_EXPR_NODES {
            Some("datatype expression nodes")
        } else if self.name_bytes > AY_MAX_EXECUTOR_SURFACE_NAME_BYTES {
            Some("executor surface name bytes")
        } else {
            None
        }
    }
}

/// Estimate AY's executor admission charge for `vc` as it would be emitted.
#[must_use]
pub fn estimate_ay_admission(vc: &ChcVc) -> AyAdmissionEstimate {
    let mut charge = Charge::default();
    for rule in &vc.rules {
        let constraints = rule.body.constraints.len();
        if constraints > 0 {
            charge.estimate.expr_roots += 1;
            // The emitter conjoins the constraints into one body expression;
            // `k` conjuncts cost `k - 1` `and` nodes on top of the conjuncts.
            charge.estimate.expr_nodes += constraints - 1;
            for constraint in rule.body.constraints.iter() {
                charge.visit(constraint);
            }
        }
        if let Some(body) = &rule.body.relation {
            for arg in body.args.iter() {
                charge.estimate.expr_roots += 1;
                charge.visit(arg);
            }
        }
        for arg in rule.head.args.iter() {
            charge.estimate.expr_roots += 1;
            charge.visit(arg);
        }
    }
    charge.estimate
}

#[derive(Default)]
struct Charge {
    estimate: AyAdmissionEstimate,
    expanded_datatypes: HashSet<String>,
    sort_sizes: HashMap<Sort, usize>,
}

impl Charge {
    fn visit(&mut self, root: &Expr) {
        let mut stack = vec![root];
        while let Some(node) = stack.pop() {
            self.estimate.expr_nodes += 1;
            match node.value() {
                ExprValue::Var { name } => {
                    self.estimate.name_bytes += name.len();
                    self.charge_sort(node.sort());
                }
                ExprValue::FuncApp { name, .. } => {
                    self.estimate.name_bytes += name.len();
                    self.charge_sort(node.sort());
                }
                ExprValue::DatatypeConstructor { constructor_name, .. } => {
                    self.estimate.name_bytes += constructor_name.len();
                    self.charge_sort(node.sort());
                }
                ExprValue::DatatypeSelector { selector_name, .. } => {
                    self.estimate.name_bytes += selector_name.len();
                    self.charge_sort(node.sort());
                }
                ExprValue::DatatypeTester { constructor_name, .. } => {
                    self.estimate.name_bytes += constructor_name.len();
                    self.charge_sort(node.sort());
                }
                ExprValue::ConstArray { index_sort, .. } => {
                    self.charge_sort(index_sort);
                }
                _ => {}
            }
            stack.extend(node.children());
        }
    }

    fn charge_sort(&mut self, sort: &Sort) {
        if let Some(&size) = self.sort_sizes.get(sort) {
            self.estimate.sort_nodes += size;
            return;
        }
        // A datatype's definition is expanded once; the first walk is charged
        // in full and every later occurrence of the same sort tree at its
        // memoized (unexpanded) size.
        let (size, expanded_any) = self.sort_size(sort);
        self.estimate.sort_nodes += size;
        if !expanded_any {
            self.sort_sizes.insert(sort.clone(), size);
        }
    }

    /// Size of a sort tree, expanding each datatype definition the first time
    /// it is met. Returns the size and whether any expansion happened.
    fn sort_size(&mut self, root: &Sort) -> (usize, bool) {
        let mut size = 0usize;
        let mut expanded_any = false;
        let mut stack = vec![root];
        while let Some(sort) = stack.pop() {
            size += 1;
            match sort.inner() {
                SortInner::Array(array) => {
                    stack.push(&array.element_sort);
                    stack.push(&array.index_sort);
                }
                SortInner::Datatype(datatype) => {
                    if self.expanded_datatypes.insert(datatype.name.clone()) {
                        expanded_any = true;
                        self.estimate.name_bytes += datatype.name.len();
                        for constructor in &datatype.constructors {
                            self.estimate.name_bytes += constructor.name.len();
                            for field in &constructor.fields {
                                self.estimate.name_bytes += field.name.len();
                                stack.push(&field.sort);
                            }
                        }
                    }
                }
                SortInner::Seq(element) => stack.push(element),
                _ => {}
            }
        }
        (size, expanded_any)
    }
}

#[cfg(test)]
#[path = "chc_admission_tests.rs"]
mod tests;
