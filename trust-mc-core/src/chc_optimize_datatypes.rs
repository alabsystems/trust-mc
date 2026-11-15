// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Datatype declarations that nothing emitted reaches.
//!
//! `codegen_decl_datatypes` declares a datatype for every sort it meets while
//! the frame is being built: every state variable (including type-indexed
//! memory arrays), every flattened local, every const-ref value and every
//! pending fresh variable. Nothing ever removed one, so a datatype whose last
//! user was dropped by array pruning, scalarization, constant propagation or
//! the unconstrained-argument projection is still printed.
//!
//! This pass keeps a `declare-datatype` only when it is reachable from what
//! `emit_chc` prints: the sorts of `declare-var`s, relation signatures, every
//! node of every rule constraint and relation argument, cover assertions, and
//! the sorts of `declare-const` / `declare-fun`. Reachability is closed over
//! datatype field sorts, array index/element sorts and sequence element sorts,
//! through both the sort embedded in the expression and the DECLARED
//! definition of the same name. A constructor, selector or tester application
//! names its datatype and keeps it; a plain function application whose name is
//! a declared constructor, selector or `is-<constructor>` tester keeps that
//! datatype too, and an uninterpreted sort named like a declared datatype keeps
//! it. A later same-name datatype declaration is dropped: the emitter keeps
//! the first definition of a name and skips the rest, so dropping it changes no
//! emitted byte.
//!
//! Exact: an unreachable declaration constrains no clause. AY's executor
//! admission charges only datatypes reachable from clauses, so this does not
//! move its sort-node or name-byte charges; it bounds the declared set that
//! AY's route admission counts (`max_datatype_defs`), the parse work, and the
//! definitions the per-property slices clone.

use std::collections::{HashMap, HashSet};

use ay_bindings::{Expr, ExprValue, Sort, SortInner};

use crate::chc::ChcVc;
use crate::decl::Decl;

/// Removes datatype declarations no emitted item reaches, and later same-name
/// duplicates. Returns the number of declarations removed.
pub(super) fn prune_unreachable_datatype_decls(vc: &mut ChcVc) -> usize {
    let mut declared: HashMap<&str, &ay_bindings::DatatypeSort> = HashMap::new();
    // Constructor, selector and tester spellings of every declared datatype, so
    // a `FuncApp` spelled with one of them keeps its datatype.
    let mut member_names: HashMap<String, &str> = HashMap::new();
    for decl in &vc.decls {
        if let Decl::Datatype { datatype } = decl {
            if declared.contains_key(datatype.name.as_str()) {
                continue;
            }
            declared.insert(datatype.name.as_str(), datatype);
            for constructor in &datatype.constructors {
                member_names.insert(constructor.name.clone(), datatype.name.as_str());
                member_names.insert(format!("is-{}", constructor.name), datatype.name.as_str());
                for field in &constructor.fields {
                    member_names.insert(field.name.clone(), datatype.name.as_str());
                }
            }
        }
    }
    if declared.is_empty() {
        return 0;
    }

    let mut reach = Reach {
        declared: &declared,
        member_names: &member_names,
        reached: HashSet::new(),
        pending: Vec::new(),
        seen_sorts: HashSet::new(),
    };
    for decl in &vc.decls {
        match decl {
            Decl::Const { sort, .. } => reach.sort(sort),
            Decl::Fun { arg_sorts, ret_sort, .. } => {
                for sort in arg_sorts {
                    reach.sort(sort);
                }
                reach.sort(ret_sort);
            }
            Decl::Datatype { .. } => {}
        }
    }
    for var in vc.vars() {
        reach.sort(&var.sort);
    }
    for relation in &vc.relations {
        for sort in &relation.arg_sorts {
            reach.sort(sort);
        }
    }
    for rule in &vc.rules {
        for constraint in rule.body.constraints.iter() {
            reach.expr(constraint);
        }
        if let Some(body) = &rule.body.relation {
            for arg in body.args.iter() {
                reach.expr(arg);
            }
        }
        for arg in rule.head.args.iter() {
            reach.expr(arg);
        }
    }
    for (_, condition) in &vc.cover_assertions {
        reach.expr(condition);
    }
    reach.close();

    let reached = reach.reached;
    let before = vc.decls.len();
    let mut kept_names: HashSet<String> = HashSet::new();
    vc.decls.retain(|decl| match decl {
        Decl::Datatype { datatype } => {
            reached.contains(datatype.name.as_str()) && kept_names.insert(datatype.name.clone())
        }
        _ => true,
    });
    before - vc.decls.len()
}

struct Reach<'a> {
    declared: &'a HashMap<&'a str, &'a ay_bindings::DatatypeSort>,
    member_names: &'a HashMap<String, &'a str>,
    reached: HashSet<String>,
    /// Declared definitions reached but not yet walked.
    pending: Vec<&'a str>,
    seen_sorts: HashSet<Sort>,
}

impl<'a> Reach<'a> {
    fn name(&mut self, name: &str) {
        if self.reached.insert(name.to_string())
            && let Some((&declared_name, _)) = self.declared.get_key_value(name)
        {
            self.pending.push(declared_name);
        }
    }

    fn sort(&mut self, root: &Sort) {
        if self.seen_sorts.contains(root) {
            return;
        }
        let mut stack = vec![root.clone()];
        while let Some(sort) = stack.pop() {
            if !self.seen_sorts.insert(sort.clone()) {
                continue;
            }
            match sort.inner() {
                SortInner::Array(array) => {
                    stack.push(array.index_sort.clone());
                    stack.push(array.element_sort.clone());
                }
                SortInner::Datatype(datatype) => {
                    self.name(&datatype.name);
                    for constructor in &datatype.constructors {
                        for field in &constructor.fields {
                            stack.push(field.sort.clone());
                        }
                    }
                }
                SortInner::Seq(element) => stack.push((**element).clone()),
                SortInner::Uninterpreted(name) => self.name(name),
                _ => {}
            }
        }
    }

    fn expr(&mut self, root: &Expr) {
        let mut stack = vec![root];
        while let Some(node) = stack.pop() {
            self.sort(node.sort());
            match node.value() {
                ExprValue::DatatypeConstructor { datatype_name, .. }
                | ExprValue::DatatypeSelector { datatype_name, .. }
                | ExprValue::DatatypeTester { datatype_name, .. } => self.name(datatype_name),
                ExprValue::FuncApp { name, .. } => {
                    if let Some(&datatype) = self.member_names.get(name.as_str()) {
                        self.name(datatype);
                    }
                }
                ExprValue::ConstArray { index_sort, .. } | ExprValue::SeqEmpty(index_sort) => {
                    self.sort(index_sort);
                }
                ExprValue::Forall { vars, .. } | ExprValue::Exists { vars, .. } => {
                    for (_, sort) in vars {
                        self.sort(sort);
                    }
                }
                _ => {}
            }
            stack.extend(node.children());
        }
    }

    /// Walks every reached declared definition's field sorts to a fixpoint.
    fn close(&mut self) {
        while let Some(name) = self.pending.pop() {
            let Some(datatype) = self.declared.get(name) else { continue };
            for constructor in &datatype.constructors {
                for field in &constructor.fields {
                    self.sort(&field.sort);
                }
            }
        }
    }
}
