// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact finite-state partitioning of a closed borrowed iterator's cursor.
//! Each value 0..=len gets a relation, plus an explicit complement relation.
//! No execution is unrolled away: a reset still leads back to state zero,
//! and a value outside the finite cases still traverses the original rules.
use super::ChcCtx;
use crate::codegen_ay::chc::call::substitute_vars;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{Operand, Place, Rvalue, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
#[path = "static_iterator_partition_facts.rs"]
mod facts;
use trust_mc_core::chc::{ChcVc, RelationApp, RelationDecl, Rule, RuleBody};

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn partition_static_iterator_cursors(&mut self) {
        let mut axes = BTreeMap::new();
        let mut flags = BTreeSet::new();
        for block in &self.body.blocks {
            let TerminatorKind::Call { args, destination, .. } = &block.terminator.kind else {
                continue;
            };
            if self.borrowed_static_next_sources(destination.local).is_none() {
                continue;
            }
            let Some(flag_idx) = self.try_state_idx_for_local(destination.local) else { continue };
            if let Some((name, sort)) = self.state_var_mgr.state_vars.get(flag_idx)
                && sort == &ay_bindings::Sort::bool()
            {
                flags.insert(name.to_string());
            }
            let Some(arg) = args.first() else { continue };
            let Some(owner) = self.static_iterator_cursor_owner(arg, 16) else { continue };
            if self.flattened_field_count(owner) != 4 {
                continue;
            }
            let op = Operand::Copy(Place { local: owner, projection: vec![] });
            let Some((_, len)) = self.static_iterator_invariants(&op) else { continue };
            let ExprValue::BitVecConst { value, .. } = len.value() else { continue };
            let Ok(len) = value.to_string().parse::<u64>() else { continue };
            if len > 256 {
                continue;
            }
            let Some(idx) = self.try_state_idx_for_local(owner) else { continue };
            let Some((name, sort)) = self.state_var_mgr.state_vars.get(idx + 3) else { continue };
            if sort.bitvec_width() == Some(POINTER_WIDTH) {
                axes.insert(name.to_string(), len);
            }
        }
        for (name, len) in axes {
            partition_cursor(&mut self.vc, &name, len);
        }
        // The Some/None tag is another exact finite state axis. Partitioning
        // it exposes exhausted transitions without assuming which tag holds.
        for flag in flags {
            partition_axis(&mut self.vc, &flag, 1, true);
        }
    }

    fn static_iterator_cursor_owner(&self, op: &Operand, depth: usize) -> Option<usize> {
        let depth = depth.checked_sub(1)?;
        let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
        if !p.projection.is_empty() {
            return None;
        }
        let ty = self.body.locals().get(p.local)?.ty;
        self.borrowed_slice_item_ty(ty)?;
        if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(..))) {
            return Some(p.local);
        }
        match crate::codegen_ay::chc::modifies_frame_net::unique_def(self.body, p.local)? {
            Rvalue::Use(op, ..) => self.static_iterator_cursor_owner(op, depth),
            Rvalue::Ref(_, _, place) if place.projection.is_empty() => {
                self.static_iterator_cursor_owner(&Operand::Copy(place.clone()), depth)
            }
            _ => None,
        }
    }
}

/// This is a semantics-preserving relation partition, independent of Rust.
/// Refuse the optimization on a conflicting schema or excessive expansion;
/// retain the original VC, without changing its admission or verdict policy.
pub(in crate::codegen_ay::chc) fn partition_cursor(vc: &mut ChcVc, cursor: &str, bound: u64) {
    partition_axis(vc, cursor, bound, false);
}

fn partition_axis(vc: &mut ChcVc, cursor: &str, bound: u64, boolean: bool) {
    let matches_sort = |e: &Expr| {
        if boolean {
            e.sort() == &ay_bindings::Sort::bool()
        } else {
            e.sort().bitvec_width() == Some(POINTER_WIDTH)
        }
    };
    let literal = |k: u64| {
        if boolean {
            Expr::bool_const(k != 0)
        } else {
            Expr::bitvec_const(k as u128, POINTER_WIDTH)
        }
    };
    if vc.rules.len() > 4096 || vc.relations.len() > 4096 {
        return;
    }
    let mut edges: HashMap<String, Vec<String>> = HashMap::new();
    let mut slots = BTreeMap::new();
    for rule in &vc.rules {
        if let Some(body) = &rule.body.relation {
            edges.entry(body.name.to_string()).or_default().push(rule.head.name.to_string());
            if let Some(slot) = body
                .args
                .iter()
                .position(|a| matches!(a.value(), ExprValue::Var { name } if name == cursor))
            {
                if slots.insert(body.name.to_string(), slot).is_some_and(|old| old != slot) {
                    return;
                }
            }
        }
    }
    slots.retain(|name, _| {
        let mut stack = edges.get(name).cloned().unwrap_or_default();
        let mut seen = HashSet::new();
        while let Some(next) = stack.pop() {
            if &next == name {
                return true;
            }
            if seen.insert(next.clone()) {
                stack.extend(edges.get(&next).into_iter().flatten().cloned());
            }
        }
        false
    });
    if slots.is_empty() {
        return;
    }
    if vc.query.target.as_ref().is_some_and(|q| slots.contains_key(q))
        || vc.properties.iter().any(|p| slots.contains_key(&p.relation))
    {
        return;
    }
    let Some(variants) =
        bound.checked_add(if boolean { 1 } else { 2 }).and_then(|n| usize::try_from(n).ok())
    else {
        return;
    };
    let mut estimate = 0usize;
    for rule in &vc.rules {
        let body = rule.body.relation.as_ref().is_some_and(|r| slots.contains_key(r.name.as_str()));
        let head = slots.contains_key(rule.head.name.as_str());
        let Some(n) =
            (if body { variants } else { 1 }).checked_mul(if head { variants } else { 1 })
        else {
            return;
        };
        let Some(next) = estimate.checked_add(n) else { return };
        estimate = next;
    }
    // An optimization work bound, not a solver budget or a proof refusal.
    if estimate > 4096 {
        return;
    }
    let existing: BTreeSet<_> = vc.relations.iter().map(|r| r.name.as_str()).collect();
    let variant_name = |name: &str, k: u64| {
        format!("{name}__static_iter_{}_{k}", if boolean { "tag" } else { "pos" })
    };
    for (name, slot) in &slots {
        let Some(decl) = vc.relations.iter().find(|r| &r.name == name) else { return };
        if decl.arg_sorts.get(*slot).is_none_or(|s| {
            if boolean {
                s != &ay_bindings::Sort::bool()
            } else {
                s.bitvec_width() != Some(POINTER_WIDTH)
            }
        }) {
            return;
        }
        for k in 0..variants as u64 {
            if existing.contains(variant_name(name, k).as_str()) {
                return;
            }
        }
    }
    // Validate every affected application before mutating any part of the VC.
    for rule in &vc.rules {
        for app in rule.body.relation.iter().chain(std::iter::once(&rule.head)) {
            if let Some(&slot) = slots.get(app.name.as_str())
                && app.args.get(slot).is_none_or(|e| !matches_sort(e))
            {
                return;
            }
        }
    }
    if vc.rules.iter().filter_map(|r| r.body.relation.as_ref()).any(|app| {
        slots
            .get(app.name.as_str())
            .is_some_and(|slot| !matches!(app.args[*slot].value(), ExprValue::Var { .. }))
    }) {
        return;
    }
    let guard = |value: Expr, k: u64| {
        if k <= bound {
            value.eq(literal(k))
        } else {
            value.bvugt(Expr::bitvec_const(bound as u128, POINTER_WIDTH))
        }
    };
    let mut rules = Vec::new();
    for rule in &vc.rules {
        let body_slot =
            rule.body.relation.as_ref().and_then(|r| slots.get(r.name.as_str()).copied());
        let head_slot = slots.get(rule.head.name.as_str()).copied();
        for b in 0..if body_slot.is_some() { variants } else { 1 } {
            let mut substitution = HashMap::new();
            let mut constraints = Vec::new();
            if let (Some(slot), Some(body)) = (body_slot, &rule.body.relation) {
                let value = body.args[slot].clone();
                constraints.push(guard(value.clone(), b as u64));
                if (b as u64) <= bound
                    && let ExprValue::Var { name } = value.value()
                {
                    substitution.insert(name.to_string(), literal(b as u64));
                }
            }
            let rewrite = |e: &Expr| substitute_vars(e, &substitution);
            constraints.extend(rule.body.constraints.iter().map(rewrite));
            let Some(substitution) = facts::case_facts(&constraints, &substitution) else {
                // Keep the normal literal-false discharge obligation. Dropping
                // the final error rule would lose a program check, not prove it.
                if trust_mc_core::chc::rule_is_error_obligation(rule) {
                    rules.push(Rule::new(
                        RuleBody::new(None, vec![Expr::bool_const(false)]),
                        rule.head.clone(),
                    ));
                }
                continue;
            };
            let rewrite = |e: &Expr| substitute_vars(e, &substitution);
            let body = rule.body.relation.as_ref().map(|body| {
                RelationApp::new(
                    if body_slot.is_some() {
                        variant_name(body.name.as_str(), b as u64)
                    } else {
                        body.name.to_string()
                    },
                    // Keep the body binder in its original position. The guard
                    // binds it to the case value; substituting a literal here
                    // would also defeat the core constant-parameter stripping
                    // pass's variable-binding convention.
                    body.args.as_ref().clone(),
                )
            });
            for h in 0..if head_slot.is_some() { variants } else { 1 } {
                let mut constraints = constraints.clone();
                let mut args: Vec<_> = rule.head.args.iter().map(rewrite).collect();
                if let Some(slot) = head_slot {
                    let head_guard = guard(args[slot].clone(), h as u64);
                    if trust_mc_core::chc_const_prop::eval::try_eval_to_bool(&head_guard)
                        == Some(false)
                    {
                        continue;
                    }
                    constraints.push(head_guard);
                    if (h as u64) <= bound {
                        args[slot] = literal(h as u64);
                    }
                }
                let name = if head_slot.is_some() {
                    variant_name(rule.head.name.as_str(), h as u64)
                } else {
                    rule.head.name.to_string()
                };
                rules.push(Rule::new(
                    RuleBody::new(body.clone(), constraints),
                    RelationApp::new(name, args),
                ));
            }
        }
    }
    let mut relations = Vec::new();
    for decl in &vc.relations {
        if slots.contains_key(&decl.name) {
            for k in 0..variants as u64 {
                relations
                    .push(RelationDecl::new(variant_name(&decl.name, k), decl.arg_sorts.clone()));
            }
        } else {
            relations.push(decl.clone());
        }
    }
    vc.rules = rules;
    vc.relations = relations;
    vc.propagate_constants();
    vc.prune_orphan_block_rules();
}
