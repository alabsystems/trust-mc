// Copyright 2026 Andrew Yates, Inc.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Identity-position detection for CHC constant propagation.

use std::collections::{HashMap, HashSet};

use ay_bindings::ExprValue;

use crate::chc::Rule;

/// Detects positions in a self-referential rule where the head arg is an
/// identity pass-through of the body arg at the same position.
///
/// For a rule `R(a, b, c) ∧ (b_out = b) ⟹ R(a_out, b_out, c_out)`:
/// position 1 is identity because `b_out` maps to `b` through the equality
/// chain, and `b` is the body arg at position 1.
///
/// Returns an empty set for non-self-referential rules.
pub(super) fn detect_identity_positions(rule: &Rule) -> HashSet<usize> {
    let mut identity = HashSet::new();

    let body_rel = match &rule.body.relation {
        Some(rel) => rel,
        None => return identity,
    };

    if body_rel.name.as_str() != rule.head.name.as_str() {
        return identity;
    }

    let mut var_equiv: HashMap<String, String> = HashMap::new();
    for expr in &rule.body.constraints {
        if let ExprValue::Eq(lhs, rhs) = expr.value() {
            if let (ExprValue::Var { name: a }, ExprValue::Var { name: b }) =
                (lhs.value(), rhs.value())
            {
                var_equiv.insert(a.clone(), b.clone());
                var_equiv.insert(b.clone(), a.clone());
            }
        }
    }

    let min_len = rule.head.args.len().min(body_rel.args.len());
    for i in 0..min_len {
        let head_arg = &rule.head.args[i];
        let body_arg = &body_rel.args[i];

        let head_name = match head_arg.value() {
            ExprValue::Var { name } => name,
            _ => continue,
        };
        let body_name = match body_arg.value() {
            ExprValue::Var { name } => name,
            _ => continue,
        };

        if head_name == body_name
            || var_equiv.get(head_name).is_some_and(|target| target == body_name)
        {
            identity.insert(i);
        }
    }

    identity
}
