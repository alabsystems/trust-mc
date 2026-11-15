// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Discharge only literal contradictions in a proposed partition case.
//! All original equalities/guards remain in the emitted rule. These facts
//! simplify its head and reject impossible cases, never constrain execution.
use super::substitute_vars;
use ay_bindings::{Expr, ExprValue};
use std::collections::HashMap;
use trust_mc_core::chc_const_prop::eval::{try_eval_to_bool, try_eval_to_const};

pub(super) fn case_facts(
    constraints: &[Expr],
    initial: &HashMap<String, Expr>,
) -> Option<HashMap<String, Expr>> {
    let mut flat = Vec::new();
    let mut stack: Vec<_> = constraints.iter().collect();
    while let Some(e) = stack.pop() {
        if let ExprValue::And(parts) = e.value() {
            stack.extend(parts);
        } else {
            flat.push(e);
        }
    }
    let mut known = initial.clone();
    loop {
        let old = known.len();
        for e in &flat {
            if let ExprValue::Eq(lhs, rhs) = e.value() {
                for (var, value) in [(lhs, rhs), (rhs, lhs)] {
                    let ExprValue::Var { name } = var.value() else { continue };
                    if known.contains_key(name) {
                        continue;
                    }
                    let Some(value) = try_eval_to_const(&substitute_vars(value, &known)) else {
                        continue;
                    };
                    if matches!(
                        value.value(),
                        ExprValue::BoolConst(_) | ExprValue::BitVecConst { .. }
                    ) {
                        known.insert(name.clone(), value);
                    }
                }
            }
        }
        if known.len() == old {
            break;
        }
    }
    let rewritten: Vec<_> = flat.iter().map(|e| substitute_vars(e, &known)).collect();
    if rewritten.iter().any(|e| try_eval_to_bool(e) == Some(false)) {
        return None;
    }
    // The symbolic cursor complement is still a real case. Drop a transition
    // only when it also requires the exact opposite unsigned comparison.
    for a in &rewritten {
        for b in &rewritten {
            let opposite = match (a.value(), b.value()) {
                (ExprValue::BvUGt(x, y), ExprValue::BvULe(u, v))
                | (ExprValue::BvUGe(x, y), ExprValue::BvULt(u, v)) => x == u && y == v,
                (ExprValue::Not(x), _) => x == b,
                _ => false,
            };
            if opposite {
                return None;
            }
        }
    }
    Some(known)
}
