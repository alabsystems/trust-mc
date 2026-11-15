// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Compose a destructor's running metadata with the subsequent outer free.

use crate::codegen_ay::chc::{
    ChcCtx,
    codegen_expr_heap::{obj_size_in, obj_size_out, obj_valid_in, obj_valid_out},
};
use ay_bindings::{Expr, ExprValue};
use std::collections::{HashMap, HashSet};

fn node(e: &Expr) -> usize {
    std::ptr::from_ref(e.value()) as usize
}

fn rewrite(expression: &Expr, substitutions: &HashMap<String, Expr>) -> Option<Expr> {
    let mut pending = vec![(expression.clone(), false)];
    let mut memo = HashMap::new();
    let mut budget = 16_384usize;
    while let Some((expr, expanded)) = pending.pop() {
        budget = budget.checked_sub(1)?;
        let id = node(&expr);
        if memo.contains_key(&id) {
            continue;
        }
        if let ExprValue::Var { name } = expr.value() {
            memo.insert(id, substitutions.get(name).cloned().unwrap_or(expr));
        } else if !expanded {
            pending.push((expr.clone(), true));
            pending.extend(expr.children().cloned().map(|child| (child, false)));
        } else {
            let children = expr
                .children()
                .map(|child| memo.get(&node(child)).cloned())
                .collect::<Option<Vec<_>>>()?;
            let changed = expr.children().zip(&children).any(|(old, new)| node(old) != node(new));
            if changed && !expr.value().is_known_variant() {
                return None;
            }
            memo.insert(
                id,
                if changed { ay_bindings::rebuild_with_children(&expr, children) } else { expr },
            );
        }
    }
    memo.remove(&node(expression))
}

fn lane(ctx: &ChcCtx<'_, '_>, input: Expr, output: &Expr, modified: bool) -> Option<Expr> {
    let definitions = ctx
        .heap_state
        .pending_updates
        .iter()
        .filter_map(|constraint| match constraint.value() {
            ExprValue::Eq(left, right) if left == output => Some(right),
            _ => None,
        })
        .collect::<Vec<_>>();
    let result = match definitions.as_slice() {
        [] if !modified => input,
        [value] => (*value).clone(),
        _ => return None,
    };
    let mut pending = vec![&result];
    let mut seen = HashSet::new();
    let mut budget = 16_384usize;
    while let Some(expr) = pending.pop() {
        budget = budget.checked_sub(1)?;
        if !seen.insert(node(expr)) {
            continue;
        }
        if matches!(expr.value(), ExprValue::Var{name} if name.ends_with("__out")) {
            return None;
        }
        pending.extend(expr.children());
    }
    Some(result)
}

/// The final free replaces its metadata output definitions. An earlier
/// observer of those names needs an event-time snapshot, which this bounded
/// composition does not invent. All real input expressions remain usable.
pub(super) fn metadata_observers_are_inputs(ctx: &ChcCtx<'_, '_>, observers: &[Expr]) -> bool {
    let result = (|| {
        let mut budget = 16_384usize;
        let mut seen = HashSet::new();
        let mut pending = observers.iter().collect::<Vec<_>>();
        while let Some(expr) = pending.pop() {
            budget = budget.checked_sub(1)?;
            if !seen.insert(node(expr)) {
                continue;
            }
            if matches!(expr.value(),ExprValue::Var{name} if name == "obj_valid__out" || name == "obj_size__out")
            {
                return None;
            }
            pending.extend(expr.children());
        }
        Some(())
    })();
    if result.is_none() {
        ctx.record_sound_fallback_reason("box_drop_event_time_metadata_unavailable");
    }
    result.is_some()
}

/// A readable prefix is insufficient for Rust's deallocation layout. Use the
/// current metadata expression after the destructor, never a birth-size cache.
pub(in crate::codegen_ay::chc) fn require_native_deallocation_extent(
    ctx: &mut ChcCtx<'_, '_>,
    object: Expr,
    bytes: u32,
) -> Option<()> {
    let Some(extent) =
        lane(ctx, obj_size_in(), &obj_size_out(), ctx.heap_state.is_obj_size_modified())
    else {
        ctx.record_sound_fallback_reason("box_drop_exact_deallocation_extent_unavailable");
        return None;
    };
    ctx.mark_heap_metadata_read();
    ctx.heap_state.pending_checks.push(extent.select(object).eq(Expr::bitvec_const(bytes, 32)));
    Some(())
}

/// `updates` is the outer free plan made by collect_box_dyn_dealloc_effects.
/// Compose its input lanes with the effects left by the actual destructor,
/// replacing those lanes' single pending definition rather than conjoining
/// contradictory definitions of __out. Refuse ambiguous/out-dependent state.
pub(in crate::codegen_ay::chc) fn compose_box_deallocation_updates(
    ctx: &mut ChcCtx<'_, '_>,
    updates: &[Expr],
) -> Option<Vec<Expr>> {
    if updates.is_empty() {
        return Some(Vec::new());
    }
    let result = (|| {
        let valid_out = obj_valid_out();
        let size_out = obj_size_out();
        let observers = ctx
            .heap_state
            .pending_updates
            .iter()
            .filter_map(|constraint| match constraint.value() {
                ExprValue::Eq(left, right) if *left == valid_out || *left == size_out => {
                    Some(right.clone())
                }
                _ => Some(constraint.clone()),
            })
            .chain(ctx.heap_state.pending_checks.iter().cloned())
            .collect::<Vec<_>>();
        if !metadata_observers_are_inputs(ctx, &observers) {
            return None;
        }
        let valid = lane(ctx, obj_valid_in(), &valid_out, ctx.heap_state.is_obj_valid_modified())?;
        let size = lane(ctx, obj_size_in(), &size_out, ctx.heap_state.is_obj_size_modified())?;
        let replacements = HashMap::from([
            ("obj_valid".to_owned(), valid.clone()),
            ("obj_size".to_owned(), size.clone()),
        ]);
        let rewritten =
            updates.iter().map(|e| rewrite(e, &replacements)).collect::<Option<Vec<_>>>()?;
        // Outer allocation must still be live after its destructor has run.
        for update in updates {
            if let ExprValue::Eq(left, right) = update.value()
                && *left == valid_out
                && let ExprValue::Store { index, .. } = right.value()
            {
                ctx.heap_state.pending_checks.push(crate::codegen_ay::chc::rules::codegen_rules_helpers::rust_dealloc_validity_guard(&valid, &size, index));
            }
        }
        ctx.heap_state.pending_updates.retain(|c| !matches!(c.value(), ExprValue::Eq(left,_) if *left == valid_out || *left == size_out));
        ctx.mark_heap_metadata_modified();
        Some(rewritten)
    })();
    if result.is_none() {
        ctx.record_sound_fallback_reason("box_drop_metadata_composition_unavailable");
    }
    result
}

/// A statement may already have mirrored a field into `mem_T__out` before
/// entering drop glue. A later store chain supersedes that definition only
/// when it contains the exact earlier memory expression and nobody observes
/// the old output lane. Otherwise retaining both definitions prunes execution;
/// deleting the old one changes event-time reads. Refuse that unresolved case.
pub(in crate::codegen_ay::chc) fn compose_host_drop_constraints(
    ctx: &ChcCtx<'_, '_>,
    shared: &[Expr],
    effects: &[Expr],
    checks: &[Expr],
) -> Option<Vec<Expr>> {
    fn tree_cost(root: &Expr, allowance: &mut usize) -> Option<usize> {
        let mut pending = vec![(root, 0usize)];
        let mut total = 0;
        while let Some((part, depth)) = pending.pop() {
            *allowance = allowance.checked_sub(1)?;
            if depth > 128 {
                return None;
            }
            total += 1;
            pending.extend(part.children().map(|child| (child, depth + 1)));
        }
        Some(total)
    }
    fn mentions(root: &Expr, name: &str, budget: &mut usize) -> Option<bool> {
        let mut pending = vec![root];
        let mut seen = HashSet::new();
        while let Some(part) = pending.pop() {
            *budget = budget.checked_sub(1)?;
            if !seen.insert(node(part)) {
                continue;
            }
            if matches!(part.value(),ExprValue::Var{name:found} if found==name) {
                return Some(true);
            }
            pending.extend(part.children());
        }
        Some(false)
    }
    let result = (|| {
        let mut remove = HashSet::new();
        let mut budget = 16_384usize;
        for (index, constraint) in shared.iter().enumerate() {
            let ExprValue::Eq(left, old) = constraint.value() else { continue };
            let ExprValue::Var { name } = left.value() else { continue };
            let definitions = effects
                .iter()
                .filter_map(|effect| match effect.value() {
                    ExprValue::Eq(output, new) if output == left => Some(new),
                    _ => None,
                })
                .collect::<Vec<_>>();
            let [new] = definitions.as_slice() else {
                if definitions.is_empty() {
                    continue;
                }
                return None;
            };
            for (other_index, other) in shared.iter().enumerate() {
                if other_index != index && mentions(other, name, &mut budget)? {
                    return None;
                }
            }
            for effect in effects {
                if matches!(effect.value(), ExprValue::Eq(output, _) if output == left) {
                    continue;
                }
                if mentions(effect, name, &mut budget)? {
                    return None;
                }
            }
            if checks
                .iter()
                .map(|check| mentions(check, name, &mut budget))
                .collect::<Option<Vec<_>>>()?
                .into_iter()
                .any(|v| v)
                || mentions(new, name, &mut budget)?
            {
                return None;
            }
            let mut pending = vec![*new];
            let mut found = false;
            while let Some(candidate) = pending.pop() {
                budget = budget.checked_sub(1)?;
                if node(candidate) == node(old) {
                    found = true;
                    break;
                }
                // Structural identity is exact, and compared only after both
                // trees' actual work and depth fit the shared bounded budget.
                let mut allowance = budget;
                if tree_cost(old, &mut allowance).is_some()
                    && tree_cost(candidate, &mut allowance).is_some()
                {
                    budget = allowance;
                    if candidate == old {
                        found = true;
                        break;
                    }
                }
                pending.extend(candidate.children());
            }
            if !found {
                return None;
            }
            remove.insert(index);
        }
        Some(
            shared
                .iter()
                .enumerate()
                .filter(|(index, _)| !remove.contains(index))
                .map(|(_, value)| value.clone())
                .collect(),
        )
    })();
    if result.is_none() {
        ctx.record_sound_fallback_reason("box_drop_statement_memory_composition_unavailable");
    }
    result
}
