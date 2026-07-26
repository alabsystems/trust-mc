// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Invariant pattern detection for CHC loop lemma hints.
//!
//! Contains pattern matchers that identify accumulator idioms from
//! detected state-variable modifications at loop headers:
//! - Forward accumulator: `sum += counter; counter += 1`
//! - Countdown accumulator: `sum += n; counter -= 1`
//!
//! Extracted from `lemma_hint.rs` — Part of #3927.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use ay_bindings::Expr;
use tracing::debug;

use crate::codegen_ay::types::int_sort;

use super::lemma_hint::{IncrSource, InvariantHint, LoopModification};

/// Detect invariant patterns from state variable modifications at a loop header.
pub(super) fn detect_invariant_patterns(
    header_bb: usize,
    modifications: &HashMap<&str, &LoopModification>,
    live_int_vars: &[&str],
    comparison_targets: &HashMap<Arc<str>, HashSet<Arc<str>>>,
) -> Vec<InvariantHint> {
    let mut hints = Vec::new();
    detect_forward_accumulator(header_bb, modifications, comparison_targets, &mut hints);
    detect_countdown_accumulator(header_bb, modifications, live_int_vars, &mut hints);
    hints
}

/// Pattern 1: Forward accumulator — sum += counter; counter += 1
/// Invariant: sum <= counter * counter ∧ counter <= bound
fn detect_forward_accumulator(
    header_bb: usize,
    modifications: &HashMap<&str, &LoopModification>,
    comparison_targets: &HashMap<Arc<str>, HashSet<Arc<str>>>,
    hints: &mut Vec<InvariantHint>,
) {
    for (&accum_name, &accum_mod) in modifications {
        let LoopModification::IncrementBy(IncrSource::Variable(counter_name)) = accum_mod else {
            continue;
        };
        // Part of #2267: rebind as &str to avoid .as_str() on Arc<str>.
        let counter_name: &str = counter_name;

        // Check that counter_name is also modified and increments by 1.
        if let Some(LoopModification::IncrementBy(IncrSource::Constant(1))) =
            modifications.get(counter_name)
        {
            debug!(
                header_bb,
                accum = %accum_name,
                counter = %counter_name,
                "detected forward accumulator pattern"
            );

            let sum_var = Expr::var(accum_name, int_sort());
            let counter_var = Expr::var(counter_name, int_sort());

            // Hint 1: 2*sum + counter = counter² (exact triangular sum invariant)
            // At the loop header: sum = 0 + 1 + ... + (counter-1)
            // so 2*sum = counter*(counter-1) = counter² - counter
            // hence 2*sum + counter = counter²
            let two = Expr::int_const(num_bigint::BigInt::from(2));
            let two_sum = two.int_mul(sum_var);
            let lhs = two_sum.int_add(counter_var.clone());
            let counter_sq = counter_var.clone().int_mul(counter_var.clone());
            hints.push(InvariantHint {
                header_bb,
                negated_invariant: lhs.eq(counter_sq).not(),
                description: "forward accumulator: 2*sum + counter = counter²",
            });

            // Hint 4+: counter <= bound for the loop guard variable.
            // Bridges sum <= counter² to post-loop sum <= n*n: at exit
            // counter >= n (from guard) + counter <= n (hint) → counter = n.
            emit_bound_hints(header_bb, comparison_targets, counter_name, &counter_var, hints);
        }
    }
}

/// Emit `counter <= var` hints for the loop guard bound variable.
///
/// Uses comparison_targets (from scanning comparison expressions in
/// constraints) to identify which variable the counter is compared against
/// in the loop guard's SwitchInt. Only emits hints for those variables,
/// avoiding spurious hints for temporaries.
fn emit_bound_hints(
    header_bb: usize,
    comparison_targets: &HashMap<Arc<str>, HashSet<Arc<str>>>,
    counter_name: &str,
    counter_var: &Expr,
    hints: &mut Vec<InvariantHint>,
) {
    let Some(counter_comparisons) = comparison_targets.get(counter_name) else {
        return;
    };
    for bound_name in counter_comparisons {
        let bound_var = Expr::var(&**bound_name, int_sort());
        hints.push(InvariantHint {
            header_bb,
            negated_invariant: counter_var.clone().int_gt(bound_var),
            description: "forward accumulator: counter <= bound",
        });
        debug!(
            header_bb,
            counter = %counter_name,
            bound = %bound_name,
            "emitting counter <= bound hint"
        );
    }
}

/// Pattern 2: Countdown accumulator — sum += n; counter -= 1
/// Invariant: sum + counter * n = n * n (where n is loop-invariant)
fn detect_countdown_accumulator(
    header_bb: usize,
    modifications: &HashMap<&str, &LoopModification>,
    live_int_vars: &[&str],
    hints: &mut Vec<InvariantHint>,
) {
    for (&accum_name, &accum_mod) in modifications {
        let LoopModification::IncrementBy(IncrSource::Variable(invariant_name)) = accum_mod else {
            continue;
        };
        // Part of #2267: rebind as &str to avoid .as_str() on Arc<str>.
        let invariant_name: &str = invariant_name;

        // The invariant variable must NOT be modified in the loop.
        if modifications.contains_key(invariant_name) {
            continue;
        }

        // It must be live at the header.
        if !live_int_vars.contains(&invariant_name) {
            continue;
        }

        // Find a counter that decrements by 1.
        for (&counter_name, &counter_mod) in modifications {
            if counter_name == accum_name {
                continue;
            }
            if !matches!(counter_mod, LoopModification::DecrementBy(IncrSource::Constant(1))) {
                continue;
            }

            debug!(
                header_bb,
                accum = %accum_name,
                counter = %counter_name,
                invariant_var = %invariant_name,
                "detected countdown accumulator pattern"
            );

            let sum_var = Expr::var(accum_name, int_sort());
            let counter_var = Expr::var(counter_name, int_sort());
            let n_var = Expr::var(invariant_name, int_sort());
            let zero = Expr::int_const(num_bigint::BigInt::from(0));

            // Hint 1: sum + counter * n = n * n (core bilinear invariant)
            let counter_times_n = counter_var.clone().int_mul(n_var.clone());
            let n_squared = n_var.clone().int_mul(n_var.clone());
            let sum_plus_cn = sum_var.clone().int_add(counter_times_n);
            hints.push(InvariantHint {
                header_bb,
                negated_invariant: sum_plus_cn.eq(n_squared).not(),
                description: "countdown accumulator: sum + counter*n = n²",
            });

            // Hint 2: counter >= 0 (counter never goes negative)
            hints.push(InvariantHint {
                header_bb,
                negated_invariant: counter_var.clone().int_ge(zero.clone()).not(),
                description: "countdown accumulator: counter >= 0",
            });

            // Hint 3: sum >= 0 (accumulator non-negative)
            hints.push(InvariantHint {
                header_bb,
                negated_invariant: sum_var.clone().int_ge(zero.clone()).not(),
                description: "countdown accumulator: sum >= 0",
            });

            // Hint 4: counter <= n (counter bounded by initial value)
            hints.push(InvariantHint {
                header_bb,
                negated_invariant: counter_var.int_le(n_var).not(),
                description: "countdown accumulator: counter <= n",
            });
        }
    }
}
