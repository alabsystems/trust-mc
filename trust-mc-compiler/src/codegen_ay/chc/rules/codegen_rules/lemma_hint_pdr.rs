// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! PDR lemma hint bridge for loop invariant detection.
//!
//! Collects `ExtractedLoopInvariant` entries for the `LOOP_INVARIANT_REGISTRY`,
//! which the driver-side pipeline converts to PDR `LemmaHint` objects for
//! ay-chc-native.
//!
//! Extracted from `lemma_hint.rs` — Part of #3927.
//! Part of #3258: CHC lemma injection for last 2 UNKNOWN harnesses.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::kani_middle::transform::loop_contracts::ExtractedLoopInvariant;
use rustc_public::mir::BasicBlockIdx;

use super::lemma_hint::{IncrSource, LoopModification};

/// Shared inputs for PDR hint collection.
///
/// Part of #3517: keeps the PDR helper signatures focused on the pattern data
/// instead of re-threading the same lookup tables and output vector.
pub(super) struct PdrHintContext<'a> {
    pub comparison_targets: &'a HashMap<Arc<str>, HashSet<Arc<str>>>,
    pub name_to_local: &'a HashMap<Arc<str>, usize>,
    pub name_to_rel_arg_pos: &'a HashMap<Arc<str>, usize>,
    pub out: &'a mut Vec<ExtractedLoopInvariant>,
}

/// Collect PDR lemma hints from detected modification patterns at a loop header.
///
/// Dispatches to pattern-specific collectors. Does NOT borrow ctx mutably;
/// only reads from the owned `name_to_local` and `name_to_rel_arg_pos` maps.
pub(super) fn collect_pdr_hints(
    header_bb: usize,
    modifications: &HashMap<&str, &LoopModification>,
    live_int_vars: &[&str],
    pdr_ctx: &mut PdrHintContext<'_>,
) {
    collect_forward_accumulator_pdr(header_bb, modifications, pdr_ctx);
    collect_countdown_accumulator_pdr(header_bb, modifications, live_int_vars, pdr_ctx);
}

/// Forward accumulator PDR hints: sum += counter; counter += 1
///
/// Produces hints with `captured_N` placeholder formulas:
/// - `(= (+ (* 2 captured_0) captured_1) (* captured_1 captured_1))` (2*sum + counter = counter²)
/// - `(<= captured_1 captured_2)` (counter <= bound)
fn collect_forward_accumulator_pdr(
    header_bb: usize,
    modifications: &HashMap<&str, &LoopModification>,
    pdr_ctx: &mut PdrHintContext<'_>,
) {
    for (&accum_name, &accum_mod) in modifications {
        let LoopModification::IncrementBy(IncrSource::Variable(counter_name)) = accum_mod else {
            continue;
        };
        // Part of #2267: rebind as &str to avoid .as_str() on Arc<str>.
        let counter_name: &str = counter_name;
        if !matches!(
            modifications.get(counter_name),
            Some(LoopModification::IncrementBy(IncrSource::Constant(1)))
        ) {
            continue;
        }

        let Some(&sum_local) = pdr_ctx.name_to_local.get(accum_name) else { continue };
        let Some(&counter_local) = pdr_ctx.name_to_local.get(counter_name) else { continue };

        // Part of #3258: Compute per-BB relation argument positions.
        let sum_pos = pdr_ctx.name_to_rel_arg_pos.get(accum_name).copied();
        let counter_pos = pdr_ctx.name_to_rel_arg_pos.get(counter_name).copied();
        let rel_positions = sum_pos.zip(counter_pos).map(|(s, c)| vec![s, c]);

        // Hint: 2*sum + counter = counter²
        pdr_ctx.out.push(ExtractedLoopInvariant {
            loop_head_bb: header_bb as BasicBlockIdx,
            loop_latch_bb: None,
            chc_loop_head_bb: None,
            captured_vars: vec![sum_local, counter_local],
            closure_def_index: None,
            formula_smt2: Some(
                "(= (+ (* 2 captured_0) captured_1) (* captured_1 captured_1))".to_string(),
            ),
            captured_rel_arg_positions: rel_positions,
        });

        // Hint: counter <= bound for each comparison target
        if let Some(bounds) = pdr_ctx.comparison_targets.get(counter_name) {
            for bound_name in bounds {
                if let Some(&bound_local) = pdr_ctx.name_to_local.get(bound_name.as_ref()) {
                    let bound_pos = pdr_ctx.name_to_rel_arg_pos.get(bound_name.as_ref()).copied();
                    let bound_positions = counter_pos.zip(bound_pos).map(|(c, b)| vec![c, b]);

                    pdr_ctx.out.push(ExtractedLoopInvariant {
                        loop_head_bb: header_bb as BasicBlockIdx,
                        loop_latch_bb: None,
                        chc_loop_head_bb: None,
                        captured_vars: vec![counter_local, bound_local],
                        closure_def_index: None,
                        formula_smt2: Some("(<= captured_0 captured_1)".to_string()),
                        captured_rel_arg_positions: bound_positions,
                    });
                }
            }
        }
    }
}

/// Countdown accumulator PDR hints: sum += n; counter -= 1
///
/// Produces hints with `captured_N` placeholder formulas:
/// - `(= (+ captured_0 (* captured_1 captured_2)) (* captured_2 captured_2))` (sum + counter*n = n²)
/// - `(>= captured_0 0)` (counter >= 0)
/// - `(>= captured_0 0)` (sum >= 0)
/// - `(<= captured_0 captured_1)` (counter <= n)
fn collect_countdown_accumulator_pdr(
    header_bb: usize,
    modifications: &HashMap<&str, &LoopModification>,
    live_int_vars: &[&str],
    pdr_ctx: &mut PdrHintContext<'_>,
) {
    for (&accum_name, &accum_mod) in modifications {
        let LoopModification::IncrementBy(IncrSource::Variable(invariant_name)) = accum_mod else {
            continue;
        };
        // Part of #2267: rebind as &str to avoid .as_str() on Arc<str>.
        let invariant_name: &str = invariant_name;
        if modifications.contains_key(invariant_name) {
            continue;
        }
        if !live_int_vars.contains(&invariant_name) {
            continue;
        }

        for (&counter_name, &counter_mod) in modifications {
            if counter_name == accum_name {
                continue;
            }
            if !matches!(counter_mod, LoopModification::DecrementBy(IncrSource::Constant(1))) {
                continue;
            }

            let Some(&sum_local) = pdr_ctx.name_to_local.get(accum_name) else { continue };
            let Some(&counter_local) = pdr_ctx.name_to_local.get(counter_name) else { continue };
            let Some(&n_local) = pdr_ctx.name_to_local.get(invariant_name) else { continue };

            // Part of #3258: Compute per-BB relation argument positions.
            let sum_pos = pdr_ctx.name_to_rel_arg_pos.get(accum_name).copied();
            let counter_pos = pdr_ctx.name_to_rel_arg_pos.get(counter_name).copied();
            let n_pos = pdr_ctx.name_to_rel_arg_pos.get(invariant_name).copied();

            // Hint: sum + counter * n = n²
            let scn_positions =
                sum_pos.zip(counter_pos).zip(n_pos).map(|((s, c), n)| vec![s, c, n]);
            pdr_ctx.out.push(ExtractedLoopInvariant {
                loop_head_bb: header_bb as BasicBlockIdx,
                loop_latch_bb: None,
                chc_loop_head_bb: None,
                captured_vars: vec![sum_local, counter_local, n_local],
                closure_def_index: None,
                formula_smt2: Some(
                    "(= (+ captured_0 (* captured_1 captured_2)) (* captured_2 captured_2))"
                        .to_string(),
                ),
                captured_rel_arg_positions: scn_positions,
            });

            // Hint: counter >= 0
            pdr_ctx.out.push(ExtractedLoopInvariant {
                loop_head_bb: header_bb as BasicBlockIdx,
                loop_latch_bb: None,
                chc_loop_head_bb: None,
                captured_vars: vec![counter_local],
                closure_def_index: None,
                formula_smt2: Some("(>= captured_0 0)".to_string()),
                captured_rel_arg_positions: counter_pos.map(|c| vec![c]),
            });

            // Hint: sum >= 0
            pdr_ctx.out.push(ExtractedLoopInvariant {
                loop_head_bb: header_bb as BasicBlockIdx,
                loop_latch_bb: None,
                chc_loop_head_bb: None,
                captured_vars: vec![sum_local],
                closure_def_index: None,
                formula_smt2: Some("(>= captured_0 0)".to_string()),
                captured_rel_arg_positions: sum_pos.map(|s| vec![s]),
            });

            // Hint: counter <= n
            let cn_positions = counter_pos.zip(n_pos).map(|(c, n)| vec![c, n]);
            pdr_ctx.out.push(ExtractedLoopInvariant {
                loop_head_bb: header_bb as BasicBlockIdx,
                loop_latch_bb: None,
                chc_loop_head_bb: None,
                captured_vars: vec![counter_local, n_local],
                closure_def_index: None,
                formula_smt2: Some("(<= captured_0 captured_1)".to_string()),
                captured_rel_arg_positions: cn_positions,
            });
        }
    }
}
