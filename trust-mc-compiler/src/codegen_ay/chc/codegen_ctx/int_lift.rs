// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Int-lift helpers for CHC predicates.
//!
//! When `--ay-chc-int-lift` is enabled, BV sorts are lifted to Int in CHC
//! relation signatures. This lets Z3 PDR synthesize loop invariants in
//! LIA (linear integer arithmetic) instead of BV theory.
//!
//! Key constraint: Z3's `(declare-var name sort)` is global across ALL rules.
//! If any relation uses Int for a variable, ALL rules must use Int for that
//! same variable name. This forces global (not per-block) lifting.
//!
//! Extracted from `mod.rs` to stay within the 500-line file limit.
//! Part of #112: designs/2026-03-03-loop-invariant-synthesis.md Direction 2.

use ay_bindings::{Expr, Sort};

use crate::codegen_ay::types::int_sort;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Lift a BV sort to Int when int_lift mode is enabled.
    ///
    /// Part of #112 Direction 2: When `--ay-chc-int-lift` is active, BV sorts
    /// are replaced with Int sorts in CHC predicate signatures. This enables
    /// PDR to synthesize loop invariants in LIA (linear integer arithmetic)
    /// instead of BV theory, which PDR cannot handle for invariant synthesis.
    ///
    /// Returns the sort unchanged if int_lift is disabled or the sort is not BV.
    pub(in crate::codegen_ay::chc) fn lift_bv_to_int_if_enabled(&self, sort: Sort) -> Sort {
        if self.int_lift && sort.is_bitvec() {
            // Part of #4207: Skip int-lifting for BV128+ sorts.
            // `BigInt::from(1u128) << 128` produces a numeral that the AY SMT
            // parser cannot handle, crashing the native CHC solver. BV128 vars
            // (i128/u128) are rare and PDR does not need them in LIA.
            if sort.bitvec_width().is_some_and(|w| w >= 128) {
                return sort;
            }
            int_sort()
        } else {
            sort
        }
    }

    /// Lift BV to Int and return the original BV width if lifted.
    ///
    /// Used by `collect_state_vars` to record which vars were lifted for
    /// entry-rule bounding constraint generation (#112 Direction 2 step 2).
    pub(in crate::codegen_ay::chc) fn lift_bv_sort_recording_width(
        &self,
        sort: Sort,
    ) -> (Sort, Option<u32>) {
        if self.int_lift {
            if let Some(width) = sort.bitvec_width() {
                // Part of #4207: Skip int-lifting for BV128+ (same as above).
                if width >= 128 {
                    return (sort, None);
                }
                return (int_sort(), Some(width));
            }
        }
        (sort, None)
    }

    /// Build state-variable expressions projected to a block's live set.
    ///
    /// Part of #2214: per-block CHC relation signatures.
    /// Part of #112 Direction 2: Uses sorts directly from state_vars, which
    /// already have Int for int-lifted locals (including Range/IndexRange
    /// fields when int-lift is active).
    pub(in crate::codegen_ay::chc) fn project_state_args(&self, bb_idx: usize) -> Vec<Expr> {
        self.state_var_mgr.live_state_indices[bb_idx]
            .iter()
            .map(|&idx| {
                let (name, sort) = &self.state_var_mgr.state_vars[idx];
                Expr::var(&**name, sort.clone())
            })
            .collect()
    }

    /// Build range-bound constraints for Int-lifted variables.
    ///
    /// Only emits bounds for vars recorded in `int_lifted_vars` (vars whose
    /// sorts were lifted from BV to Int during collect_state_vars, including
    /// Range/IndexRange fields when int-lift is active).
    ///
    /// Returns empty Vec if int_lift is disabled.
    /// Part of #112 Direction 2.
    pub(in crate::codegen_ay::chc) fn int_lift_range_constraints(
        &self,
        bb_idx: usize,
    ) -> Vec<Expr> {
        if !self.int_lift || self.int_lifted_vars.is_empty() {
            return Vec::new();
        }
        let mut constraints = Vec::new();
        for &idx in &self.state_var_mgr.live_state_indices[bb_idx] {
            // Only emit bounds for vars that were actually lifted to Int.
            // Part of #2267: O(1) HashMap lookup (was O(n) linear search).
            let Some(&(width, is_signed)) = self.int_lifted_vars.get(&idx) else {
                continue;
            };
            let (name, _sort) = &self.state_var_mgr.state_vars[idx];
            let int_var = Expr::var(&**name, int_sort());
            // Part of #3169: Use signed or unsigned bounds.
            if is_signed {
                let lower = Expr::int_const(-(num_bigint::BigInt::from(1u128) << (width - 1)));
                let upper = Expr::int_const(num_bigint::BigInt::from(1u128) << (width - 1));
                constraints.push(int_var.clone().int_ge(lower));
                constraints.push(int_var.int_lt(upper));
            } else {
                let zero = Expr::int_const(0i64);
                let upper = Expr::int_const(num_bigint::BigInt::from(1u128) << width);
                constraints.push(int_var.clone().int_ge(zero));
                constraints.push(int_var.int_lt(upper));
            }
        }
        constraints
    }

    /// Build BV-range bounding constraints for Int-lifted nondet output variables.
    ///
    /// When `int_lift` is enabled and a local is assigned via kani::any() (nondet),
    /// the output variable is unconstrained (existentially quantified in CHC).
    /// Unlike BV sorts which are inherently bounded [0, 2^w), Int sorts are unbounded
    /// and can take negative values. This causes spurious counterexamples where
    /// e.g. `kani::any::<u64>()` returns -5, which satisfies `kani::assume(n < 1B)`
    /// but violates unsigned postconditions.
    ///
    /// This method generates `0 <= x_out < 2^w` constraints for each Int-lifted
    /// state var slot occupied by the given local (including flattened tuple fields).
    ///
    /// Part of #112 Direction 2 step 3: nondet output bounding.
    pub(in crate::codegen_ay::chc) fn int_lift_nondet_bounds(
        &self,
        dest_local: usize,
    ) -> Vec<Expr> {
        if !self.int_lift {
            return Vec::new();
        }
        let mut constraints = Vec::new();
        let Some(vec_idx) = self.try_state_idx_for_local(dest_local) else {
            return Vec::new();
        };

        // Determine how many consecutive state var slots this local occupies.
        // Flattened locals (tuples, Option, Result) consume N slots.
        let field_count = if self.flatten.flattened_tuple_locals.contains(&dest_local) {
            self.flattened_field_count(dest_local)
        } else {
            1
        };

        for i in 0..field_count {
            let slot = vec_idx + i;
            let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(slot) else {
                continue;
            };
            if !out_sort.is_int() {
                continue;
            }
            // Find original BV width and signedness from int_lifted_vars.
            // Part of #2267: O(1) HashMap lookup (was O(n) linear search).
            let Some(&(width, is_signed)) = self.int_lifted_vars.get(&slot) else {
                continue;
            };
            let out_var = Expr::var(&**out_name, out_sort.clone());
            // Part of #3169: Use signed or unsigned bounds for nondet outputs.
            // Part of #112: Use BigInt to handle all widths including 128-bit
            // (1i128 << 127 wraps to i128::MIN, producing wrong bounds).
            if is_signed {
                let lower = Expr::int_const(-(num_bigint::BigInt::from(1u128) << (width - 1)));
                let upper = Expr::int_const(num_bigint::BigInt::from(1u128) << (width - 1));
                constraints.push(out_var.clone().int_ge(lower));
                constraints.push(out_var.int_lt(upper));
            } else {
                constraints.push(out_var.clone().int_ge(Expr::int_const(0)));
                let upper = Expr::int_const(num_bigint::BigInt::from(1u128) << width);
                constraints.push(out_var.int_lt(upper));
            }
        }
        constraints
    }

    /// Repair a stale `output_args` vector that was built before late state vars
    /// were added during call dispatch. Appends identity (input-var) entries for
    /// any suffix slots that were added after `output_args` was constructed.
    ///
    /// Part of #3815, #3561: D1 from `designs/2026-03-14-issue-3815-late-output-args-parity.md`.
    pub(in crate::codegen_ay::chc) fn refresh_full_output_args(
        &self,
        output_args: &[Expr],
    ) -> Vec<Expr> {
        let sv_len = self.state_var_mgr.state_vars.len();
        if output_args.len() == sv_len {
            return output_args.to_vec();
        }
        assert!(
            output_args.len() < sv_len,
            "refresh_full_output_args: output_args ({}) > state_vars ({})",
            output_args.len(),
            sv_len,
        );
        let mut refreshed = output_args.to_vec();
        for idx in output_args.len()..sv_len {
            // Late-added state vars get __out if modified, input var otherwise.
            if self.encode.modified_state_indices.contains(&idx) {
                if let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(idx) {
                    refreshed.push(Expr::var(&**out_name, out_sort.clone()));
                    continue;
                }
            }
            let (name, sort) = &self.state_var_mgr.state_vars[idx];
            refreshed.push(Expr::var(&**name, sort.clone()));
        }
        refreshed
    }

    /// Project full-arity output_args to a target block's live state indices.
    ///
    /// Part of #3815: D2 — repair stale `output_args` inside the choke point
    /// rather than spreading the fix through every call handler.
    pub(in crate::codegen_ay::chc) fn project_full_output_to_block(
        &self,
        to_bb: usize,
        output_args: &[Expr],
    ) -> Vec<Expr> {
        let refreshed = self.refresh_full_output_args(output_args);
        self.state_var_mgr.live_state_indices[to_bb]
            .iter()
            .map(|&idx| {
                let arg = refreshed[idx].clone();
                // Only wrap with bv2int for vars that were actually lifted to Int.
                // Relation parameter sort comes from state_vars[idx].1.
                let target_sort = &self.state_var_mgr.state_vars[idx].1;
                if target_sort.is_int() && arg.sort().is_bitvec() {
                    // Part of #3180: Use signed bv2int for signed types to preserve
                    // negative value semantics. Without this, -1i32 (BV 0xFFFFFFFF)
                    // becomes u32::MAX instead of -1, contradicting signed range
                    // constraints and potentially causing false PROOFs.
                    // Part of #2267: O(1) HashMap lookup (was O(n) linear search).
                    let is_signed =
                        self.int_lifted_vars.get(&idx).map(|(_, s)| *s).unwrap_or(false);
                    if is_signed { arg.bv2int_signed() } else { arg.bv2int() }
                } else {
                    arg
                }
            })
            .collect()
    }
}
