// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Complete, ordered model queries for concrete playback. Auxiliary equalities
//! only name existing expressions; they add no restriction on program inputs.

use super::AYCtx;
use crate::codegen_ay::types::bool_sort;
use ay_bindings::{Expr, Sort};

impl AYCtx<'_, '_> {
    /// Record a native nondeterministic input with its statement's execution guard.
    pub(in crate::codegen_ay) fn record_kani_any_var(&mut self, expr: Expr, guard: Option<Expr>) {
        self.record_playback_value(expr, guard, true);
    }

    /// A solver-only value has no native input to consume. If its site executes,
    /// refuse playback instead of inventing a value or shifting the input stream.
    pub(in crate::codegen_ay) fn record_unreplayable_playback_value(
        &mut self,
        expr: Expr,
        guard: Option<Expr>,
    ) {
        self.record_playback_value(expr, guard, false);
    }

    fn record_playback_value(&mut self, expr: Expr, guard: Option<Expr>, replayable: bool) {
        let ordinal = self.any_vars.len() / 3;
        // Snapshot suffix assumptions at the input site. Later failed asserts
        // must not suppress earlier inputs, and inputs after a failure are inactive.
        let guard = match (&self.assumption_context, guard) {
            (Some(context), Some(path)) => context.clone().and(path),
            (Some(context), None) => context.clone(),
            (None, Some(path)) => path,
            (None, None) => Expr::bool_const(true),
        };
        let active = self.declare_var(&format!("ay_playback_guard_{ordinal}"), bool_sort());
        self.assert(active.clone().eq(guard));
        let value = self.declare_var(&format!("ay_playback_value_{ordinal}"), expr.sort().clone());
        self.assert(value.clone().eq(expr));
        let supported = self.declare_var(&format!("ay_playback_replayable_{ordinal}"), bool_sort());
        self.assert(supported.clone().eq(Expr::bool_const(replayable)));
        self.any_vars.extend([active, value, supported]);
    }

    /// Emit before check-sat, including for a harness with no inputs. The count
    /// lets the consumer distinguish a valid empty stream from truncated output.
    pub(in crate::codegen_ay) fn finalize_playback_inputs(&mut self) {
        let name = "ay_playback_count";
        if !self.var_map.contains_key(name) {
            let count = self.declare_var(name, Sort::bitvec(64));
            self.assert(count.eq(Expr::bitvec_const((self.any_vars.len() / 3) as u64, 64)));
        }
    }

    /// Used by both direct SMT emission and emit_bmc. Keep aliases and the count
    /// together so secondary model queries can request the same complete stream.
    pub(in crate::codegen_ay) fn playback_model_queries(&mut self) -> Vec<Expr> {
        self.finalize_playback_inputs();
        let mut queries = self.any_vars.clone();
        queries.push(self.var_map["ay_playback_count"].clone());
        queries
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::context::with_test_ay_ctx;

    #[test]
    fn playback_queries_snapshot_path_and_suffix_guards_in_creation_order() {
        with_test_ay_ctx(|mut ctx| {
            let branch = ctx.declare_var("branch", bool_sort());
            let first = ctx.declare_var("first", Sort::bitvec(16));
            ctx.record_kani_any_var(first, Some(branch.clone()));
            ctx.add_ordered_assumption(branch.not());
            let second = ctx.declare_var("second", Sort::bitvec(8));
            ctx.record_kani_any_var(second, None);
            let queries = ctx.playback_model_queries();
            let query_names: Vec<_> = queries.iter().map(ToString::to_string).collect();
            assert_eq!(
                query_names,
                [
                    "ay_playback_guard_0",
                    "ay_playback_value_0",
                    "ay_playback_replayable_0",
                    "ay_playback_guard_1",
                    "ay_playback_value_1",
                    "ay_playback_replayable_1",
                    "ay_playback_count",
                ]
            );
            let smt = ctx.program.to_string();
            assert!(smt.contains("(= ay_playback_guard_0 branch)"), "{smt}");
            assert!(smt.contains("(= ay_playback_guard_1 ay_assume_ctx_"), "{smt}");
            assert!(
                smt.contains(&format!("(= ay_playback_count {})", Expr::bitvec_const(2u64, 64))),
                "{smt}"
            );
        });
    }

    #[test]
    fn solver_only_values_are_explicitly_unreplayable() {
        with_test_ay_ctx(|mut ctx| {
            let value = ctx.declare_var("havoc", bool_sort());
            ctx.record_unreplayable_playback_value(value, Some(Expr::bool_const(false)));
            let smt = ctx.program.to_string();
            assert!(smt.contains("(= ay_playback_replayable_0 false)"), "{smt}");
            assert!(smt.contains("(= ay_playback_guard_0 false)"), "{smt}");
        });
    }
}
