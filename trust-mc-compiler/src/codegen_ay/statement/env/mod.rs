// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Environment and path condition management for statement codegen.
//!
//! This module handles:
//! - Block entry environment initialization with phi merging
//! - Path condition tracking for guarded assertions
//! - Outgoing edge recording for control flow
//! - Violation recording with path condition guards
//!
//! Part of #2408: decomposed from monolithic env.rs (649 LOC).

mod edge_flow;
mod phi;
mod sort_harmonize;

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use super::{Env, Expr, IncomingEdge, Place, Sort, SortInner, StatementCodegen, VariantFact};
use ay_bindings::ExprValue;
use tracing::warn;

/// Counter for BigInt phi conversion fresh variable names.
/// Hoisted from function-local static for session reset support (Part of #2360).
pub(super) static BIGINT_CONVERT_CTR: AtomicU64 = AtomicU64::new(0);

/// Reset the BigInt conversion counter, returning the previous value (Part of #2360).
pub(super) fn take_bigint_convert_counter() -> u64 {
    BIGINT_CONVERT_CTR.swap(0, Ordering::Relaxed)
}

/// Unsoundness counter: sort_harmonize fresh-var fallbacks (#3263).
///
/// Counts events where sort harmonization creates a fresh unconstrained
/// symbolic variable, destroying value information at phi merge points.
/// Classified as SOUND_APPROXIMATION in the driver: fresh symbolics are
/// universally quantified, so PROOF under this model is valid (proved for
/// all possible values). CTREX results with nonzero counts are classified
/// as OverApproximation (counterexamples may be spurious). Part of #3366.
static SORT_HARMONIZE_FRESH_VAR_COUNT: AtomicUsize = AtomicUsize::new(0);

pub(super) fn record_sort_harmonize_fresh_var() {
    SORT_HARMONIZE_FRESH_VAR_COUNT.fetch_add(1, Ordering::Relaxed);
}

pub(in crate::codegen_ay) fn get_sort_harmonize_fresh_var_count() -> usize {
    SORT_HARMONIZE_FRESH_VAR_COUNT.load(Ordering::Relaxed)
}

/// Take (consume + reset) the sort harmonize fresh-var counter (#3263).
pub(in crate::codegen_ay) fn take_sort_harmonize_fresh_var_count() -> usize {
    SORT_HARMONIZE_FRESH_VAR_COUNT.swap(0, Ordering::Relaxed)
}

/// Set sort harmonize fresh-var counter for test isolation (Part of #3369).
#[cfg(test)]
#[allow(dead_code)]
pub(in crate::codegen_ay) fn set_sort_harmonize_fresh_var_count_for_test(count: usize) {
    SORT_HARMONIZE_FRESH_VAR_COUNT.store(count, Ordering::Relaxed);
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    fn ssa_init_symbol_name(base_name: &str, sort: &Sort) -> String {
        use std::fmt::Write;
        use std::hash::{Hash, Hasher};

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        // Hash the sort directly — Sort implements Hash via its Arc<SortInner>.
        // Avoids allocating a temporary String via format!("{:?}", ...).
        sort.hash(&mut hasher);
        // Part of #2267: pre-allocate instead of format!().
        let mut name = String::with_capacity(base_name.len() + 27);
        name.push_str(base_name);
        name.push_str("__ssa_init_");
        let _ = write!(name, "{:016x}", hasher.finish());
        name
    }

    fn get_or_declare_ssa_init_symbol(&mut self, base_name: &str, sort: &Sort) -> Expr {
        let symbol_name = Self::ssa_init_symbol_name(base_name, sort);
        if let Some(existing) = self.ctx.lookup_var(&symbol_name) {
            return existing.clone();
        }
        self.ctx.declare_var(&symbol_name, sort.clone())
    }

    /// Look up a variable's current expression in the environment.
    ///
    /// ENSURES: Returns Some if `var_name` exists in `current_env`
    pub(super) fn env_lookup(&self, var_name: &str) -> Option<&Expr> {
        self.current_env.get(var_name)
    }

    /// Update a variable's expression in the current environment.
    ///
    /// ENSURES: `current_env[var_name]` = `expr` after call
    pub(super) fn env_update(&mut self, var_name: impl Into<std::sync::Arc<str>>, expr: Expr) {
        self.current_env.insert(var_name.into(), expr);
    }

    pub(super) fn resolve_concrete_expr(&self, expr: &Expr) -> Expr {
        if let ExprValue::Var { name } = expr.value()
            && let Some(concrete) = self.ssa_concrete_values.get(name)
        {
            return concrete.clone();
        }
        expr.clone()
    }

    /// Collect piecewise storage entries that belong to a flattened value.
    ///
    /// Flattened Option-like enums (#2076) and checked-arithmetic tuples store
    /// their components under derived keys rather than as a single datatype:
    ///   - `{base}.0`                          — discriminant / first element
    ///   - `{base}.1`                          — payload / second element
    ///   - `{base}_variant_{V}_field_{F}`      — enum variant payloads
    ///   - `{base}_field_{F}`                  — flattened tuple/struct fields
    ///
    /// Returns `(suffix, expr)` pairs so a whole-value move/copy can re-key the
    /// entries onto the destination base. Part of #4112 follow-up: without this,
    /// copying a flattened enum drops its discriminant link, so `discriminant(x)`
    /// falls back to an unconstrained symbolic and Downcast payload reads return
    /// None (EncodingGap demotions on iterator-protocol MIR).
    pub(super) fn collect_flattened_value_entries(
        env: &Env,
        src_base: &str,
    ) -> Vec<(String, Expr)> {
        let mut entries = Vec::new();
        // Dotted element keys: `{base}.0` / `{base}.1`.
        for dotted in [".0", ".1"] {
            let mut key = String::with_capacity(src_base.len() + dotted.len());
            key.push_str(src_base);
            key.push_str(dotted);
            if let Some(expr) = env.get(key.as_str()) {
                entries.push((dotted.to_string(), expr.clone()));
            }
        }
        // Underscore-prefixed projection keys: `{base}_variant_...`, `{base}_field_...`.
        for pfx in ["_variant_", "_field_"] {
            let mut prefix = String::with_capacity(src_base.len() + pfx.len());
            prefix.push_str(src_base);
            prefix.push_str(pfx);
            let range_start: std::sync::Arc<str> = std::sync::Arc::from(prefix.as_str());
            for (key, expr) in
                env.range(range_start..).take_while(|(k, _)| k.starts_with(prefix.as_str()))
            {
                entries.push((key[src_base.len()..].to_string(), expr.clone()));
            }
        }
        entries
    }

    /// Re-key collected flattened-value entries onto a destination base.
    ///
    /// Declares a fresh SSA variable for each `{dest_base}{suffix}` key and
    /// constrains it to the source expression with `assert_ssa_def` (ite
    /// semantics under the current path condition), then publishes the new
    /// variable in the environment. Sound: each entry is an exact copy of a
    /// component of the value being moved. Part of #4112 follow-up.
    pub(super) fn apply_flattened_value_entries(
        &mut self,
        dest_base: &str,
        entries: Vec<(String, Expr)>,
    ) {
        for (suffix, expr) in entries {
            let mut dest_key = String::with_capacity(dest_base.len() + suffix.len());
            dest_key.push_str(dest_base);
            dest_key.push_str(&suffix);
            let dest_name = self.ssa_name_from_base(&dest_key, true);
            let dest_var = self.ctx.declare_var(&dest_name, expr.sort().clone());
            self.assert_ssa_def(dest_var.clone(), expr, &dest_key);
            self.env_update(dest_key, dest_var);
        }
    }

    /// Assert an SSA variable definition with `ite` semantics under path conditions.
    ///
    /// When no path condition is active, asserts `lhs = rhs` unconditionally.
    /// When a path condition `pc` is active and a previous value exists in the env
    /// for `base_name`, asserts `lhs = ite(pc, rhs, prev)` — preserving the old
    /// value when the path is not taken. This prevents SSA variables from being
    /// unconstrained on untaken paths, which would allow the solver to assign
    /// arbitrary values and produce spurious counterexamples (#2081).
    ///
    /// REQUIRES: lhs_expr is a freshly declared SSA variable
    /// ENSURES: lhs_expr is constrained to rhs_expr when pc is true,
    ///          or to previous env value when pc is false
    pub(super) fn assert_ssa_def(&mut self, lhs_expr: Expr, rhs_expr: Expr, base_name: &str) {
        let signed = self.signedness_from_base_name(base_name);
        // Coerce rhs to match lhs sort when they differ (#2244).
        // The lhs is the freshly declared SSA variable whose sort downstream code expects.
        let rhs_expr = if *lhs_expr.sort() != *rhs_expr.sort() {
            let rhs_sort = rhs_expr.sort().clone();
            let coerced = self.convert_expr_to_sort_declared(rhs_expr, lhs_expr.sort(), signed);
            if *coerced.sort() != *lhs_expr.sort() {
                // Coercion failed — use a fresh symbolic variable instead of silently
                // dropping the constraint. Without this, lhs_expr is completely
                // unconstrained, allowing the solver to pick any value (#2533).
                warn!(
                    "assert_ssa_def: unresolvable sort mismatch for {base_name}: \
                     lhs={:?} rhs={:?} — using symbolic fallback (#2533)",
                    lhs_expr.sort(),
                    rhs_sort
                );
                self.ctx.unsupported_with_fallback(
                    "assert_ssa_def sort mismatch",
                    format!("{base_name}: lhs={:?} rhs={:?}", lhs_expr.sort(), rhs_sort),
                );
                // Fall through with a fresh symbolic variable of the correct sort.
                // This keeps the lhs constrained (via ITE with path condition) rather
                // than leaving it free for the solver to exploit.
                self.get_or_declare_ssa_init_symbol(base_name, lhs_expr.sort())
            } else {
                coerced
            }
        } else {
            rhs_expr
        };
        if self.current_path_condition.is_none() {
            self.cache_ssa_concrete_value(&lhs_expr, rhs_expr.clone());
            self.ctx.assert(lhs_expr.eq(rhs_expr));
            return;
        }
        // Resolve else_expr while borrowing self mutably (env_lookup + get_or_declare).
        // Clone env lookup result to release borrow before potential mutable calls.
        let else_expr = match self.env_lookup(base_name).cloned() {
            Some(prev_expr) if prev_expr.sort() == rhs_expr.sort() => prev_expr,
            Some(prev_expr) => {
                let converted_prev =
                    self.convert_expr_to_sort_declared(prev_expr, rhs_expr.sort(), signed);
                if converted_prev.sort() == rhs_expr.sort() {
                    converted_prev
                } else {
                    warn!(
                        "assert_ssa_def: failed to reconcile sort mismatch for {base_name}; \
                         using symbolic pre-state value"
                    );
                    self.get_or_declare_ssa_init_symbol(base_name, rhs_expr.sort())
                }
            }
            None => {
                // First conditional definition for this base in the current path.
                // Seed a stable symbolic pre-state value so untaken paths keep a
                // consistent value instead of leaving the SSA variable unconstrained.
                self.get_or_declare_ssa_init_symbol(base_name, rhs_expr.sort())
            }
        };
        // Clone pc after else_expr is resolved — avoids holding borrow across match.
        // Fallback: if path condition disappeared (should not happen — guarded at line 109),
        // assert unconditional equality rather than silently dropping the constraint.
        let Some(pc) = self.current_path_condition.clone() else {
            self.ctx.assert(lhs_expr.eq(rhs_expr));
            return;
        };
        let rhs_with_path = Expr::ite(pc, rhs_expr, else_expr);
        self.cache_ssa_concrete_value(&lhs_expr, rhs_with_path.clone());
        self.ctx.assert(lhs_expr.eq(rhs_with_path));
    }

    fn cache_ssa_concrete_value(&mut self, lhs_expr: &Expr, rhs_expr: Expr) {
        if let ExprValue::Var { name } = lhs_expr.value() {
            self.ssa_concrete_values.insert(name.clone(), rhs_expr);
        }
    }

    /// Declare an SSA variable for `destination`, bind it to `result` via `assert_ssa_def`,
    /// and update the environment.
    ///
    /// Consolidates the common 5-line pattern:
    /// ```text
    /// let base_name = self.ssa_base_name(destination);
    /// let dest_name = self.ssa_name_from_base(&base_name, true);
    /// let dest_expr = self.ctx.declare_var(&dest_name, result.sort().clone());
    /// self.assert_ssa_def(dest_expr.clone(), result, &base_name);
    /// self.env_update(base_name, dest_expr);
    /// ```
    ///
    /// Eliminates one `dest_expr.clone()` and one `result.sort().clone()` per callsite.
    pub(super) fn bind_ssa_result(&mut self, destination: &Place, result: Expr) {
        let base_name = self.ssa_base_name(destination);
        let dest_name = self.ssa_name_from_base(&base_name, true);
        let dest_expr = self.ctx.declare_var(&dest_name, result.sort().clone());
        // Cache the concrete value before SSA indirection (#3107).
        // Expr is Arc-based so clone is a reference count increment.
        self.ssa_concrete_values.insert(dest_name, result.clone());
        self.assert_ssa_def(dest_expr.clone(), result, &base_name);
        self.env_update(base_name, dest_expr);
    }

    /// Assert a constraint guarded by the current path condition using implication.
    ///
    /// This is for auxiliary constraints (pointer validity, assume, etc.) that
    /// should be vacuously true when the path is not taken. NOT for SSA variable
    /// definitions — use `assert_ssa_def` for those (#2081).
    ///
    /// ENSURES: When pc is None, asserts constraint unconditionally
    /// ENSURES: When pc is Some, asserts `pc => constraint`
    pub(super) fn assert_guarded(&mut self, constraint: Expr) {
        match &self.current_path_condition {
            None => self.ctx.assert(constraint),
            Some(pc) => {
                self.ctx.assert(pc.clone().implies(constraint));
            }
        }
    }

    /// Record a property violation guarded by the current path condition.
    ///
    /// Takes a `violation` predicate (true when the property is violated). For path condition `pc`,
    /// records `pc ∧ violation`. Callers pass the negation of what should hold:
    /// - For `assert!(cond)`, pass `cond.not()` (violation when cond is false)
    /// - For overflow checks, pass `no_overflow.not()` (violation when overflow occurs)
    ///
    /// These are OR'd together by `finalize_counterexample_query`, so SAT = counterexample.
    ///
    /// REQUIRES: violation.sort().is_bool()
    /// ENSURES: Adds (path_condition ∧ violation) to ctx.violations
    /// ENSURES: If path_condition is None, adds bare violation
    pub(super) fn record_violation_guarded(&mut self, violation: Expr, label: &str) {
        let guard = self.current_path_condition.clone();
        let guarded = match &guard {
            None => violation,
            Some(path_cond) => path_cond.clone().and(violation),
        };
        // #1164: Pass source location for property location tracking.
        let location = self.current_source_location();
        // Thread the path condition so the ctx emits a per-check reachability
        // flag (driver-side UNREACHABLE classification).
        self.ctx.record_property_violation_with_guard(guarded, label, location, None, guard);
    }

    /// Record a property violation guarded by the current path condition,
    /// carrying a human-readable message (e.g. the assertion expression text).
    ///
    /// Like `record_violation_guarded`, but threads `message` to the VC artifact
    /// so the driver reports it as the check description instead of a generic
    /// label-derived fallback. `message` is `None` when no caller text exists.
    pub(super) fn record_violation_guarded_with_message(
        &mut self,
        violation: Expr,
        label: &str,
        message: Option<String>,
    ) {
        let guard = self.current_path_condition.clone();
        let guarded = match &guard {
            None => violation,
            Some(path_cond) => path_cond.clone().and(violation),
        };
        let location = self.current_source_location();
        self.ctx.record_property_violation_with_guard(guarded, label, location, message, guard);
    }
}
