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

use super::{
    Env, Expr, IncomingEdge, Place, RefPointees, Sort, SortInner, StatementCodegen, VariantFact,
};
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
    /// Any repeat-array shortcut recorded for that NAME is withdrawn first: the
    /// `[value; N]` side table says "this name's value is N copies of E", and a
    /// new value bound to the name makes that a stale answer. `codegen_assign`
    /// re-records it immediately after this call when the rvalue really is a
    /// `Repeat`, so the shortcut survives exactly the assignment that
    /// establishes it.
    ///
    /// Without the withdrawal the READ side kept answering from the shortcut
    /// while the array register moved underneath it: `let p = &mut a;
    /// p[0].x = 9; assert!(a[0].x == 0)` was VERIFICATION:- SUCCESSFUL with
    /// [AY:PROOF_QUALIFIERS:clean] — `try_codegen_datatype_field_assign`
    /// stored the updated element into the array and `Index projection:
    /// resolved repeated datatype array element` answered the read with the
    /// PRE-STORE element (pre-existing on origin/main fe89d6a0d; it surfaced
    /// on this branch once the repeat array stopped being unconstrained and
    /// the demotion that had masked it went away).
    ///
    /// ENSURES: `current_env[var_name]` = `expr` after call
    pub(super) fn env_update(&mut self, var_name: impl Into<std::sync::Arc<str>>, expr: Expr) {
        let var_name = var_name.into();
        if !self.repeat_array_values.is_empty() {
            self.repeat_array_values.remove(var_name.as_ref());
        }
        let is_datatype = expr.sort().is_datatype();
        // A root's FIRST binding cannot leave its derived entries stale: with
        // no earlier value of the root, they were written as components (a
        // tuple aggregate stores `{base}_field_{i}` and binds no root), and
        // the binding is the root's memory image when it is borrowed, a fresh
        // value no assertion ties to them. Re-selecting them from it made
        // `t.0` and `t.1` unconstrained
        // (`negative/elem_field_ref_depth.rs::tuple_field_array_elem_field_safe`,
        // undecided where main proves it).
        let had_value = self.current_env.insert(var_name.clone(), expr.clone()).is_some();
        if is_datatype && had_value {
            self.refresh_derived_field_entries(&var_name, &expr);
        }
    }

    /// Bring every derived field entry of `base` (`{base}_field_{i}...`, the
    /// name a field place and a borrow of it are kept under) in line with
    /// `base`'s new value `value`.
    ///
    /// A field place is read under its derived name first
    /// (`codegen_place`'s full-name lookup), and a write through a derived
    /// name is carried up into `base` (`try_propagate_deref_write_to_parent_datatype`),
    /// but nothing carried a write of `base` (a whole store, a field store
    /// through `(*r).f`, a direct `s.f = ..`) DOWN into the derived entries:
    /// after `let q = &mut s.a; *q = 1;` the entry `s_field_0` held 1, `r.a = 5`
    /// through `r = &mut s` updated `s` only, and `assert!(s.a == 1)` read the
    /// stale 1 and verified clean where Kani fails, while the true `s.a == 5`
    /// was certified a Genuine failure; a drop-glue borrow of `s.v` did the
    /// same to `s.v = vec![1, 2]` and `s.v.len() == 0` (walker fail-closed
    /// repair round 4, finding 7's class, `r6_bmc_field_stale.rs`,
    /// `r3_vec_through_ref.rs` `d5`, `r5_vec_field_store.rs` `f1`/`f2`/`f6`).
    ///
    /// An entry whose suffix is a chain of fields of single-constructor
    /// datatypes and of array elements (a constant index, or an index local
    /// assigned once and never borrowed, so its value now is its value when
    /// the entry was made) is re-selected from `value`; any other (a variant
    /// payload, an index that may have moved, a sort the selection does not
    /// reproduce) becomes a fresh value with a recorded sound havoc. Element
    /// steps matter: `let p = &mut h.a[0]; p.x = 9;` keeps `h.a[0]` as
    /// `h_field_0_idx_by_N`, and havocking it left
    /// `negative/elem_ref_field_stores.rs::two_stores_nested_container_safe`
    /// undecided where main proves it.
    fn refresh_derived_field_entries(&mut self, base: &str, value: &Expr) {
        let mut prefix = String::with_capacity(base.len() + 7);
        prefix.push_str(base);
        prefix.push_str("_field_");
        let range_start: std::sync::Arc<str> = std::sync::Arc::from(prefix.as_str());
        let derived: Vec<(std::sync::Arc<str>, Sort)> = self
            .current_env
            .range(range_start..)
            .take_while(|(key, _)| key.starts_with(prefix.as_str()))
            .map(|(key, expr)| (key.clone(), expr.sort().clone()))
            .collect();
        for (key, old_sort) in derived {
            // The entry a write is being carried up from, and those above it
            // on its chain, already hold what the root is built from; and an
            // entry that leaves that chain at a different FIELD of a
            // single-constructor value is a place the write does not touch
            // (`derived_write_source`). Re-selecting either only deepens the
            // term the solver sees: `t.0` after a write through
            // `&mut t.1[0].z` became a select of the rebuilt tuple, and
            // `negative/elem_field_ref_depth.rs::tuple_field_array_elem_field_safe`
            // went undecided where main proves it.
            if let Some(source) = self.derived_write_source.as_deref()
                && derived_entry_untouched_by_write(base, key.as_ref(), source)
            {
                continue;
            }
            let refreshed = derived_chain(&key[base.len()..])
                .and_then(|chain| self.select_derived_chain(base, value, &chain))
                .filter(|selected| *selected.sort() == old_sort);
            let new_value = match refreshed {
                Some(selected) => selected,
                None => {
                    let name = self.ctx.fresh_name("derived_field_refresh");
                    self.ctx.bmc_sound_havoc("derived_field_entry_unrefreshed");
                    self.ctx.declare_var(&name, old_sort)
                }
            };
            if !self.repeat_array_values.is_empty() {
                self.repeat_array_values.remove(key.as_ref());
            }
            self.current_env.insert(key, new_value);
        }
    }

    /// `value` selected along `chain` ([`select_field_chain`] for the field
    /// steps). An element step selects at a constant index, or at the current
    /// value of an index local of this body that is assigned once and never
    /// borrowed; `base` must be a local of this body for that.
    fn select_derived_chain(&self, base: &str, value: &Expr, chain: &[DerivedStep]) -> Option<Expr> {
        let mut current = value.clone();
        for step in chain {
            current = match *step {
                DerivedStep::Field(field_idx) => select_field_chain(&current, &[field_idx])?,
                DerivedStep::ConstIndex(offset) => {
                    let width = array_index_width(&current)?;
                    current.select(Expr::bitvec_const(u128::from(offset), width))
                }
                DerivedStep::IndexBy(local) => {
                    let fn_name = self.ctx.current_fn_name();
                    let mut fn_prefix = String::with_capacity(fn_name.len() + 8);
                    fn_prefix.push_str(fn_name);
                    fn_prefix.push_str("::local_");
                    if !base.starts_with(fn_prefix.as_str()) || !self.index_local_is_stable(local) {
                        return None;
                    }
                    let width = array_index_width(&current)?;
                    let index_name = crate::codegen_ay::names::local_name(fn_name, local);
                    let index = self.current_env.get(index_name.as_str())?.clone();
                    let index_width = index.sort().bitvec_width()?;
                    let index = match index_width.cmp(&width) {
                        std::cmp::Ordering::Equal => index,
                        std::cmp::Ordering::Less => index.zero_extend(width - index_width),
                        std::cmp::Ordering::Greater => return None,
                    };
                    current.select(index)
                }
            };
        }
        Some(current)
    }

    /// Is `local` assigned exactly once in this body (by a statement or as a
    /// call's destination) and never borrowed or pointed to?
    fn index_local_is_stable(&self, local: usize) -> bool {
        use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};
        let mut assigned = 0usize;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if place.local == local {
                    if !place.projection.is_empty() {
                        return false;
                    }
                    assigned += 1;
                }
                if let Rvalue::Ref(_, _, borrowed) | Rvalue::AddressOf(_, borrowed) = rvalue
                    && borrowed.local == local
                {
                    return false;
                }
            }
            if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
                && destination.local == local
            {
                assigned += 1;
            }
        }
        assigned == 1
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

    /// [`Self::record_violation_guarded_with_message`] for a check that is in
    /// the program, which no `--no-overflow-checks` or
    /// `--no-memory-safety-checks` removes ([`CheckGate::Always`]): a MIR
    /// `Assert` terminator, a model of one (std's `Sum`), or an assertion
    /// Kani's compiler writes. The label still names the property.
    ///
    /// [`CheckGate::Always`]: crate::codegen_ay::context::CheckGate::Always
    pub(super) fn record_violation_guarded_ungated(
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
        self.ctx.record_property_violation_gated(
            guarded,
            label,
            location,
            message,
            guard,
            crate::codegen_ay::context::CheckGate::Always,
        );
    }
}

/// The field indices of a derived-entry suffix made only of `_field_{i}`
/// segments (`_field_0_field_2` is `[0, 2]`), or `None` for any other suffix.
/// A step of a derived entry's name past its root (`codegen_place`'s
/// `_field_{i}`, `_idx_by_{local}` and `_cidx_{offset}` spellings).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DerivedStep {
    Field(usize),
    IndexBy(usize),
    ConstIndex(u64),
}

/// The steps of a derived entry's suffix, or `None` for any other spelling (a
/// variant payload, a deref, an index from the end, a dotted component).
fn derived_chain(suffix: &str) -> Option<Vec<DerivedStep>> {
    let mut chain = Vec::new();
    let mut rest = suffix;
    while !rest.is_empty() {
        let (make, tail): (fn(u64) -> Option<DerivedStep>, &str) =
            if let Some(tail) = rest.strip_prefix("_field_") {
                (|n| usize::try_from(n).ok().map(DerivedStep::Field), tail)
            } else if let Some(tail) = rest.strip_prefix("_idx_by_") {
                (|n| usize::try_from(n).ok().map(DerivedStep::IndexBy), tail)
            } else if let Some(tail) = rest.strip_prefix("_cidx_") {
                if tail.starts_with("end_") {
                    return None;
                }
                (|n| Some(DerivedStep::ConstIndex(n)), tail)
            } else {
                return None;
            };
        let digits = tail.bytes().take_while(u8::is_ascii_digit).count();
        if digits == 0 {
            return None;
        }
        chain.push(make(tail[..digits].parse().ok()?)?);
        rest = &tail[digits..];
    }
    (!chain.is_empty()).then_some(chain)
}

/// Is the derived entry `key` of `base` untouched by a write carried up from
/// the derived name `source`: `key` is `source` or above it on its chain, or
/// leaves that chain at a different field (where `base` and every step down
/// to the divergence are field or element steps)? An entry below `source`, or
/// one that leaves at an element step (another index may name the same
/// element), is not.
fn derived_entry_untouched_by_write(base: &str, key: &str, source: &str) -> bool {
    if source.strip_prefix(key).is_some_and(|rest| rest.is_empty() || rest.starts_with('_')) {
        return true;
    }
    let (Some(key_suffix), Some(source_suffix)) = (key.strip_prefix(base), source.strip_prefix(base)) else {
        return false;
    };
    let (Some(key_chain), Some(source_chain)) = (derived_chain(key_suffix), derived_chain(source_suffix)) else {
        return false;
    };
    for (key_step, source_step) in key_chain.iter().zip(source_chain.iter()) {
        if key_step == source_step {
            continue;
        }
        return matches!(
            (key_step, source_step),
            (DerivedStep::Field(a), DerivedStep::Field(b)) if a != b
        );
    }
    false
}

/// The bitvector width of `array`'s index sort.
fn array_index_width(array: &Expr) -> Option<u32> {
    let SortInner::Array(array_sort) = array.sort().inner() else {
        return None;
    };
    array_sort.index_sort.bitvec_width()
}

/// `value` selected along `chain`, each step a field of a single-constructor
/// datatype; `None` anywhere else.
fn select_field_chain(value: &Expr, chain: &[usize]) -> Option<Expr> {
    let mut current = value.clone();
    for &field_idx in chain {
        let SortInner::Datatype(dt) = current.sort().inner() else {
            return None;
        };
        if dt.constructors.len() != 1 {
            return None;
        }
        let field = dt.constructors[0].fields.get(field_idx)?;
        let (dt_name, field_name, field_sort) =
            (dt.name.clone(), field.name.clone(), field.sort.clone());
        current = current.try_field_select(dt_name, field_name, field_sort).ok()?;
    }
    Some(current)
}

#[cfg(test)]
mod derived_field_refresh_tests {
    use super::{DerivedStep, derived_chain, select_field_chain};
    use ay_bindings::{Expr, Sort};

    /// The derived-entry suffixes a field or element place is kept under
    /// parse to their steps; any other suffix (a variant, an index from the
    /// end, a deref, a dotted component) does not, and is havocked rather than
    /// re-selected (walker fail-closed repair round 4, `r6_bmc_field_stale.rs`,
    /// `negative/elem_ref_field_stores.rs`).
    #[test]
    fn test_derived_field_chain_parses_only_field_chains() {
        use DerivedStep::{ConstIndex, Field, IndexBy};
        assert_eq!(derived_chain("_field_0"), Some(vec![Field(0)]));
        assert_eq!(derived_chain("_field_1_field_12"), Some(vec![Field(1), Field(12)]));
        assert_eq!(derived_chain("_field_0_idx_by_7"), Some(vec![Field(0), IndexBy(7)]));
        assert_eq!(derived_chain("_cidx_2_field_1"), Some(vec![ConstIndex(2), Field(1)]));
        assert_eq!(derived_chain(""), None);
        assert_eq!(derived_chain("_field_"), None);
        assert_eq!(derived_chain("_field_0_cidx_end_1"), None);
        assert_eq!(derived_chain("_field_0_variant_1_field_0"), None);
        assert_eq!(derived_chain("_field_0.1"), None);
        assert_eq!(derived_chain("_field_0_deref"), None);
    }

    /// A write carried up from `t_field_1_idx_by_7_field_1` leaves the entries
    /// above it and those at another field alone; an entry below it, or at
    /// another index of the same array, is re-selected.
    #[test]
    fn test_derived_entry_untouched_by_write() {
        use super::derived_entry_untouched_by_write as untouched;
        let source = "f::local_1_field_1_idx_by_7_field_1";
        let base = "f::local_1";
        assert!(untouched(base, source, source), "the source itself");
        assert!(untouched(base, "f::local_1_field_1", source), "an ancestor");
        assert!(untouched(base, "f::local_1_field_1_idx_by_7", source), "an ancestor");
        assert!(untouched(base, "f::local_1_field_0", source), "another field");
        assert!(untouched(base, "f::local_1_field_1_idx_by_7_field_0", source), "another field");
        assert!(!untouched(base, "f::local_1_field_1_idx_by_8_field_1", source), "another index may alias");
        assert!(!untouched(base, "f::local_1_field_1_idx_by_7_field_1_field_0", source), "below the source");
        assert!(untouched(base, "f::local_1_field_10", source), "field 10: another field, not an ancestor");
        assert!(!untouched(base, "f::local_1_field_0_variant_1_field_0", source), "unparsed spelling");
    }

    /// A derived entry is re-selected from the root's new value: after `r.a =
    /// 5` through `r = &mut s`, the entry `s_field_0` is `s'.a`, not the 1 an
    /// earlier `*q = 1` left there (the root write never reached it, and
    /// `assert!(s.a == 1)` verified clean where Kani fails).
    #[test]
    fn test_select_field_chain_follows_single_constructor_fields() {
        let inner = Sort::struct_type("In", [("x", Sort::bitvec(8)), ("y", Sort::bitvec(16))]);
        let outer = Sort::struct_type("Out", [("a", Sort::bitvec(8)), ("b", inner.clone())]);
        let root = Expr::var("root", outer);
        let a = select_field_chain(&root, &[0]).expect("field 0");
        assert_eq!(a.sort(), &Sort::bitvec(8));
        let y = select_field_chain(&root, &[1, 1]).expect("field 1 then 1");
        assert_eq!(y.sort(), &Sort::bitvec(16));
        assert!(select_field_chain(&root, &[2]).is_none(), "no field 2");
        assert!(select_field_chain(&root, &[0, 0]).is_none(), "a bitvector has no fields");
        let either = Sort::enum_type(
            "Either",
            [("L", vec![("l", Sort::bitvec(8))]), ("R", vec![("r", Sort::bitvec(8))])],
        );
        assert!(select_field_chain(&Expr::var("e", either), &[0]).is_none(), "multi-constructor");
    }
}
