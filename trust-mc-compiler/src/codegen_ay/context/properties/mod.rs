// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Property tracking for AY codegen context.
//!
//! Manages property violations, cover properties, kani::any variables,
//! and unsupported construct diagnostics.
//! Extracted from context.rs as part of #2093.

use ay_bindings::Expr;
use std::fmt::Write as _;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::codegen_ay::types::bool_sort;
use trust_mc_core::artifact::PropertyMetadata;
use trust_mc_core::decl::Decl;
use trust_mc_core::ident::{PropertyId, SourceLocation};
use trust_mc_core::violation::{PropertyKind, Violation};

use super::AYCtx;

/// Telemetry counter for unsupported construct fallback hits (#3017).
/// Tracks when `ctx.unsupported_with_fallback()` is called — i.e., an unsupported
/// construct was encountered but codegen proceeded with incorrect/fallback data
/// rather than bailing early. Each hit represents a potential false-proof vector.
static UNSUPPORTED_CONSTRUCT_FALLBACK_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Reset the unsupported construct fallback counter, returning the previous value.
pub(in crate::codegen_ay) fn take_unsupported_construct_fallback_count() -> usize {
    UNSUPPORTED_CONSTRUCT_FALLBACK_COUNT.swap(0, Ordering::Relaxed)
}

/// Non-destructive read of the unsupported construct fallback counter (Part of #3080).
pub(in crate::codegen_ay) fn get_unsupported_construct_fallback_count() -> usize {
    UNSUPPORTED_CONSTRUCT_FALLBACK_COUNT.load(Ordering::Relaxed)
}

/// Set unsupported construct fallback counter for test isolation (Part of #3369).
#[cfg(test)]
#[allow(dead_code)]
pub(in crate::codegen_ay) fn set_unsupported_construct_fallback_count_for_test(count: usize) {
    UNSUPPORTED_CONSTRUCT_FALLBACK_COUNT.store(count, Ordering::Relaxed);
}

/// Telemetry counter for unconstrained assignment hits (#3192).
/// Tracks when `codegen_assign` receives `None` from `codegen_rvalue`, leaving
/// the LHS SSA variable declared but unconstrained. Distinct from
/// `UNSUPPORTED_CONSTRUCT_FALLBACK_COUNT` which tracks fallback-data paths.
static UNCONSTRAINED_ASSIGNMENT_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Reset the unconstrained assignment counter, returning the previous value.
pub(in crate::codegen_ay) fn take_unconstrained_assignment_count() -> usize {
    UNCONSTRAINED_ASSIGNMENT_COUNT.swap(0, Ordering::Relaxed)
}

/// Non-destructive read of the unconstrained assignment counter.
pub(in crate::codegen_ay) fn get_unconstrained_assignment_count() -> usize {
    UNCONSTRAINED_ASSIGNMENT_COUNT.load(Ordering::Relaxed)
}

/// Set unconstrained assignment counter for test isolation (Part of #3369).
#[cfg(test)]
#[allow(dead_code)]
pub(in crate::codegen_ay) fn set_unconstrained_assignment_count_for_test(count: usize) {
    UNCONSTRAINED_ASSIGNMENT_COUNT.store(count, Ordering::Relaxed);
}

impl<'tcx, 't> AYCtx<'tcx, 't> {
    /// Add an assertion to the AY program.
    pub(in crate::codegen_ay) fn assert(&mut self, expr: Expr) {
        // Dual-write: add to both program and bmc_vc
        self.program.assert(expr.clone());
        self.bmc_vc.add_constraint(expr);
    }

    /// Record a property violation predicate.
    ///
    /// `violation` should be satisfiable iff there exists an execution that reaches a violated
    /// property. These are OR'd together by `finalize_counterexample_query`.
    pub(in crate::codegen_ay) fn record_property_violation(
        &mut self,
        violation: Expr,
        label: &str,
    ) {
        self.record_property_violation_with_location(violation, label, None);
    }

    /// Record a property violation predicate with source location.
    ///
    /// Like `record_property_violation`, but also captures source location metadata
    /// for the violation. The location is included in the VC artifact sidecar
    /// for the driver to map solver results to source positions.
    pub(in crate::codegen_ay) fn record_property_violation_with_location(
        &mut self,
        violation: Expr,
        label: &str,
        location: Option<SourceLocation>,
    ) {
        self.record_property_violation_full(violation, label, location, None);
    }

    /// Record a property violation predicate with source location and message.
    ///
    /// Like `record_property_violation_with_location`, but also captures the
    /// human-readable property message (e.g. the assertion expression text
    /// `assertion failed: foo() == None`). The message is stored on the VC
    /// artifact so the driver can report it as the check description instead of
    /// a generic fallback. `message` should be `None` for checks that have no
    /// caller-supplied text (the driver derives a description from the label).
    pub(in crate::codegen_ay) fn record_property_violation_full(
        &mut self,
        violation: Expr,
        label: &str,
        location: Option<SourceLocation>,
        message: Option<String>,
    ) {
        self.record_property_violation_with_guard(violation, label, location, message, None);
    }

    /// Record a property violation predicate with an explicit reachability guard.
    ///
    /// Like `record_property_violation_full`, but additionally:
    /// - Conjoins the ordered assumption context (Kani assert-assume semantics):
    ///   the check is only failable on paths consistent with the assumptions
    ///   recorded before it in codegen order.
    /// - Emits a per-check reachability flag `ay_reach_<label>_<n>` defined as
    ///   `assumption_context ∧ guard` (the path condition at the check site).
    ///   The driver classifies the check UNREACHABLE when the solver proves
    ///   this flag unsatisfiable. The flag is omitted when both the guard and
    ///   the assumption context are trivially `true` (always reachable).
    pub(in crate::codegen_ay) fn record_property_violation_with_guard(
        &mut self,
        violation: Expr,
        label: &str,
        location: Option<SourceLocation>,
        message: Option<String>,
        guard: Option<Expr>,
    ) {
        let kind = Self::label_to_property_kind(label);
        if !self.should_emit_property_kind(kind) {
            return;
        }

        // Kani assert-assume ordering: conjoin the assumption context so this
        // check cannot fire on paths excluded by earlier assumptions.
        let violation = match &self.assumption_context {
            Some(assum_ctx) => assum_ctx.clone().and(violation),
            None => violation,
        };

        // Write to program (legacy path)
        let check_idx = self.label_counter;
        self.label_counter += 1;
        let mut name = String::with_capacity("ay_violation__".len() + label.len() + 20);
        name.push_str("ay_violation_");
        name.push_str(label);
        name.push('_');
        let _ = write!(&mut name, "{check_idx}");
        let pred = self.program.declare_const(&name, bool_sort());
        self.program.assert(pred.clone().eq(violation.clone()));
        self.property_violations.push(pred);

        // Reachability flag: assumption_context ∧ guard. A missing flag means
        // "trivially reachable" to the driver, so skip the trivial `true` case.
        let reach_expr = match (&self.assumption_context, guard) {
            (None, None) => None,
            (Some(assum_ctx), None) => Some(assum_ctx.clone()),
            (None, Some(g)) => Some(g),
            (Some(assum_ctx), Some(g)) => Some(assum_ctx.clone().and(g)),
        };
        let reach_name = reach_expr.map(|expr| {
            let mut rname = String::with_capacity("ay_reach__".len() + label.len() + 20);
            rname.push_str("ay_reach_");
            rname.push_str(label);
            rname.push('_');
            let _ = write!(&mut rname, "{check_idx}");
            // declare_var + assert dual-write to program and bmc_vc, so both
            // the legacy and emit_bmc payloads carry the flag definition.
            let rpred = self.declare_var(&rname, bool_sort());
            self.assert(rpred.eq(expr));
            rname
        });

        // Dual-write: add to bmc_vc.violations
        let property_id = PropertyId::new(self.property_counter);
        self.property_counter += 1;
        let mut viol = Violation::new(property_id, kind, violation).with_smt_var(name); // #1164: Store exact SMT var name for artifact mapping
        if let Some(loc) = location {
            viol = viol.with_location(loc);
        }
        if let Some(msg) = message {
            viol = viol.with_message(msg);
        }
        if let Some(rname) = reach_name {
            viol = viol.with_reach_var(rname);
        }
        self.bmc_vc.add_violation(viol);
    }

    /// Append a constraint to the ordered assumption context (assert-assume).
    ///
    /// CBMC/Kani semantics: an `assume` — including the assume half of
    /// `kani::assert`'s assert-assume lowering — constrains only the program
    /// suffix (checks recorded after it in codegen order). Asserting it
    /// globally would retroactively mask earlier failures (and, for a failing
    /// assert, mask the assert's own violation). Instead the constraint is
    /// folded into a chained Bool variable `ay_assume_ctx_<n>` that subsequent
    /// violation/cover/reach flags conjoin. The chained variable keeps the
    /// emitted formula linear in the number of assumptions.
    pub(in crate::codegen_ay) fn add_ordered_assumption(&mut self, constraint: Expr) {
        let combined = match self.assumption_context.take() {
            Some(prev) => prev.and(constraint),
            None => constraint,
        };
        let name = self.fresh_name("ay_assume_ctx");
        let pred = self.declare_var(&name, bool_sort());
        self.assert(pred.clone().eq(combined));
        self.assumption_context = Some(pred);
    }

    fn should_emit_property_kind(&self, kind: PropertyKind) -> bool {
        match kind {
            PropertyKind::ArithmeticOverflow => self.config.overflow_checks,
            PropertyKind::MemorySafety
            | PropertyKind::NullPointer
            | PropertyKind::OutOfBounds
            | PropertyKind::PointerOverflow => self.config.memory_safety_checks,
            _ => true,
        }
    }

    /// Map a violation label to the corresponding PropertyKind.
    fn label_to_property_kind(label: &str) -> PropertyKind {
        match label {
            "kani_assert" => PropertyKind::Assertion,
            "kani_assume" => PropertyKind::Assumption,
            "bounds_check" => PropertyKind::OutOfBounds,
            "div_by_zero_check" | "mod_by_zero_check" | "division_by_zero" => {
                PropertyKind::DivisionByZero
            }
            "overflow_check" | "overflow_check_neg" | "untranslatable_overflow_assert" => {
                PropertyKind::ArithmeticOverflow
            }
            l if l.starts_with("overflow_check_") => PropertyKind::ArithmeticOverflow,
            "null_pointer_check" => PropertyKind::NullPointer,
            "alignment_check" => PropertyKind::MemorySafety,
            "pointer_invalid" | "dead_object" => PropertyKind::MemorySafety,
            "use_after_free_check"
            | "double_free_check"
            | "dealloc_size_mismatch"
            | "dealloc_base_pointer_check" => PropertyKind::MemorySafety,
            "shift_distance_check" | "shift_distance_check_negative" => {
                PropertyKind::ArithmeticOverflow
            }
            "offset_value_overflow" | "offset_bytes_overflow" | "offset_result_overflow" => {
                PropertyKind::PointerOverflow
            }
            "enum_check" => PropertyKind::UndefinedBehavior,
            "coroutine_check" => PropertyKind::UndefinedBehavior,
            "unsupported_cfg_cycle" => PropertyKind::Unreachable,
            "panic" => PropertyKind::Panic,
            _ => PropertyKind::Other, // non-enum: &str
        }
    }

    /// Finalize the harness counterexample query.
    ///
    /// Adds a single assertion `(or viol_0 ... viol_n)` so SAT corresponds to a reachable
    /// counterexample and UNSAT corresponds to a proof.
    ///
    /// Also upgrades the logic to ALL if datatypes were declared (since QF_AUFBV etc.
    /// don't support algebraic datatypes).
    pub(in crate::codegen_ay) fn finalize_counterexample_query(&mut self) {
        // Upgrade logic if datatypes are present (QF_AUFBV doesn't support datatypes)
        self.program.upgrade_logic_for_datatypes();

        let any_violation = self
            .property_violations
            .iter()
            .cloned()
            .reduce(ay_bindings::Expr::or)
            .unwrap_or_else(|| Expr::bool_const(false));
        self.program.assert(any_violation);
    }

    /// Add get-value queries for property violation flags.
    ///
    /// Should be called after check-sat. The output allows the driver to identify
    /// which specific property was violated when the query is SAT.
    pub(in crate::codegen_ay) fn add_get_value_for_violations(&mut self) {
        if !self.property_violations.is_empty() {
            self.program.get_value(std::mem::take(&mut self.property_violations));
        }
    }

    /// Record a kani::any_raw symbolic variable for concrete playback.
    pub(in crate::codegen_ay) fn record_kani_any_var(&mut self, expr: Expr) {
        self.any_vars.push(expr);
    }

    /// Add get-value queries for kani::any_raw symbolic variables.
    pub(in crate::codegen_ay) fn add_get_value_for_kani_any(&mut self) {
        if !self.any_vars.is_empty() {
            self.program.get_value(std::mem::take(&mut self.any_vars));
        }
    }

    /// Record a cover property with source location and optional message (#1164).
    ///
    /// Like `record_cover_property`, but stores location metadata for the VC artifact.
    pub(in crate::codegen_ay) fn record_cover_property_with_location(
        &mut self,
        condition: Expr,
        location: Option<SourceLocation>,
        message: Option<String>,
    ) -> u64 {
        // Kani assert-assume ordering: a cover after a failed assert (or after
        // an assume) is only satisfiable on paths consistent with the
        // assumption context recorded before it.
        let condition = match &self.assumption_context {
            Some(assum_ctx) => assum_ctx.clone().and(condition),
            None => condition,
        };
        // Create a named predicate for the cover condition
        let cover_id = self.label_counter;
        let mut name = String::with_capacity("ay_cover_".len() + 20);
        name.push_str("ay_cover_");
        let _ = write!(&mut name, "{cover_id}");
        self.label_counter += 1;
        let pred = self.program.declare_const(&name, bool_sort());
        let pred_eq_condition = pred.clone().eq(condition);
        self.program.assert(pred_eq_condition.clone());
        self.cover_properties.push(pred.clone());

        // #922: Dual-write to bmc_vc for emit_bmc path
        self.bmc_vc.add_decl(Decl::constant(&name, bool_sort()));
        self.bmc_vc.add_constraint(pred_eq_condition);
        self.bmc_vc.add_model_query(pred);

        // #1164: Store cover metadata for VC artifact emission
        let property_id = PropertyId::new(self.property_counter);
        self.property_counter += 1;
        let mut metadata =
            PropertyMetadata::new(property_id, PropertyKind::Cover).with_smt_var(name);
        if let Some(loc) = location {
            metadata = metadata.with_location(loc);
        }
        if let Some(msg) = message {
            metadata = metadata.with_message(msg);
        }
        self.cover_metadata.push(metadata);

        cover_id
    }

    /// Add get-value queries for cover properties.
    ///
    /// Called after check-sat to determine which cover conditions are satisfiable.
    pub(in crate::codegen_ay) fn add_get_value_for_covers(&mut self) {
        if !self.cover_properties.is_empty() {
            self.program.get_value(std::mem::take(&mut self.cover_properties));
        }
    }

    /// Record a source coverage predicate.
    ///
    /// Coverage predicates are satisfiability queries over reachability of MIR
    /// coverage points. They are intentionally not included in the verification
    /// counterexample query.
    pub(in crate::codegen_ay) fn record_coverage_property_with_location(
        &mut self,
        condition: Expr,
        location: Option<SourceLocation>,
    ) -> u64 {
        // Coverage points after an abort/assume are not executed — conjoin the
        // ordered assumption context (same semantics as violations/covers).
        let condition = match &self.assumption_context {
            Some(assum_ctx) => assum_ctx.clone().and(condition),
            None => condition,
        };
        let coverage_id = self.label_counter;
        let mut name = String::with_capacity("ay_coverage_".len() + 20);
        name.push_str("ay_coverage_");
        let _ = write!(&mut name, "{coverage_id}");
        self.label_counter += 1;

        let pred = self.program.declare_const(&name, bool_sort());
        let pred_eq_condition = pred.clone().eq(condition);
        self.program.assert(pred_eq_condition.clone());
        self.coverage_properties.push(pred.clone());

        self.bmc_vc.add_decl(Decl::constant(&name, bool_sort()));
        self.bmc_vc.add_constraint(pred_eq_condition);
        self.bmc_vc.add_model_query(pred);

        let property_id = PropertyId::new(self.property_counter);
        self.property_counter += 1;
        let mut metadata =
            PropertyMetadata::new(property_id, PropertyKind::Other).with_smt_var(name);
        if let Some(loc) = location {
            metadata = metadata.with_location(loc);
        }
        self.coverage_metadata.push(metadata);

        coverage_id
    }

    /// Add get-value queries for source coverage predicates.
    pub(in crate::codegen_ay) fn add_get_value_for_coverage(&mut self) {
        if !self.coverage_properties.is_empty() {
            self.program.get_value(std::mem::take(&mut self.coverage_properties));
        }
    }

    /// Record an unsupported construct encountered during codegen.
    ///
    /// These are collected for diagnostics and don't immediately fail codegen.
    /// `construct` is `&'static str` because all callers pass string literals,
    /// avoiding a `.to_owned()` allocation per call (~90 call sites). Part of #2267.
    pub(in crate::codegen_ay) fn unsupported(
        &mut self,
        construct: &'static str,
        location: impl Into<String>,
    ) {
        self.unsupported_constructs.entry(construct).or_default().push(location.into());
    }

    /// Total number of unsupported-construct records on this ctx (all
    /// categories, including the plain diagnostics-only `unsupported()` ones
    /// that bump NO atomic counter). Iterator unrolling snapshots this so an
    /// in-path unsupported cut inside an inlined per-element closure cannot
    /// masquerade as a sound unroll (the cut leaves downstream checks
    /// UNREACHABLE, which partial-vacuity V4 does not catch).
    pub(in crate::codegen_ay) fn unsupported_construct_total(&self) -> usize {
        self.unsupported_constructs.values().map(Vec::len).sum()
    }

    /// Record an unsupported construct that proceeds with fallback data (#3017).
    ///
    /// Like `unsupported()`, but also increments the global demotion counter.
    /// Use this when codegen proceeds with incorrect/fallback data rather than
    /// bailing early (returning None/Unsupported). The counter feeds into the
    /// driver's verdict demotion pipeline to prevent false proofs.
    pub(in crate::codegen_ay) fn unsupported_with_fallback(
        &mut self,
        construct: &'static str,
        location: impl Into<String>,
    ) {
        let location = location.into();
        tracing::debug!(construct, %location, "unsupported_with_fallback recorded");
        self.unsupported(construct, location);
        UNSUPPORTED_CONSTRUCT_FALLBACK_COUNT.fetch_add(1, Ordering::Relaxed);
    }

    /// Record an unconstrained assignment (#3192).
    ///
    /// Called when `codegen_rvalue` returns `None` in the BMC assignment path,
    /// leaving the LHS SSA variable declared but unconstrained. Also records
    /// the construct as unsupported for diagnostics. The counter feeds into
    /// the driver's verdict demotion pipeline as a distinct category from
    /// `unsupported_construct_fallback`.
    pub(in crate::codegen_ay) fn unconstrained_assignment(
        &mut self,
        construct: &'static str,
        location: impl Into<String>,
    ) {
        self.unsupported(construct, location);
        UNCONSTRAINED_ASSIGNMENT_COUNT.fetch_add(1, Ordering::Relaxed);
    }
}

#[cfg(test)]
mod tests;
