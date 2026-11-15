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

/// Whether a `--no-overflow-checks` / `--no-memory-safety-checks` flag may
/// remove a BMC check.
///
/// Kani's two flags only take CBMC's instrumentation off (`cbmc_check_flags`
/// in kani-driver's call_cbmc.rs: `--signed-overflow-check`,
/// `--bounds-check`, …). The driver compiles every crate with
/// `-C overflow-checks=on`, as Kani does, and the checks that are in the
/// program itself stay whatever the flags say: rustc's MIR `Assert`
/// terminators, and the assertions Kani's compiler writes (an
/// `unchecked_*` intrinsic's UB, a SIMD lane's shift distance). The CHC lane
/// keeps every MIR `Assert` the same way (`emit_assert_error_rule_shared`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay) enum CheckGate {
    /// trust-mc's own instrumentation: the check's kind
    /// (`label_to_property_kind`) decides, through
    /// `should_emit_property_kind`.
    ByKind,
    /// A check in the program: no check flag removes it. Dropping one
    /// under a flag while the code after it still assumes it held (a MIR
    /// `Assert`'s edge condition) prunes the failing executions, so the
    /// harness verifies: a false proof.
    Always,
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
        self.record_property_violation_gated(
            violation,
            label,
            location,
            message,
            guard,
            CheckGate::ByKind,
        );
    }

    /// [`Self::record_property_violation_with_guard`] with an explicit
    /// [`CheckGate`]. The kind still comes from the label; under
    /// [`CheckGate::Always`] it only names the property and no check flag
    /// drops it.
    pub(in crate::codegen_ay) fn record_property_violation_gated(
        &mut self,
        violation: Expr,
        label: &str,
        location: Option<SourceLocation>,
        message: Option<String>,
        guard: Option<Expr>,
        gate: CheckGate,
    ) {
        let kind = Self::label_to_property_kind(label);
        if gate == CheckGate::ByKind && !self.should_emit_property_kind(kind) {
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
        crate::codegen_ay::emitter::define_property_flag(
            &mut self.program,
            pred.clone(),
            violation.clone(),
        );
        self.property_violations.push(pred);

        // Reachability flag: assumption_context ∧ guard. A missing flag means
        // "trivially reachable" to the driver, so skip the trivial `true` case.
        //
        // TWO independent reasons to withhold the reachability COMPANION flag.
        // The companion is what lets the driver reclassify a discharged check as
        // UNREACHABLE, so withholding it makes the check report the solver's own
        // verdict instead.
        //
        // 1. `unwind_assert` — Kani parity. The unwinding assertion is a
        //    CBMC-side check and CBMC's reachability instrumentation covers only
        //    Kani-codegen'd assertions, so Kani reports it SUCCESS or FAILURE,
        //    never UNREACHABLE (corpus: never-return pins `Status: SUCCESS` for
        //    "unwinding assertion loop 0" on a loop that exits within the bound).
        //    The FAILURE direction is untouched — an insufficient bound still
        //    fires via the violation flag in the main query.
        //
        // 2. `--no-assertion-reach-checks` — the user asked for the companion
        //    instrumentation not to be computed at all. Kani attaches a companion
        //    to every assert it codegens (user assertions AND the MIR `Assert`
        //    terminators for bounds / overflow / divide-by-zero, which is why
        //    `expected/reach/*/unreachable` pin UNREACHABLE for those classes
        //    with the checks ON); with them off, a check in dead code reports
        //    SUCCESS, which is what `expected/reach/turned-off` and
        //    `expected/assert-location/debug-assert` pin.
        //
        // SOUNDNESS, for both: the `ay_violation_*` obligation above is emitted
        // either way, so no check leaves the query. This suppresses an ANNOTATION
        // of an already-discharged check, never a check, and only non-FAILURE
        // checks are ever annotated. The V4 vacuity gate keeps the half that
        // matters — a proof discharged under contradictory assumptions is caught
        // by `probe_harness_reachable`, which probes the program constraints and
        // does not read these per-check flags. Under (2) the DEAD-CHECK half does
        // go (its trigger is "every non-cover check is UNREACHABLE"), so the
        // driver prints a note on stderr whenever the flag is passed — see
        // `call_single_file::kani_compiler_local_flags`. That is the user's
        // explicit trade, not a silent one.
        let suppress_reach_flag = !self.config.assertion_reach_checks || label == "unwind_assert";
        let reach_expr = match (&self.assumption_context, guard) {
            _ if suppress_reach_flag => None,
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
            // SIMD lane checks (statement/intrinsics/simd/ops.rs) are
            // assert-assume pairs whose assume half is added unconditionally, and
            // Kani emits them whatever `--no-overflow-checks` says. Under the
            // gated ArithmeticOverflow kind only the assert half would vanish,
            // silently pruning every overflowing lane: a false proof. Keep them
            // ungated; signed `MIN / -1` in simd_div/rem is UB.
            "overflow_check_simd_div_rem" => PropertyKind::UndefinedBehavior,
            "overflow_check_simd_arith" => PropertyKind::Other,
            l if l.starts_with("overflow_check_") => PropertyKind::ArithmeticOverflow,
            "null_pointer_check" | "raw_ptr_deref_null" => PropertyKind::NullPointer,
            "alignment_check" | "raw_ptr_deref_misaligned" | "pointer_bounds_check" => {
                PropertyKind::MemorySafety
            }
            "unsupported_foreign_function" => PropertyKind::UndefinedBehavior,
            "box_deref_validity" => PropertyKind::UndefinedBehavior,
            "simd_div_by_zero_check" | "unchecked_div_by_zero" => PropertyKind::UndefinedBehavior,
            // `unchecked_{add,sub,mul}` overflow (statement/arithmetic_checks.rs
            // `overflow_check`): UB of an unsafe intrinsic. Kani asserts it with an
            // ungated `codegen_assert` and refuses to compile without rustc
            // overflow checks, so `--no-overflow-checks` never removes it there.
            // The BMC check has no assume half: under the gated
            // `ArithmeticOverflow` kind the flag DROPPED the only check of this UB
            // (core's `ub_checks` are compiled false) and an overflowing harness
            // verified SUCCESSFUL. Ungated.
            "unchecked_add_overflow" | "unchecked_sub_overflow" | "unchecked_mul_overflow" => {
                PropertyKind::UndefinedBehavior
            }
            // Operator-level integer `Div`/`Rem` checks (statement/rvalue.rs):
            // the only checks on a lowered `unchecked_div`/`unchecked_rem`,
            // which is UB, never a panic, and unsatisfiable after a source `/`
            // or `%` (the MIR `Assert`'s edge condition holds). Kani's
            // `check_div_overflow` asserts both whatever `--no-overflow-checks`
            // says. Under the gated ArithmeticOverflow kind, a lowered
            // `unchecked_div(MIN, -1)` would lose its only check under that
            // flag: a false proof. Same shape as `overflow_check_simd_div_rem`.
            "binop_div_by_zero" | "binop_rem_by_zero" | "binop_div_overflow"
            | "binop_rem_overflow" => PropertyKind::UndefinedBehavior,
            "pointer_invalid" | "dead_object" => PropertyKind::MemorySafety,
            "use_after_free_check"
            | "double_free_check"
            | "dealloc_size_mismatch"
            | "dealloc_base_pointer_check" => PropertyKind::MemorySafety,
            // The MIR `Assert(Overflow(Shl|Shr))` and SIMD lane checks; both
            // record under `CheckGate::Always` (statement/arithmetic_checks.rs),
            // so this kind only names them.
            "shift_distance_check" | "shift_distance_check_negative" => {
                PropertyKind::ArithmeticOverflow
            }
            // `unchecked_shl`/`unchecked_shr` past the width (or by a negative
            // signed distance): UB of an unsafe intrinsic, which Kani asserts as
            // `arithmetic_overflow`, "attempt to shift by excessive shift
            // distance" (tests/ui/should-panic-attribute/unexpected-failures),
            // whatever `--no-overflow-checks` says. On the shared
            // `shift_distance_check` label under the gated kind the flag dropped
            // the only check of this UB: the check has no assume half, and core's
            // `ub_checks` are compiled false. Ungated.
            "unchecked_shift_distance_check" | "unchecked_shift_distance_check_negative" => {
                PropertyKind::UndefinedBehavior
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

    /// Publish the whole-trace assumption conjunction as the UNASSERTED flag
    /// `ay_assume_final` (defined `= final_context`, never asserted here).
    ///
    /// Since `kani::assume` joined the ordered assumption context (instead of
    /// being asserted globally), the program constraints alone no longer say
    /// whether the harness's assumptions can all hold — which is exactly the
    /// question the driver's vacuity probe (`probe_harness_reachable`) must
    /// answer to tell `[AY:VACUOUS:unsat-assumption]` from dead checks. The
    /// probe asserts this flag on top of the constraints; the main query and
    /// every per-check flag are untouched by an unasserted definition.
    pub(in crate::codegen_ay) fn emit_assume_final_flag(&mut self) {
        if let Some(ctx) = self.assumption_context.clone() {
            let pred = self.declare_var("ay_assume_final", bool_sort());
            self.assert(pred.eq(ctx));
        }
    }

    /// Finalize the harness counterexample query.
    ///
    /// Adds a single assertion `(or viol_0 ... viol_n)` so SAT corresponds to a reachable
    /// counterexample and UNSAT corresponds to a proof.
    ///
    /// Also upgrades the logic to ALL if datatypes were declared (since QF_AUFBV etc.
    /// don't support algebraic datatypes), or if a term uses floating point and
    /// the user named no logic.
    pub(in crate::codegen_ay) fn finalize_counterexample_query(&mut self) {
        // The vacuity probe needs the whole-trace assumption conjunction.
        self.emit_assume_final_flag();
        // Upgrade logic if datatypes are present (QF_AUFBV doesn't support datatypes)
        self.program.upgrade_logic_for_datatypes();
        // And if floating point is (QF_AUFBV has none), unless the user named
        // the logic (`--ay-logic`, #621). Every program assert is dual-written
        // to `bmc_vc`, so its terms are the program's.
        if !self.config.logic_override {
            let uses_floating_point =
                crate::codegen_ay::emitter::bmc_vc_uses_floating_point(&self.bmc_vc);
            crate::codegen_ay::emitter::upgrade_logic_for_floating_point(
                &mut self.program,
                uses_floating_point,
            );
        }

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

    /// Add get-value queries for kani::any_raw symbolic variables.
    pub(in crate::codegen_ay) fn add_get_value_for_kani_any(&mut self) {
        let queries = self.playback_model_queries();
        self.program.get_value(queries);
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
        self.record_cover_property_with_guard(condition, None, location, message)
    }

    /// Record a cover property together with the SITE GUARD it sits under.
    ///
    /// `guard` is the path condition at the `kani::cover!` statement, kept
    /// SEPARATE from the cover condition itself. The cover flag is still
    /// `assumption_context ∧ guard ∧ condition` — unchanged — but keeping the
    /// two apart lets this function also emit the reachability companion
    /// `ay_reach_cover_<n>` defined as `assumption_context ∧ guard`.
    ///
    /// # Why the companion exists (Kani parity)
    ///
    /// Kani distinguishes two ways a cover can fail to hold, and pins both:
    ///
    /// * **UNSATISFIABLE** — the cover STATEMENT is reachable, but the
    ///   condition is never true there.
    /// * **UNREACHABLE** — the cover statement itself sits on dead code, so the
    ///   condition was never even asked (`expected/cover/cover-unreachable`
    ///   pins `Status: UNREACHABLE` for `kani::cover!(x == 2)` under
    ///   `if x > 10 { if x < 5 { … } }`, and the tally
    ///   `** 1 of 3 cover properties satisfied (2 unreachable)`).
    ///
    /// A single flag conflates them: `guard ∧ condition` is unsat in both
    /// cases, so the driver had no way to tell them apart and reported every
    /// dead cover as UNSATISFIABLE. The companion answers exactly the missing
    /// question — "is the cover SITE reachable at all" — and the driver
    /// reclassifies to UNREACHABLE only when the solver proves it is not.
    ///
    /// Gated on `config.assertion_reach_checks` for the same reason the
    /// violation companion is (see `record_property_violation_with_guard`):
    /// Kani attaches the reachability companion to every assert it codegens,
    /// `kani::cover!` included, and `--no-assertion-reach-checks` removes them
    /// all — under that flag Kani reports a dead cover UNSATISFIABLE, which is
    /// this function's behaviour with the companion withheld.
    ///
    /// SOUNDNESS: the companion adds a definition, never removes an obligation,
    /// and the reclassification it enables moves between two NEGATIVE cover
    /// outcomes (neither counts toward "N of M cover properties satisfied", and
    /// `has_unsatisfiable_cover` treats them identically). No cover can become
    /// SATISFIED through this path, and no verification verdict can flip.
    pub(in crate::codegen_ay) fn record_cover_property_with_guard(
        &mut self,
        condition: Expr,
        guard: Option<Expr>,
        location: Option<SourceLocation>,
        message: Option<String>,
    ) -> u64 {
        // Kani assert-assume ordering: a cover after a failed assert (or after
        // an assume) is only satisfiable on paths consistent with the
        // assumption context recorded before it.
        let site_guard = match (&self.assumption_context, guard) {
            (None, None) => None,
            (Some(assum_ctx), None) => Some(assum_ctx.clone()),
            (None, Some(g)) => Some(g),
            (Some(assum_ctx), Some(g)) => Some(assum_ctx.clone().and(g)),
        };
        let condition = match &site_guard {
            Some(g) => g.clone().and(condition),
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

        // Reachability companion. A missing flag means "trivially reachable" to
        // the driver, so the trivial `true` guard is skipped, exactly as on the
        // violation path.
        let reach_name = match site_guard {
            _ if !self.config.assertion_reach_checks => None,
            None => None,
            Some(expr) => {
                let mut rname = String::with_capacity("ay_reach_cover_".len() + 20);
                rname.push_str("ay_reach_cover_");
                let _ = write!(&mut rname, "{cover_id}");
                // declare_var + assert dual-write to program and bmc_vc, so both
                // the legacy and emit_bmc payloads carry the flag definition.
                let rpred = self.declare_var(&rname, bool_sort());
                self.assert(rpred.eq(expr));
                Some(rname)
            }
        };

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
        if let Some(rname) = reach_name {
            metadata = metadata.with_reach_var(rname);
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

    /// Record, in the BMC lane, an encoding that can only ADD behaviours: a
    /// certified-fresh unconstrained value standing in for a program value, or
    /// a check forced to fail (fail-closed) for a construct that is not modelled.
    ///
    /// Such an encoding cannot produce a false proof, so it must not demote an
    /// UNSAT result; but a counterexample found under it may be an artifact of
    /// the freed value or of the forced failure, and must never be certified
    /// `Genuine`. The existing category with exactly that polarity is
    /// `chc_sound_havoc_drop`: a `SOUND_APPROXIMATION_CATEGORIES` member (a SAT
    /// result classifies `OverApproximation`) that the driver excludes from the
    /// sound-fallback proof qualifier (an UNSAT result stays a clean proof).
    ///
    /// Before this recorder the BMC lane counted nothing at these sites, so
    /// `classify_ctrex` saw zero taint and certified the counterexample
    /// `Genuine` — the first soundness-dual gate run (2026-09-11) measured
    /// three: `dual_77_dependent::dual_dependent`,
    /// `dual69_safe_twin::dual69_safe_twin_truncate` and
    /// `transmute_provenance_repro::provenance_roundtrip_CONTROL_failclosed`.
    ///
    /// Writes only the per-function map, never the crate atomic, so the CHC
    /// lane's snapshot deltas over `GLOBAL_COUNTERS.sound_havoc_drop` are not
    /// perturbed. Deliberately does NOT call `unsupported()`: its total gates
    /// iterator unrolling (`unsupported_construct_total`), and this record must
    /// change the certificate only, never the encoding.
    pub(in crate::codegen_ay) fn bmc_sound_havoc(&self, site: &'static str) {
        let fn_name = self.bmc_attribution_fn_name();
        tracing::debug!(site, fn_name, "bmc_sound_havoc recorded");
        crate::codegen_ay::chc::record_bmc_sound_havoc_for_fn(fn_name, 1);
    }

    /// Record, in the BMC lane, a checked pointer offset (`ptr::offset`, `add`,
    /// `sub`, the `Offset` model) or an `offset_from` whose allocation the
    /// encoder could not NAME, so Kani's same-allocation obligation
    /// (kani_core models.rs: object identity and both pointers inside it) was
    /// not emitted for that site.
    ///
    /// `offset_provenance_unresolved` is a DEMOTED category, the same one the
    /// CHC lane records when its `ptr_offset_alloc_bound_check` cannot resolve
    /// the base: a PROOF that leaned on the site is downgraded to FAILURE with
    /// `[AY:DEMOTION_REASONS:offset_provenance_unresolved=N]`, and a SAT result
    /// whose only demotion is this one is routed to OverApproximation, never
    /// Genuine (driver `classify_ctrex`). Before this recorder the BMC check
    /// abstained SILENTLY: `offset(s.as_ptr(), isize::MAX)` on a `&str`
    /// literal and `ptr.wrapping_add(10).offset_from(ptr)` on a stack `u128`
    /// both printed SUCCESSFUL (tests/expected/offset-bounds-check).
    ///
    /// Attributed to the root harness through mini-inlined frames, as
    /// `bmc_sound_havoc` is. Deliberately does NOT call `unsupported()`: its
    /// total gates iterator unrolling, and this record must change the
    /// certificate only.
    pub(in crate::codegen_ay) fn bmc_offset_provenance_unresolved(&self, site: &'static str) {
        let fn_name = self.bmc_attribution_fn_name();
        tracing::debug!(site, fn_name, "bmc_offset_provenance_unresolved recorded");
        crate::codegen_ay::chc::record_bmc_offset_provenance_unresolved_for_fn(fn_name, 1);
    }
}

#[cfg(test)]
mod tests;
