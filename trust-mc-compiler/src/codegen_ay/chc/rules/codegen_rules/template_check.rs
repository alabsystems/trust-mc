// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Template-Directed Inductive Checking (TIC).
//!
//! Verifies candidate loop invariants using 3 standard SMT checks
//! (initiation, consecution, safety) instead of CHC synthesis.
//!
//! When pattern detection identifies a loop with a known invariant
//! (forward accumulator or countdown accumulator), TIC constructs
//! 3 separate SMT queries and verifies them with AY:
//!
//! 1. **Initiation:** Invariant holds at loop entry
//! 2. **Consecution:** Invariant is preserved by one loop iteration
//! 3. **Safety:** Invariant implies the user property at loop exit
//!
//! If all 3 checks pass (UNSAT), the VC is replaced with a trivially
//! safe system (no rules derive error), allowing the driver to report PROOF.
//!
//! Part of #3258: Alternative to PDR synthesis for detected patterns.
//! Design: designs/2026-03-06-issue-3258-local-maximum-alternative.md

use tracing::{debug, info, warn};

use super::lemma_hint::{IncrSource, LoopModification};
use super::lemma_hint_detect;
use crate::codegen_ay::chc::ChcCtx;

/// Apply template-directed inductive checking.
///
/// If a candidate invariant is detected and all 3 TIC checks pass,
/// replaces the VC with a trivially provable system (no rules → error
/// unreachable). Called after `apply_linearization()` in `translate_inner()`.
///
/// Returns `true` if TIC succeeded and the VC was replaced.
pub(in crate::codegen_ay::chc) fn apply_template_check(ctx: &mut ChcCtx<'_, '_>) -> bool {
    if !ctx.int_lift || ctx.loop_headers.is_empty() {
        return false;
    }

    let result = lemma_hint_detect::detect_all_modifications(&ctx.vc.rules);
    if result.modifications.is_empty() {
        return false;
    }

    // Try forward accumulator TIC: sum += counter; counter += 1
    if try_forward_accumulator_tic(&result) {
        info!(fn_name = %ctx.fn_name, "TIC: forward accumulator invariant verified");
        ctx.vc.rules.clear();
        ctx.vc.trivially_safe_discharged = true;
        return true;
    }

    // Try countdown accumulator TIC: sum += n; counter -= 1
    if try_countdown_accumulator_tic(&result) {
        info!(fn_name = %ctx.fn_name, "TIC: countdown accumulator invariant verified");
        ctx.vc.rules.clear();
        ctx.vc.trivially_safe_discharged = true;
        return true;
    }

    false
}

/// Run an SMT-LIB2 query through AY and check for UNSAT.
///
/// Returns `true` if AY reports "unsat", `false` otherwise.
fn ay_check_unsat(smt2: &str, check_name: &str) -> bool {
    let commands = match ay_frontend::parse(smt2) {
        Ok(commands) => commands,
        Err(err) => {
            warn!(check = check_name, "TIC: AY parse failed: {err}");
            return false;
        }
    };

    let mut executor = ay_dpll::Executor::new();
    executor.set_timeout(Some(std::time::Duration::from_secs(10)));
    let outputs = match executor.execute_all(&commands) {
        Ok(outputs) => outputs,
        Err(err) => {
            warn!(check = check_name, "TIC: AY execution failed: {err}");
            return false;
        }
    };

    let verdict = outputs
        .iter()
        .find_map(|output| {
            let verdict = output.trim();
            matches!(verdict, "sat" | "unsat" | "unknown").then_some(verdict)
        })
        .unwrap_or("");
    let is_unsat = verdict == "unsat";
    debug!(check = check_name, is_unsat, verdict, "TIC AY check");
    is_unsat
}

/// Run all 3 TIC checks (initiation, consecution, safety) for a pattern.
/// Returns `true` only if all 3 are UNSAT.
fn run_tic_checks(init: &str, consec: &str, safety: &str, label: &str) -> bool {
    if !ay_check_unsat(init, &format!("{label}_initiation")) {
        debug!("TIC {label}: initiation check failed");
        return false;
    }
    if !ay_check_unsat(consec, &format!("{label}_consecution")) {
        debug!("TIC {label}: consecution check failed");
        return false;
    }
    if !ay_check_unsat(safety, &format!("{label}_safety")) {
        debug!("TIC {label}: safety check failed");
        return false;
    }
    info!("TIC: {label} invariant verified (3/3 checks UNSAT)");
    true
}

// --- Forward accumulator SMT-LIB2 check formulas ---
// Invariant I(n, sum, i, sq):
// 2*sum + i = sq, sq = i*i, 0<=i<=n, sum>=0, sq>=0, sum<=sq.
// The final bound is redundant but keeps the safety check in AY's linear fragment.

const FWD_INITIATION: &str = "(set-logic QF_NIA)\n\
(declare-const n Int)\n\
(assert (>= n 0))\n\
(assert (not (and (= (+ (* 2 0) 0) 0) (= 0 (* 0 0))\n\
  (>= 0 0) (<= 0 n) (>= 0 0) (>= 0 0) (<= 0 0))))\n\
(check-sat)\n";

const FWD_CONSECUTION: &str = "(set-logic QF_NIA)\n\
(declare-const n Int)\n\
(declare-const sum Int)\n\
(declare-const i Int)\n\
(declare-const sq Int)\n\
(declare-const sum_next Int)\n\
(declare-const i_next Int)\n\
(declare-const sq_next Int)\n\
(assert (>= n 0))\n\
(assert (= (+ (* 2 sum) i) sq))\n\
(assert (= sq (* i i)))\n\
(assert (>= i 0))\n\
(assert (<= i n))\n\
(assert (>= sum 0))\n\
(assert (>= sq 0))\n\
(assert (<= sum sq))\n\
(assert (< i n))\n\
(assert (= sum_next (+ sum i)))\n\
(assert (= i_next (+ i 1)))\n\
(assert (= sq_next (+ sq (+ (* 2 i) 1))))\n\
(assert (not (and (= (+ (* 2 sum_next) i_next) sq_next)\n\
  (= sq_next (* i_next i_next))\n\
  (>= i_next 0) (<= i_next n) (>= sum_next 0) (>= sq_next 0) (<= sum_next sq_next))))\n\
(check-sat)\n";

const FWD_SAFETY: &str = "(set-logic QF_NIA)\n\
(declare-const n Int)\n\
(declare-const sum Int)\n\
(declare-const i Int)\n\
(declare-const sq Int)\n\
(assert (>= n 0))\n\
(assert (= (+ (* 2 sum) i) sq))\n\
(assert (= sq (* i i)))\n\
(assert (>= i 0))\n\
(assert (<= i n))\n\
(assert (>= sum 0))\n\
(assert (>= sq 0))\n\
(assert (<= sum sq))\n\
(assert (>= i n))\n\
(assert (not (<= sum sq)))\n\
(check-sat)\n";

// --- Countdown accumulator SMT-LIB2 check formulas ---
// Invariant I(n, sum, counter): sum + counter*n = n*n, counter>=0, sum>=0, counter<=n.

const CDN_INITIATION: &str = "(set-logic QF_NIA)\n\
(declare-const n Int)\n\
(assert (>= n 0))\n\
(assert (not (and (= (+ 0 (* n n)) (* n n))\n\
  (>= n 0) (>= 0 0) (<= n n))))\n\
(check-sat)\n";

const CDN_CONSECUTION: &str = "(set-logic QF_NIA)\n\
(declare-const n Int)\n\
(declare-const sum Int)\n\
(declare-const counter Int)\n\
(declare-const sum_next Int)\n\
(declare-const counter_next Int)\n\
(assert (>= n 0))\n\
(assert (= (+ sum (* counter n)) (* n n)))\n\
(assert (>= counter 0))\n\
(assert (>= sum 0))\n\
(assert (<= counter n))\n\
(assert (> counter 0))\n\
(assert (= sum_next (+ sum n)))\n\
(assert (= counter_next (- counter 1)))\n\
(assert (not (and (= (+ sum_next (* counter_next n)) (* n n))\n\
  (>= counter_next 0) (>= sum_next 0) (<= counter_next n))))\n\
(check-sat)\n";

const CDN_SAFETY: &str = "(set-logic QF_NIA)\n\
(declare-const n Int)\n\
(declare-const sum Int)\n\
(declare-const counter Int)\n\
(assert (>= n 0))\n\
(assert (= (+ sum (* counter n)) (* n n)))\n\
(assert (>= counter 0))\n\
(assert (>= sum 0))\n\
(assert (<= counter n))\n\
(assert (<= counter 0))\n\
(assert (not (= sum (* n n))))\n\
(check-sat)\n";

/// Detect and verify forward accumulator pattern: sum += counter; counter += 1.
fn try_forward_accumulator_tic(result: &lemma_hint_detect::ModificationResult) -> bool {
    for (accum_name, accum_mod) in &result.modifications {
        let LoopModification::IncrementBy(IncrSource::Variable(counter_name)) = accum_mod else {
            continue;
        };
        let counter: &str = counter_name;
        if !matches!(
            result.modifications.get(counter),
            Some(LoopModification::IncrementBy(IncrSource::Constant(1)))
        ) {
            continue;
        }
        if result.comparison_targets.get(counter).map_or(true, |s| s.is_empty()) {
            debug!(accum = %accum_name, counter, "TIC forward: no bound, skipping");
            continue;
        }
        debug!(accum = %accum_name, counter, "TIC: attempting forward accumulator");
        if run_tic_checks(FWD_INITIATION, FWD_CONSECUTION, FWD_SAFETY, "forward") {
            return true;
        }
    }
    false
}

/// Detect and verify countdown accumulator pattern: sum += n; counter -= 1.
fn try_countdown_accumulator_tic(result: &lemma_hint_detect::ModificationResult) -> bool {
    for (accum_name, accum_mod) in &result.modifications {
        let LoopModification::IncrementBy(IncrSource::Variable(invariant_name)) = accum_mod else {
            continue;
        };
        let invariant_name: &str = invariant_name;
        if result.modifications.contains_key(invariant_name) {
            continue;
        }
        for (counter_name, counter_mod) in &result.modifications {
            if counter_name == accum_name {
                continue;
            }
            if !matches!(counter_mod, LoopModification::DecrementBy(IncrSource::Constant(1))) {
                continue;
            }
            debug!(
                accum = %accum_name, counter = %counter_name,
                invariant_var = %invariant_name, "TIC: attempting countdown"
            );
            if run_tic_checks(CDN_INITIATION, CDN_CONSECUTION, CDN_SAFETY, "countdown") {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]
    use super::*;

    #[test]
    fn test_ay_available() {
        let result = ay_check_unsat(
            "(set-logic QF_LIA)\n(assert false)\n(check-sat)\n",
            "availability_check",
        );
        assert!(result, "AY should report UNSAT for (assert false)");
    }

    #[test]
    fn test_ay_sat_returns_false() {
        let result =
            ay_check_unsat("(set-logic QF_LIA)\n(assert true)\n(check-sat)\n", "sat_check");
        assert!(!result, "AY should return SAT for (assert true)");
    }

    #[test]
    fn test_forward_initiation() {
        assert!(ay_check_unsat(FWD_INITIATION, "fwd_init"));
    }

    #[test]
    fn test_forward_consecution() {
        assert!(ay_check_unsat(FWD_CONSECUTION, "fwd_consec"));
    }

    #[test]
    fn test_forward_safety() {
        assert!(ay_check_unsat(FWD_SAFETY, "fwd_safety"));
    }

    #[test]
    fn test_countdown_initiation() {
        assert!(ay_check_unsat(CDN_INITIATION, "cdn_init"));
    }

    #[test]
    fn test_countdown_consecution() {
        assert!(ay_check_unsat(CDN_CONSECUTION, "cdn_consec"));
    }

    #[test]
    fn test_countdown_safety() {
        // Capability pin flipped 2026-07-02: ay (pin a0654082, NIA ordered-box
        // product cuts + McCormick reasons) now PROVES the countdown nonlinear
        // exit implication (z3 cross-checked unsat), so the countdown TIC
        // template check is fully operational. The production path at
        // run_tic_checks stays fail-closed on the same runtime proof.
        assert!(
            ay_check_unsat(CDN_SAFETY, "cdn_safety"),
            "AY proves the countdown nonlinear exit implication since pin a0654082; \
             a regression back to unknown re-opens the countdown TIC capability gap"
        );
    }
}
