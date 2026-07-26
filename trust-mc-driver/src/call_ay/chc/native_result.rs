// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Result interpretation for native ay-chc portfolio solver.
//!
//! Extracted from `native.rs` to keep file sizes under 500 LOC.
//! Converts `VerifiedChcResult` (Safe/Unsafe/Unknown) into trust_mc's
//! `(VerificationStatus, FailedProperties, Vec<Property>, ProofCrosscheck)`.

use std::borrow::Cow;
use std::collections::HashSet;

use trust_mc_metadata::HarnessMetadata;

use crate::property_model::{CheckStatus, Property, PropertyId, RawSourceLocation};
use crate::session::KaniSession;
use crate::verification_result::{FailedProperties, ProofCrosscheck, VerificationStatus};

use super::smt_analysis::smt_has_recursive_unwind_assertion;
use super::verdict_policy::{ChcOutcomeKind, apply_recursion_unwind_verdict, classify_chc_outcome};
use super::{ChcSolverResult, TRIVIAL_SAFE_NO_ERROR_RULE_QUALIFIER};

macro_rules! solver_stdout {
    ($($arg:tt)*) => {{
        use std::io::Write;
        let stdout = std::io::stdout();
        let mut handle = stdout.lock();
        let _ = writeln!(handle, $($arg)*);
    }};
}

impl KaniSession {
    /// Interpret a trivially safe CHC system where no rule derives `error`.
    ///
    /// When the CHC system queries `error` but no rule can produce it, the
    /// system is trivially safe without invoking the solver. This avoids
    /// wasting solver budget on problems with many array-sorted variables
    /// where the encoding eliminated all assertion paths.
    pub(super) fn interpret_chc_trivial_safe(
        &self,
        smt_file: &std::path::Path,
        smt_content: &str,
        harness: &HarnessMetadata,
    ) -> anyhow::Result<ChcSolverResult> {
        let status = VerificationStatus::Success;
        let failed_props = FailedProperties::None;
        let proof_crosscheck = ProofCrosscheck::NotRun;

        let has_recursive_unwind = smt_has_recursive_unwind_assertion(smt_content);
        // BSEM-18: expand into per-property VERIFIED lines from the artifact
        // table when present; otherwise keep the single aggregate property.
        let mut properties = super::property_report::chc_success_properties(smt_file, harness)
            .unwrap_or_else(|| {
                vec![Property {
                    description: Cow::Borrowed(
                        "CHC verification: error unreachable — no error-producing rule (trivial)",
                    ),
                    property_id: PropertyId { fn_name: None, class: Cow::Borrowed("chc"), id: 0 },
                    source_location: RawSourceLocation {
                        column: None,
                        file: None,
                        function: None,
                        line: None,
                    },
                    status: CheckStatus::Success,
                    trace: None,
                }]
            });

        // Cover property checks (same as interpret_chc_safe).
        let cover_names = crate::smt_io::extract_cover_declarations_from_content(smt_content);
        if !cover_names.is_empty() {
            let vc_artifact_path = crate::ay_parse::vc_artifact_path_for_smt(smt_file);
            let location_map = crate::ay_parse::load_vc_artifact(&vc_artifact_path);
            let sat_results =
                self.check_cover_satisfiability_for_chc(smt_content, &cover_names, smt_file);
            let cover_properties = crate::ay_parse::build_cover_properties_from_sat_checks(
                &cover_names,
                &sat_results,
                location_map.as_ref(),
            );
            properties.extend(cover_properties);
        }

        let outcome = classify_chc_outcome(false, status, failed_props);
        let (status, failed_props, properties, _) = apply_recursion_unwind_verdict(
            has_recursive_unwind,
            outcome,
            status,
            failed_props,
            properties,
            Some(harness.pretty_name.as_str()),
        );

        solver_stdout!("[AY:PROOF] CHC verification: property proven (trivially safe)");

        Ok(ChcSolverResult {
            status,
            failed_properties: failed_props,
            properties,
            proof_crosscheck,
            proof_qualifiers: vec![TRIVIAL_SAFE_NO_ERROR_RULE_QUALIFIER.to_string()],
            proof_transcript_metadata: None,
            native_full_verification_verdict: None,
        })
    }

    /// Interpret a compiler-discharged CHC system that preserves an explicit
    /// false-bodied `error` obligation.
    pub(super) fn interpret_chc_false_error_safe(
        &self,
        smt_file: &std::path::Path,
        smt_content: &str,
        harness: &HarnessMetadata,
    ) -> anyhow::Result<ChcSolverResult> {
        let status = VerificationStatus::Success;
        let failed_props = FailedProperties::None;
        let proof_crosscheck = ProofCrosscheck::NotRun;

        let has_recursive_unwind = smt_has_recursive_unwind_assertion(smt_content);
        // BSEM-18: expand into per-property VERIFIED lines from the artifact
        // table when present; otherwise keep the single aggregate property.
        let mut properties = super::property_report::chc_success_properties(smt_file, harness)
            .unwrap_or_else(|| {
                vec![Property {
                    description: Cow::Borrowed(
                        "CHC verification: error unreachable - false error obligation",
                    ),
                    property_id: PropertyId { fn_name: None, class: Cow::Borrowed("chc"), id: 0 },
                    source_location: RawSourceLocation {
                        column: None,
                        file: None,
                        function: None,
                        line: None,
                    },
                    status: CheckStatus::Success,
                    trace: None,
                }]
            });

        let cover_names = crate::smt_io::extract_cover_declarations_from_content(smt_content);
        if !cover_names.is_empty() {
            let vc_artifact_path = crate::ay_parse::vc_artifact_path_for_smt(smt_file);
            let location_map = crate::ay_parse::load_vc_artifact(&vc_artifact_path);
            let sat_results =
                self.check_cover_satisfiability_for_chc(smt_content, &cover_names, smt_file);
            let cover_properties = crate::ay_parse::build_cover_properties_from_sat_checks(
                &cover_names,
                &sat_results,
                location_map.as_ref(),
            );
            properties.extend(cover_properties);
        }

        let outcome = classify_chc_outcome(false, status, failed_props);
        let (status, failed_props, properties, _) = apply_recursion_unwind_verdict(
            has_recursive_unwind,
            outcome,
            status,
            failed_props,
            properties,
            Some(harness.pretty_name.as_str()),
        );

        solver_stdout!("[AY:PROOF] CHC verification: property proven (false error obligation)");

        Ok(ChcSolverResult {
            status,
            failed_properties: failed_props,
            properties,
            proof_crosscheck,
            proof_qualifiers: Vec::new(),
            proof_transcript_metadata: None,
            native_full_verification_verdict: None,
        })
    }

    /// Interpret a `VerifiedChcResult::Safe` from the native ay-chc solver.
    ///
    /// Handles recursion unwind verdict adjustment and provenance marker output.
    /// Z3 BMC cross-checking has been removed (Phase 2 of Z3 elimination, #4223).
    pub(super) fn interpret_chc_safe(
        &self,
        verified_inv: ay::chc::VerifiedInvariant,
        smt_content: &str,
        smt_file: &std::path::Path,
        harness: &HarnessMetadata,
        _demoted_fallback_count: usize,
        proof_transcript_metadata: Option<serde_json::Value>,
        native_full_verification_verdict: Option<trust_mc_core::FullVerificationVerdict>,
    ) -> anyhow::Result<ChcSolverResult> {
        if self.args.common_args.verbose {
            let model = verified_inv.model();
            solver_stdout!("[AY-chc] AdaptivePortfolio proved SAFE");
            if !model.is_empty() {
                solver_stdout!("[AY-chc] Discovered {} invariant(s)", model.len());
            }
        }

        let status = VerificationStatus::Success;
        let failed_props = FailedProperties::None;
        let proof_crosscheck = ProofCrosscheck::NotRun;

        let has_recursive_unwind = smt_has_recursive_unwind_assertion(smt_content);
        let check_status = if status == VerificationStatus::Success {
            CheckStatus::Success
        } else {
            CheckStatus::Failure
        };
        // BSEM-18: expand into per-property VERIFIED lines from the artifact
        // table when present; otherwise keep the single aggregate property.
        let mut properties = super::property_report::chc_success_properties(smt_file, harness)
            .filter(|_| check_status == CheckStatus::Success)
            .unwrap_or_else(|| {
                vec![Property {
                    description: Cow::Borrowed("CHC verification: error unreachable (ay-chc)"),
                    property_id: PropertyId { fn_name: None, class: Cow::Borrowed("chc"), id: 0 },
                    source_location: RawSourceLocation {
                        column: None,
                        file: None,
                        function: None,
                        line: None,
                    },
                    status: check_status,
                    trace: None,
                }]
            });

        // Part of #1162: Secondary cover property checks for native CHC path.
        // When the main query proves safe, cover properties cannot be
        // determined from the CHC result. Run a secondary plain SMT query.
        if status == VerificationStatus::Success {
            let cover_names = crate::smt_io::extract_cover_declarations_from_content(smt_content);
            if !cover_names.is_empty() {
                let vc_artifact_path = crate::ay_parse::vc_artifact_path_for_smt(smt_file);
                let location_map = crate::ay_parse::load_vc_artifact(&vc_artifact_path);
                let sat_results =
                    self.check_cover_satisfiability_for_chc(smt_content, &cover_names, smt_file);
                if self.args.common_args.verbose {
                    solver_stdout!(
                        "[AY:COVER_CHC] {} cover properties checked via secondary SAT query (native)",
                        cover_names.len()
                    );
                }
                let cover_properties = crate::ay_parse::build_cover_properties_from_sat_checks(
                    &cover_names,
                    &sat_results,
                    location_map.as_ref(),
                );
                properties.extend(cover_properties);
            }
        }

        let outcome = classify_chc_outcome(false, status, failed_props);
        let (status, failed_props, properties, outcome) = apply_recursion_unwind_verdict(
            has_recursive_unwind,
            outcome,
            status,
            failed_props,
            properties,
            Some(harness.pretty_name.as_str()),
        );
        let proof_crosscheck =
            if has_recursive_unwind { ProofCrosscheck::NotRun } else { proof_crosscheck };

        match outcome {
            ChcOutcomeKind::Proof => {
                solver_stdout!("[AY:PROOF] CHC verification: property proven");
            }
            ChcOutcomeKind::Counterexample => {
                if has_recursive_unwind {
                    solver_stdout!("[AY:CTREX] CHC verification: recursion unwinding assertion");
                } else {
                    solver_stdout!("[AY:CTREX] CHC verification: counterexample reachable");
                }
            }
            ChcOutcomeKind::ConservativeUnknown | ChcOutcomeKind::SolverUnknown => {
                solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
            }
        }

        Ok(ChcSolverResult {
            status,
            failed_properties: failed_props,
            properties,
            proof_crosscheck,
            proof_qualifiers: Vec::new(),
            proof_transcript_metadata,
            native_full_verification_verdict,
        })
    }

    /// Interpret a `VerifiedChcResult::Unsafe` from the native ay-chc solver.
    ///
    /// Handles 0-step counterexample cross-check fallback and recursion unwind
    /// verdict adjustment.
    pub(super) fn interpret_chc_unsafe(
        &self,
        verified_cex: ay::chc::VerifiedCounterexample,
        problem: &ay::chc::ChcProblem,
        smt_file: &std::path::Path,
        smt_content: &str,
        harness: &HarnessMetadata,
        proof_transcript_metadata: Option<serde_json::Value>,
        native_full_verification_verdict: Option<trust_mc_core::FullVerificationVerdict>,
    ) -> anyhow::Result<ChcSolverResult> {
        let cex = verified_cex.counterexample();
        if self.args.common_args.verbose {
            solver_stdout!(
                "[AY-chc] AdaptivePortfolio found counterexample ({} steps)",
                cex.steps.len()
            );
        }
        // Part of #4182: 0-step counterexamples from ay-chc are suspicious.
        if cex.steps.is_empty() {
            solver_stdout!("[AY-chc] 0-step counterexample — returning UNKNOWN");
            anyhow::bail!("ay-chc 0-step counterexample — inconclusive");
        }
        // Provenance marker for scripts (Part of #1058)
        solver_stdout!(
            "[AY:CTREX] CHC verification: counterexample with {} steps",
            cex.steps.len()
        );
        // BSEM-18: identify which per-property `error_p{id}` relations the
        // counterexample violated so the report names the failing check(s).
        // The counterexample trace passes through the specific `error_p{id}`
        // before reaching the aggregate `error`, so resolving each step's
        // predicate name against the solved problem recovers the failing set.
        let mut failing_relations = HashSet::new();
        for step in &cex.steps {
            if let Some(pred) = problem.get_predicate(step.predicate) {
                if pred.name.starts_with("error_p") {
                    failing_relations.insert(pred.name.clone());
                }
            }
        }

        // When the counterexample names one or more per-property relations we
        // report those as FAILURE and the rest as UNDETERMINED (sound — an
        // UNSAFE run does not prove the untriggered checks safe). Otherwise we
        // keep the single aggregate failure property.
        let per_property =
            super::property_report::chc_failure_properties(smt_file, harness, &failing_relations);

        // Derive `failed_properties` from the ACTUAL failing property class,
        // not a hard-coded `PanicsOnly`. A memory_safety / pointer_dereference /
        // UB counterexample must be `Other` (→ FAILED under #[should_panic]);
        // only genuine assertion/panic failures are `PanicsOnly`. When the
        // counterexample names no per-property relation (direct `error` head,
        // e.g. a panic call), treat it as a panic — matching the prior default.
        let failed_class = match &per_property {
            Some(props) => crate::ay_parse::determine_failed_from_properties(props),
            None => FailedProperties::PanicsOnly,
        };

        let properties = per_property.unwrap_or_else(|| {
            vec![Property {
                description: Cow::Borrowed("CHC verification: error reachable (ay-chc)"),
                property_id: PropertyId { fn_name: None, class: Cow::Borrowed("chc"), id: 0 },
                source_location: RawSourceLocation {
                    column: None,
                    file: None,
                    function: None,
                    line: None,
                },
                status: CheckStatus::Failure,
                trace: None,
            }]
        });
        // Part of #4058: the compiler-emitted recursive unwind marker
        // is authoritative.
        let has_recursive_unwind = smt_has_recursive_unwind_assertion(smt_content);
        let (status, failed_props, properties, _) = apply_recursion_unwind_verdict(
            has_recursive_unwind,
            ChcOutcomeKind::Counterexample,
            VerificationStatus::Failure,
            failed_class,
            properties,
            Some(harness.pretty_name.as_str()),
        );
        Ok(ChcSolverResult {
            status,
            failed_properties: failed_props,
            properties,
            proof_crosscheck: ProofCrosscheck::NotRun,
            proof_qualifiers: Vec::new(),
            proof_transcript_metadata,
            native_full_verification_verdict,
        })
    }
}
