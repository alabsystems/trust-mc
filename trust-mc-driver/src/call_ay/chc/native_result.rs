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
use crate::verification_provenance::SolverUnknownReason;
use crate::verification_result::{FailedProperties, ProofCrosscheck, VerificationStatus};

use super::smt_analysis::smt_has_recursive_unwind_assertion;
use super::smt_analysis::smt_has_vacuous_checks_marker;
use super::verdict_policy::{ChcOutcomeKind, apply_recursion_unwind_verdict, classify_chc_outcome};
use super::{ChcSolverResult, TRIVIAL_SAFE_NO_ERROR_RULE_QUALIFIER};

macro_rules! solver_stdout {
    ($($arg:tt)*) => {{
        // Honor `--quiet` ("no output, just an exit code and requested
        // artifacts"): this macro used to write straight to stdout, so a quiet
        // run still printed `[AY:PROOF] CHC verification: ...` and the other
        // solver markers. The gate lives in the macro rather than at the ~70
        // call sites because several of them are free functions with no
        // `&KaniSession` in reach. Only the WRITE is skipped — the verdict and
        // the exit code are untouched — and with `--quiet` absent the bytes
        // are identical to before, which is what `scripts/ay-compiletest.sh`
        // parses.
        if !crate::args::common::quiet_output() {
            use std::io::Write;
            let stdout = std::io::stdout();
            let mut handle = stdout.lock();
            let _ = writeln!(handle, $($arg)*);
        }
    }};
}

impl KaniSession {
    /// Interpret a CHC system that queries `error` while no rule derives it,
    /// or whose every per-property query AY pruned away.
    ///
    /// No solver answers here. If the harness registered any checked
    /// obligation, the error rules were LOST from the encoding, not
    /// discharged, and the result fails closed as INCONCLUSIVE with
    /// `[AY:UNKNOWN_REASON:LostErrorRules]` ([`lost_error_rules_result`]).
    /// A discharge the compiler proved keeps an explicit `(=> false error)`
    /// obligation and is interpreted by `interpret_chc_false_error_safe`, not
    /// here. Only a harness that registered no checked obligation keeps the
    /// old interpretation: an empty report the no-checks gate settles, or
    /// covers adjudicated by their own SAT checks.
    pub(super) fn interpret_chc_trivial_safe(
        &self,
        smt_file: &std::path::Path,
        smt_content: &str,
        harness: &HarnessMetadata,
        deadline: crate::deadline::Deadline,
    ) -> anyhow::Result<ChcSolverResult> {
        // SOUNDNESS: registered checks with no error derivation are lost
        // checks. This path used to print `[AY:PROOF]` and list every
        // registered check SUCCESS without a solver, which the compiler's
        // straight-line discharge refuses for exactly this shape (#67).
        if crate::ay_parse::vc_artifact::artifact_may_register_checked_obligations(
            &crate::ay_parse::vc_artifact_path_for_smt(smt_file),
        ) {
            return Ok(lost_error_rules_result(smt_file, smt_content, harness));
        }
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
            let sat_results = self.check_cover_satisfiability_for_chc(
                smt_content,
                &cover_names,
                smt_file,
                deadline,
            );
            let cover_properties = crate::ay_parse::build_cover_properties_from_sat_checks(
                &cover_names,
                &sat_results,
                location_map.as_ref(),
            );
            properties.extend(cover_properties);
        }

        Self::apply_vacuous_checks_marker(smt_content, &mut properties);
        self.apply_chc_vacuity_probe(smt_content, smt_file, &mut properties, deadline);
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
            solver_unknown_reason: None,
            status,
            failed_properties: failed_props,
            properties,
            proof_crosscheck,
            proof_qualifiers: vec![TRIVIAL_SAFE_NO_ERROR_RULE_QUALIFIER.to_string()],
            proof_transcript_metadata: None,
            native_full_verification_verdict: None,
            exact_counterexample: false,
        })
    }

    /// Re-status a would-be CHC proof whose obligations the compiler proved
    /// UNREACHABLE rather than SAFE.
    ///
    /// Marking the checks `Unreachable` hands the run to the SAME V4 vacuity
    /// gate the BMC lane uses (`is_unsat_assumption_vacuous` in
    /// `harness_runner`), so both modes print one verdict, honour
    /// `--allow-vacuous` identically, and cannot drift apart. Without this the
    /// CHC lane reported `SUCCESSFUL` with `PROOF_QUALIFIERS:clean` for
    /// `assume(x > 10); assume(x < 5)`.
    fn apply_vacuous_checks_marker(smt_content: &str, properties: &mut [Property]) {
        if !smt_has_vacuous_checks_marker(smt_content) {
            return;
        }
        for property in properties.iter_mut() {
            // Covers carry their own vocabulary (Satisfied / Unsatisfiable /
            // Undetermined) and V4 skips them; re-statusing one here would
            // mislabel a cover without changing the verdict.
            if !property.is_cover_property() && property.status == CheckStatus::Success {
                property.status = CheckStatus::Unreachable;
            }
        }
    }

    /// CHC-side V4 vacuity: re-status a would-be proof whose every check SITE
    /// the solver proves unreachable.
    ///
    /// `apply_vacuous_checks_marker` above covers only what the COMPILER can
    /// decide structurally (`straightline_proof`'s exit-block walk). A
    /// SEMANTIC contradiction — `assume(x.is_nan() && x > 0.0)` — leaves the
    /// block graph intact, so that marker never fires and every check came back
    /// `SUCCESS` with `[AY:PROOF_QUALIFIERS:clean]` while the BMC lane, which
    /// probes (`call_ay::probe_harness_reachable`), reported `VACUOUS`. Two
    /// lanes, one source program, opposite verdicts, and the CHC one fail-OPEN
    /// on the project's own `--allow-vacuous` default.
    ///
    /// This runs the same question through the CHC encoding — see
    /// `vacuity_probe` for why a decided `unsat` there cannot be a false
    /// vacuity report — and produces the ONE shape the V4 gate in
    /// `harness_runner` keys on: every non-cover check `Unreachable`.
    ///
    /// Only a would-be CLEAN proof is probed (every non-cover check `Success`),
    /// and only a decided "no check site reachable" changes anything.
    pub(super) fn apply_chc_vacuity_probe(
        &self,
        smt_content: &str,
        smt_file: &std::path::Path,
        properties: &mut [Property],
        deadline: crate::deadline::Deadline,
    ) {
        let mut probeable = false;
        for property in properties.iter() {
            if property.is_cover_property() {
                continue;
            }
            if property.status != CheckStatus::Success {
                // A check the solver already decided FAILED, or one the marker
                // above already re-statused UNREACHABLE: not the clean-proof
                // shape this probe is for.
                return;
            }
            probeable = true;
        }
        if !probeable {
            return;
        }
        // Budgeted against what is left of the per-harness deadline, like
        // every other post-solve probe: below the useful floor it is skipped
        // with the typed `[AY:STAGE_SKIPPED:chc-vacuity-probe:…]` marker, and
        // a skipped probe answers exactly what an undecided one does (it
        // changes nothing).
        let Some(budget) = self.probe_stage_budget("chc-vacuity-probe", deadline) else {
            return;
        };
        let probe_started = std::time::Instant::now();
        let Some(probe) = super::vacuity_probe::build_chc_reachability_probe(smt_content) else {
            let outcome = super::vacuity_probe::ProbeOutcome::Undetermined;
            crate::stage_timing::record("chc-vacuity-probe", probe_started, outcome.label());
            return;
        };
        // The common answer — a check site IS reachable — changes nothing, yet
        // cost the external `ay` up to its whole budget (13.3 s of 15 s,
        // undecided, on `history/simple_pass` at ay 6818b5d06). A checked
        // in-process derivation (`vacuity_witness`) settles it first, within a
        // bounded slice. It can only ever answer "reachable", never
        // "unreachable", so it cannot mint or hide a vacuity report.
        let witness_slice = std::cmp::min(budget / 5, super::vacuity_probe::WITNESS_SLICE_CAP);
        if let Some(outcome) = super::vacuity_probe::certified_probe_witness(
            &probe,
            witness_slice,
            self.args.common_args.verbose,
        ) {
            crate::stage_timing::record("chc-vacuity-probe", probe_started, outcome.label());
            return;
        }
        // No certificate: the external probe runs with the budget it has always
        // had, re-clamped to what the witness left of the harness deadline, so
        // an unsuccessful search never shortens the probe below one per-call
        // timeout while the deadline has room.
        let Some(budget) = self.probe_stage_budget("chc-vacuity-probe", deadline) else {
            let outcome = super::vacuity_probe::ProbeOutcome::Undetermined;
            crate::stage_timing::record("chc-vacuity-probe", probe_started, outcome.label());
            return;
        };
        let outcome = self.probe_chc_check_sites_reachable(&probe, smt_file, budget);
        crate::stage_timing::record("chc-vacuity-probe", probe_started, outcome.label());
        if outcome != super::vacuity_probe::ProbeOutcome::NoCheckSiteReachable {
            return;
        }
        for property in properties.iter_mut() {
            if !property.is_cover_property() && property.status == CheckStatus::Success {
                property.status = CheckStatus::Unreachable;
            }
        }
        solver_stdout!(
            "[AY:CHC-VACUITY-PROBE:no-reachable-check-site] every check site is provably \
             unreachable — the proof is vacuous"
        );
    }

    /// Interpret a compiler-discharged CHC system that preserves an explicit
    /// false-bodied `error` obligation.
    pub(super) fn interpret_chc_false_error_safe(
        &self,
        smt_file: &std::path::Path,
        smt_content: &str,
        harness: &HarnessMetadata,
        deadline: crate::deadline::Deadline,
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
            let sat_results = self.check_cover_satisfiability_for_chc(
                smt_content,
                &cover_names,
                smt_file,
                deadline,
            );
            let cover_properties = crate::ay_parse::build_cover_properties_from_sat_checks(
                &cover_names,
                &sat_results,
                location_map.as_ref(),
            );
            properties.extend(cover_properties);
        }

        Self::apply_vacuous_checks_marker(smt_content, &mut properties);
        self.apply_chc_vacuity_probe(smt_content, smt_file, &mut properties, deadline);
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
            solver_unknown_reason: None,
            status,
            failed_properties: failed_props,
            properties,
            proof_crosscheck,
            proof_qualifiers: Vec::new(),
            proof_transcript_metadata: None,
            native_full_verification_verdict: None,
            exact_counterexample: false,
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
        deadline: crate::deadline::Deadline,
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
                let sat_results = self.check_cover_satisfiability_for_chc(
                    smt_content,
                    &cover_names,
                    smt_file,
                    deadline,
                );
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

        Self::apply_vacuous_checks_marker(smt_content, &mut properties);
        self.apply_chc_vacuity_probe(smt_content, smt_file, &mut properties, deadline);
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
            solver_unknown_reason: None,
            status,
            failed_properties: failed_props,
            properties,
            proof_crosscheck,
            proof_qualifiers: Vec::new(),
            proof_transcript_metadata,
            native_full_verification_verdict,
            exact_counterexample: false,
        })
    }

    /// Interpret a `VerifiedChcResult::Unsafe` from the native ay-chc solver.
    ///
    /// Handles 0-step counterexample cross-check fallback and recursion unwind
    /// verdict adjustment.
    ///
    /// `correlated_relations` carries per-property `error_p{id}` relations the
    /// SOLVE SEAM identified independently of the counterexample trace. The
    /// per-property lane needs it: its sliced obligation problem no longer
    /// routes the trace through `error_p{id}` (that clause is outside the
    /// query's cone of influence once the query has been unfolded), so the
    /// trace-walk below finds nothing and the report would fall back to a
    /// single unattributed failure. AY's stable obligation label is the
    /// authority there. Additive only — a relation named by the trace is still
    /// reported, and an empty set reproduces the previous behaviour exactly.
    pub(super) fn interpret_chc_unsafe(
        &self,
        verified_cex: ay::chc::VerifiedCounterexample,
        problem: &ay::chc::ChcProblem,
        smt_file: &std::path::Path,
        smt_content: &str,
        harness: &HarnessMetadata,
        proof_transcript_metadata: Option<serde_json::Value>,
        native_full_verification_verdict: Option<trust_mc_core::FullVerificationVerdict>,
        correlated_relations: &HashSet<String>,
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
        // Union in the seam-correlated relations (see the doc comment): the
        // per-property lane knows WHICH obligation was refuted even when the
        // sliced trace cannot say so.
        failing_relations.extend(correlated_relations.iter().cloned());

        // When the counterexample names one or more per-property relations we
        // report those as FAILURE and the rest as UNDETERMINED (sound — an
        // UNSAFE run does not prove the untriggered checks safe). Otherwise we
        // keep the single aggregate failure property.
        let per_property =
            super::property_report::chc_failure_properties(smt_file, harness, &failing_relations);

        // Derive `failed_properties` from the ACTUAL failing property class,
        // not a hard-coded `PanicsOnly`. A memory_safety / pointer_dereference /
        // UB counterexample must be `Other` (→ FAILED under #[should_panic]);
        // only genuine assertion/panic failures are `PanicsOnly`.
        //
        // A counterexample that names no per-property relation reached a bare
        // `error` head and is reported as the anonymous `chc.0` check. It keeps the
        // prior `PanicsOnly` class so an ordinary harness's genuine counterexample
        // stays certified; what it can NEVER do is stand as the expected panic of a
        // `should_panic` harness, because nothing identifies it as a panic rather than
        // an unreachable terminator, an undefined foreign call or an unsupported
        // construct. `harness_runner`'s V7 gate enforces that for every lane.
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
            solver_unknown_reason: None,
            status,
            failed_properties: failed_props,
            properties,
            proof_crosscheck: ProofCrosscheck::NotRun,
            proof_qualifiers: Vec::new(),
            proof_transcript_metadata,
            native_full_verification_verdict,
            // DELIBERATELY false on AY's own `Unsafe`. The counterexample here
            // is a solver model, and the driver has a separate lane that
            // adjudicates it (strict certification / checked replay); the flag
            // means "the DRIVER derived the error itself", which is true only
            // of `interpret_chc_trivial_unsafe`. Leaving it false keeps this
            // path byte-identical to its pre-flag behaviour.
            exact_counterexample: false,
        })
    }
}

impl KaniSession {
    /// V5-CHC (mandatory witness, fail-CLOSED): decide what an UNDECIDED
    /// `cover(...)` means for a `--ay-chc` run.
    ///
    /// # Why this lane cannot decide covers
    ///
    /// A cover asks a REACHABILITY question — "is there a feasible run that
    /// reaches this point with this condition true". The BMC lane answers it
    /// exactly: its query already carries every assumption as a top-level
    /// assertion, so `cover_cond ∧ program_constraints` is decidable. The Horn
    /// encoding cannot: the compiler records a cover as a bare
    /// `(assert (= ay_cover_N <cond>))` emitted AFTER `(query error)`, with no
    /// relation application naming the block it sits in and no copy of the path
    /// constraints that reach it (`hook_cover` in the compiler has both
    /// `from_app` and `stmt_constraints` in hand and attaches neither). The
    /// assumptions that bound the cover live inside `(rule ...)` bodies keyed to
    /// a program point this file does not record, and the entry relation is
    /// total — `(rule (=> true (bb0 …)))` — so even "reachable in SOME block"
    /// is satisfied by every satisfiable condition. There is no sound way, from
    /// the CHC artifact alone, to turn a `sat` into a witness.
    ///
    /// `check_cover_satisfiability_for_chc` therefore reports UNDETERMINED for
    /// anything it cannot prove unsatisfiable. That is honest, but on its own it
    /// is fail-OPEN for `--strict-vacuity`: V5 in `harness_runner` only fires on
    /// a cover PROVED `Unsatisfiable`/`Unreachable`, so a harness whose witness
    /// obligation was never adjudicated would exit 0 and be counted verified —
    /// the gate asked for could never fire.
    ///
    /// # What this does
    ///
    /// Under `--strict-vacuity` an unadjudicated cover is a hard failure: the
    /// flag's contract is "a declared cover must be shown to hold", and "we did
    /// not check" is not "it holds". Mirrors V5's shape — `failed_properties` is
    /// only overwritten when it is `None`, so a `should_panic` harness that
    /// panicked as expected keeps `PanicsOnly` and stays an effective manual
    /// success, exactly as it does under `harness_runner`'s V5.
    ///
    /// Without `--strict-vacuity` the verdict is untouched (V5 is warning-only
    /// by default and covers are optional for plain harnesses); a conformance
    /// harness is already hard-failed by `harness_runner`, so all this adds
    /// there is the explanation of WHY no cover could be satisfied.
    ///
    /// ENSURES: never relaxes a verdict — status only moves to `Failure`
    /// ENSURES: a run with no cover, or with every cover adjudicated, is untouched
    pub(in crate::call_ay) fn apply_chc_cover_witness_fail_close(
        &self,
        harness: &HarnessMetadata,
        result: &mut ChcSolverResult,
    ) {
        let undetermined = result
            .properties
            .iter()
            .filter(|p| p.is_cover_property() && p.status == CheckStatus::Undetermined)
            .count();
        if undetermined == 0 {
            return;
        }

        let is_conformance =
            self.args.conformance_harnesses.iter().any(|h| h == &harness.pretty_name);
        if !self.args.strict_vacuity && !is_conformance {
            return;
        }

        if self.args.strict_vacuity {
            solver_stdout!(
                "[AY:VACUOUS:cover-undetermined] {}: {undetermined} declared cover(...) \
                 could not be adjudicated in the unbounded (--ay-chc) lane — the Horn \
                 encoding records a cover's condition without the program point that \
                 guards it, so neither SATISFIED nor UNSATISFIABLE can be established \
                 soundly. --strict-vacuity treats an unchecked witness as a failure. \
                 Run the harness in the default (bounded) lane to adjudicate its covers.",
                harness.pretty_name
            );
            result.status = VerificationStatus::Failure;
            if matches!(result.failed_properties, FailedProperties::None) {
                result.failed_properties = FailedProperties::Other;
            }
        } else {
            solver_stdout!(
                "[AY:VACUOUS:cover-undetermined] {}: {undetermined} declared cover(...) \
                 could not be adjudicated in the unbounded (--ay-chc) lane, so this \
                 conformance harness cannot produce the SATISFIED cover it must \
                 demonstrate. Run it in the default (bounded) lane.",
                harness.pretty_name
            );
        }
    }
}

/// The fail-closed result for registered checks that reach no `error`
/// derivation: INCONCLUSIVE, every registered check `UNDETERMINED`, no proof
/// qualifier, reason [`SolverUnknownReason::LostErrorRules`].
///
/// Covers are listed `UNDETERMINED` too: they are not SAT-checked here, because
/// an encoding that lost its error rules may have lost the transitions a cover
/// needs as well, and an `UNSATISFIABLE` cover read off it would be a claim.
pub(super) fn lost_error_rules_result(
    smt_file: &std::path::Path,
    smt_content: &str,
    harness: &HarnessMetadata,
) -> ChcSolverResult {
    let mut properties = super::property_report::chc_undetermined_properties(smt_file, harness)
        .unwrap_or_else(|| {
            vec![Property {
                description: Cow::Borrowed(
                    "CHC verification: registered checks lost from the encoding — no rule derives \
                     error",
                ),
                property_id: PropertyId { fn_name: None, class: Cow::Borrowed("chc"), id: 0 },
                source_location: RawSourceLocation {
                    column: None,
                    file: None,
                    function: None,
                    line: None,
                },
                status: CheckStatus::Undetermined,
                trace: None,
            }]
        });
    let cover_names = crate::smt_io::extract_cover_declarations_from_content(smt_content);
    if !cover_names.is_empty() {
        let location_map =
            crate::ay_parse::load_vc_artifact(&crate::ay_parse::vc_artifact_path_for_smt(smt_file));
        let undecided = vec![None; cover_names.len()];
        properties.extend(crate::ay_parse::build_cover_properties_from_sat_checks(
            &cover_names,
            &undecided,
            location_map.as_ref(),
        ));
    }
    solver_stdout!(
        "[AY:UNKNOWN] CHC verification: registered checks but no rule derives error — lost \
         checks, not proved checks (no solver ran)"
    );
    ChcSolverResult {
        status: VerificationStatus::Failure,
        failed_properties: FailedProperties::Other,
        properties,
        proof_crosscheck: ProofCrosscheck::NotRun,
        proof_qualifiers: Vec::new(),
        proof_transcript_metadata: None,
        native_full_verification_verdict: None,
        solver_unknown_reason: Some(SolverUnknownReason::LostErrorRules),
        // No solver ran, so nothing was derived: the fail-closed reading.
        exact_counterexample: false,
    }
}
