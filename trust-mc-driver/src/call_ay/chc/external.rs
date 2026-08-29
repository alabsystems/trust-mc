// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! External `ay` binary fallback for native CHC UNKNOWN results.

use std::borrow::Cow;
use std::path::Path;
use std::process::Command;

use trust_mc_metadata::HarnessMetadata;

use crate::ay_parse::parse_solver_output;
use crate::property_model::{CheckStatus, Property, PropertyId, RawSourceLocation};
use crate::session::{KaniSession, run_piped_with_timeout};
use crate::verification_result::{FailedProperties, ProofCrosscheck, VerificationStatus};

use super::ChcSolverResult;
use super::smt_analysis::smt_has_recursive_unwind_assertion;
use super::verdict_policy::{ChcOutcomeKind, apply_recursion_unwind_verdict, classify_chc_outcome};

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

fn external_ay_proved_safe(stdout: &str) -> bool {
    parse_solver_output(stdout).0 == VerificationStatus::Success
}

impl KaniSession {
    /// Try the latest external `ay` binary as a proof-only fallback after the
    /// linked native CHC portfolio returns an inconclusive UNKNOWN.
    ///
    /// This fallback is deliberately proof-only: `sat`, `unknown`, malformed
    /// output, and subprocess failures all return `Ok(None)` so the original
    /// native UNKNOWN remains authoritative.
    pub(in crate::call_ay) fn try_ay_chc_external_proof_fallback(
        &self,
        smt_file: &Path,
        smt_content: &str,
        harness: &HarnessMetadata,
        deadline: crate::deadline::Deadline,
    ) -> anyhow::Result<Option<ChcSolverResult>> {
        let Ok(ay_path) = which::which("ay") else {
            if self.args.common_args.verbose {
                solver_stdout!("[AY] External ay fallback skipped: ay not found in PATH");
            }
            return Ok(None);
        };

        if self.args.common_args.verbose {
            solver_stdout!(
                "[AY] Native ay-chc inconclusive; trying external ay binary: {}",
                ay_path.display()
            );
        }

        let solver_smt_content = crate::smt_io::strip_cover_assertions_for_chc_solver(smt_content);
        let solver_smt_path = if solver_smt_content.len() == smt_content.len() {
            None
        } else {
            let path = smt_file.with_extension("solver_chc.smt2");
            std::fs::write(&path, &solver_smt_content)?;
            Some(path)
        };

        // This fallback runs AFTER the native portfolio already consumed its
        // budget, so the per-harness deadline clamp is what stops the harness
        // total from reaching 2x the per-call timeout.
        let timeout =
            deadline.clamp(super::super::solver_timeout_duration(self.args.harness_timeout));
        let mut cmd = Command::new(&ay_path);
        cmd.arg(solver_smt_path.as_deref().unwrap_or(smt_file));
        let output = match run_piped_with_timeout(cmd, timeout) {
            Ok(output) => output,
            Err(err) => {
                if let Some(path) = &solver_smt_path {
                    let _ = std::fs::remove_file(path);
                }
                if self.args.common_args.verbose {
                    solver_stdout!("[AY] External ay fallback failed: {err}");
                }
                return Ok(None);
            }
        };
        if let Some(path) = &solver_smt_path {
            let _ = std::fs::remove_file(path);
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        if self.args.common_args.verbose {
            solver_stdout!("[AY] External ay fallback output:\n{stdout}");
            if !stderr.is_empty() {
                solver_stdout!("[AY] External ay fallback stderr:\n{stderr}");
            }
        }

        if !output.status.success() || !external_ay_proved_safe(&stdout) {
            return Ok(None);
        }

        let status = VerificationStatus::Success;
        let failed_props = FailedProperties::None;
        let mut properties = vec![Property {
            description: Cow::Borrowed("CHC verification: error unreachable (external ay)"),
            property_id: PropertyId { fn_name: None, class: Cow::Borrowed("chc"), id: 0 },
            source_location: RawSourceLocation {
                column: None,
                file: None,
                function: None,
                line: None,
            },
            status: CheckStatus::Success,
            trace: None,
        }];

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

        let has_recursive_unwind = smt_has_recursive_unwind_assertion(smt_content);
        let outcome = classify_chc_outcome(false, status, failed_props);
        let (status, failed_props, properties, outcome) = apply_recursion_unwind_verdict(
            has_recursive_unwind,
            outcome,
            status,
            failed_props,
            properties,
            Some(harness.pretty_name.as_str()),
        );

        match outcome {
            ChcOutcomeKind::Proof => {
                solver_stdout!("[AY:PROOF] CHC verification: property proven (external ay)");
            }
            ChcOutcomeKind::Counterexample => {
                solver_stdout!("[AY:CTREX] CHC verification: recursion unwinding assertion");
            }
            ChcOutcomeKind::ConservativeUnknown | ChcOutcomeKind::SolverUnknown => {
                solver_stdout!("[AY:UNKNOWN] CHC verification: solver returned unknown");
            }
        }

        Ok(Some(ChcSolverResult {
            status,
            failed_properties: failed_props,
            properties,
            proof_crosscheck: ProofCrosscheck::NotRun,
            proof_qualifiers: Vec::new(),
            proof_transcript_metadata: None,
            native_full_verification_verdict: None,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::external_ay_proved_safe;

    #[test]
    fn external_ay_proof_parser_accepts_certificate_unsat() {
        let output = "c ay.session.start build.commit=abc\nunsat\n;; AY CHC Certificate: SAFE\n";
        assert!(external_ay_proved_safe(output));
    }

    #[test]
    fn external_ay_proof_parser_rejects_non_proofs() {
        assert!(!external_ay_proved_safe("sat\n"));
        assert!(!external_ay_proved_safe("unknown\n"));
        assert!(!external_ay_proved_safe("c no final result\n"));
    }
}
