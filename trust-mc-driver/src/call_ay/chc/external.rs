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
    /// Try the pinned external `ay` binary as a proof-only fallback after the
    /// linked native CHC portfolio returns an inconclusive UNKNOWN.
    ///
    /// This fallback is deliberately proof-only: `sat`, `unknown`, malformed
    /// output, and subprocess failures all return `Ok(None)` so the original
    /// native UNKNOWN remains authoritative.
    ///
    /// `budget` is the stage budget the caller computed against the
    /// per-harness deadline (`run_ay` decides whether to attempt the fallback
    /// at all and prints the `[AY:EXTERNAL_AY_FALLBACK:...]` disposition);
    /// `deadline` still bounds the cover checks a proof triggers.
    pub(in crate::call_ay) fn try_ay_chc_external_proof_fallback(
        &self,
        smt_file: &Path,
        smt_content: &str,
        harness: &HarnessMetadata,
        budget: std::time::Duration,
        deadline: crate::deadline::Deadline,
    ) -> anyhow::Result<Option<ChcSolverResult>> {
        // Located and pin-checked like every other `ay` subprocess
        // (`crate::ay_binary`). Unusable -- absent, or off-pin and not allowed --
        // fails closed: the native UNKNOWN stays authoritative.
        let ay_path = match crate::ay_binary::pinned_ay() {
            Ok(path) => path,
            Err(err) => {
                eprintln!("[AY] external ay fallback: no usable ay binary ({err:#})");
                return Ok(None);
            }
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
        // budget; `budget` is what the per-harness deadline has left for it
        // (capped at one per-call timeout), so the harness total cannot reach
        // 2x the per-call timeout.
        let timeout = budget;
        let mut cmd = Command::new(&ay_path);
        // The fallback is another lane of the same harness, in its own
        // process: without a ceiling it runs under the ay CLI's default (85% of
        // the host's RAM on Linux), outside the driver's armed cap. It gets
        // the harness envelope instead (AY ask R2), re-measured now because
        // the driver's footprint at THIS moment is what it shares the cap with.
        if let Some(mb) = super::resource_envelope::external_ay_memory_mb(
            super::resource_envelope::HarnessMemoryEnvelope::for_current_harness(),
        ) {
            eprintln!(
                "[AY] external ay fallback memory ceiling: --memory {mb} (MiB, harness envelope)"
            );
            cmd.arg("--memory").arg(mb.to_string());
        }
        // A deadline of its own inside the budget, like every `ay` child
        // (`crate::ay_binary::orphan_deadline_ms`): the driver still kills it at
        // `timeout`, first on an undecided query, and `-t` bounds it when the
        // driver cannot. It runs in its own process group, and a SIGKILL of the
        // driver's group (the retry parent's timeout, an outer runner's
        // `killpg`) left it solving with no time bound (measured 2026-10-01:
        // alive 120 s later at 1.6 GB RSS).
        cmd.arg("-t").arg(crate::ay_binary::orphan_deadline_ms(timeout).to_string());
        let solver_input = solver_smt_path.as_deref().unwrap_or(smt_file);
        cmd.arg(solver_input);
        let export_args: Vec<String> =
            cmd.get_args().map(|arg| arg.to_string_lossy().into_owned()).collect();
        let started = std::time::Instant::now();
        let output = match run_piped_with_timeout(cmd, timeout) {
            Ok(output) => output,
            Err(err) => {
                super::row_export::record_external_fallback(
                    &harness.pretty_name,
                    solver_input,
                    &export_args,
                    timeout,
                    started.elapsed(),
                    Err(err.to_string()),
                );
                if let Some(path) = &solver_smt_path {
                    let _ = std::fs::remove_file(path);
                }
                if self.args.common_args.verbose {
                    solver_stdout!("[AY] External ay fallback failed: {err}");
                }
                return Ok(None);
            }
        };
        super::row_export::record_external_fallback(
            &harness.pretty_name,
            solver_input,
            &export_args,
            timeout,
            started.elapsed(),
            Ok(&output),
        );
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

        // Same V4 vacuity question the native proof paths ask
        // (`native_result::apply_chc_vacuity_probe`): an external `unsat` on
        // `(query error)` is equally UNSAT when the harness cannot run at all.
        self.apply_chc_vacuity_probe(smt_content, smt_file, &mut properties, deadline);

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
            solver_unknown_reason: None,
            status,
            failed_properties: failed_props,
            properties,
            proof_crosscheck: ProofCrosscheck::NotRun,
            proof_qualifiers: Vec::new(),
            proof_transcript_metadata: None,
            native_full_verification_verdict: None,
            exact_counterexample: false,
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
