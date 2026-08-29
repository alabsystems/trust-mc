// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Verification result output and summary formatting.
//!
//! Contains `impl KaniSession` methods for processing harness output,
//! writing results to files, and printing the final verification summary.

use anyhow::{Context, Result, bail};
use std::env::current_dir;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};

use crate::args::OutputFormat;
use crate::demotion::is_effective_manual_success;
use crate::harness_runner::{HarnessResult, proof_qualifiers_marker};
use crate::session::{BUG_REPORT_URL, KaniSession};
use crate::verification_result::{
    CtrexCategory, ValidationStatus, VerificationResult, VerificationStatus,
};

impl KaniSession {
    pub(crate) fn process_output(
        &self,
        result: &VerificationResult,
        harness: &trust_mc_metadata::HarnessMetadata,
        thread_index: usize,
    ) -> Result<()> {
        if self.should_print_output() {
            if self.args.output_into_files {
                self.write_output_to_file(result, harness, thread_index)?;
            }

            if let Some(marker) = proof_qualifiers_marker(result) {
                println!("{marker}");
            }

            let output = result.render(&self.args.output_format, harness.attributes.should_panic);
            if rayon::current_num_threads() > 1 {
                println!("Thread {thread_index}: {output}");
            } else {
                println!("{output}");
            }
        }
        Ok(())
    }

    fn should_print_output(&self) -> bool {
        // `--output-format old` previously muted ALL per-harness output — the
        // VERIFICATION verdict line was never printed, so the runner branded
        // old-format runs `error` ("no verdict emitted") even when the driver
        // had a certified result (assert-location pair). `render` already
        // degrades gracefully for Old (summary + verdict, no per-check block),
        // so print it; Kani's old format prints a verdict too.
        !self.args.common_args.quiet
    }

    fn write_output_to_file(
        &self,
        result: &VerificationResult,
        harness: &trust_mc_metadata::HarnessMetadata,
        thread_index: usize,
    ) -> Result<()> {
        let target_dir =
            self.result_output_dir().context("Failed to determine output directory")?;
        let file_name = target_dir.join(&harness.pretty_name);
        let prefix = file_name.parent().unwrap_or(Path::new("."));

        std::fs::create_dir_all(prefix)
            .with_context(|| format!("Failed to create output directory {}", prefix.display()))?;
        let mut file = File::create(&file_name)
            .with_context(|| format!("Failed to create output file {}", file_name.display()))?;
        let mut file_output =
            result.render(&OutputFormat::Regular, harness.attributes.should_panic);
        if rayon::current_num_threads() > 1 {
            file_output = format!("Thread {thread_index}:\n{file_output}");
        }

        writeln!(file, "{file_output}")
            .with_context(|| format!("Failed to write to file {}", file_name.display()))?;
        Ok(())
    }

    fn result_output_dir(&self) -> Result<PathBuf> {
        let target_dir = match &self.args.target_dir {
            Some(d) => d.clone(),
            None => current_dir()?,
        };
        Ok(target_dir.join("result_output_dir")) //Hardcode output to result_output_dir, may want to make it adjustable?
    }

    /// Concludes a session by printing a summary report and exiting the process with an
    /// error code (if applicable).
    ///
    /// `metadata_harness_count`: the number of harnesses in the
    /// compiler-emitted metadata (BEFORE any `--harness` filtering). A count
    /// of 0 keys the zero-harness success-with-note verdict (task #49); it
    /// must never be derived from an empty result set, so a
    /// harness-discovery bug can never become a silent false-pass channel.
    ///
    /// `available_harnesses`: every harness name the metadata knows about, used
    /// to answer "then what ARE the names?" when a `--harness` filter matches
    /// nothing. The user cannot act on a rejection that does not say what the
    /// alternatives were.
    ///
    /// Note: Takes `self` "by ownership". This function wants to be able to drop before
    /// exiting with an error code, if needed.
    pub(crate) fn print_final_summary(
        self,
        results: &[HarnessResult<'_>],
        metadata_harness_count: usize,
        available_harnesses: &[String],
    ) -> Result<()> {
        if self.args.common_args.quiet {
            // Count failures even in quiet mode — exit(1) on failure (#3255)
            let manual_failures = results
                .iter()
                .filter(|r| {
                    !r.harness.is_automatically_generated
                        && !is_effective_manual_success(
                            r.result.status,
                            r.harness.attributes.should_panic,
                            r.result.failed_properties,
                        )
                })
                .count();
            let autoharness_failures = if self.autoharness_compiler_flags.is_some() {
                results
                    .iter()
                    .filter(|r| {
                        r.harness.is_automatically_generated
                            && r.result.status != VerificationStatus::Success
                    })
                    .count()
            } else {
                0
            };
            let unvalidated_success_count = results
                .iter()
                .filter(|r| {
                    !r.harness.is_automatically_generated
                        && is_effective_manual_success(
                            r.result.status,
                            r.harness.attributes.should_panic,
                            r.result.failed_properties,
                        )
                        && r.result.validation_status == ValidationStatus::Unvalidated
                })
                .count();
            if should_fail_final_summary(
                manual_failures,
                autoharness_failures,
                0,
                unvalidated_success_count,
                self.args.fail_on_unvalidated_success,
            ) {
                drop(self);
                std::process::exit(1);
            }
            // Check for unmatched harness filter (#3259)
            let manual_count =
                results.iter().filter(|r| !r.harness.is_automatically_generated).count();
            if manual_count == 0 && !self.args.harnesses.is_empty() {
                drop(self);
                std::process::exit(1);
            }
            return Ok(());
        }

        let (automatic, manual): (Vec<_>, Vec<_>) =
            results.iter().partition(|r| r.harness.is_automatically_generated);

        // A should_panic harness with PanicsOnly failures is effectively a success:
        // the test expected a panic/assertion failure, and one was found.
        let is_effective_success = |r: &&HarnessResult| {
            is_effective_manual_success(
                r.result.status,
                r.harness.attributes.should_panic,
                r.result.failed_properties,
            )
        };
        let (successes, non_successes): (Vec<_>, Vec<_>) =
            manual.into_iter().partition(is_effective_success);

        // Sub-partition successes: validated proofs vs unvalidated (NIA) proofs
        let (validated_successes, unvalidated_successes): (Vec<_>, Vec<_>) = successes
            .into_iter()
            .partition(|r| r.result.validation_status == ValidationStatus::Validated);

        let (failures, unvalidated): (Vec<_>, Vec<_>) = non_successes
            .into_iter()
            .partition(|r| r.result.validation_status == ValidationStatus::Validated);

        let succeeding = validated_successes.len();
        let unvalidated_success_count = unvalidated_successes.len();
        let failing = failures.len();
        let unvalidated_count = unvalidated.len();
        let total = succeeding + unvalidated_success_count + failing + unvalidated_count;

        if self.args.concrete_playback.is_some() {
            if failures.is_empty() {
                println!(
                    "INFO: The concrete playback feature never generated unit tests because there were no failing harnesses."
                )
            } else if failures.iter().all(|r| !r.result.generated_concrete_test) {
                eprintln!(
                    "The concrete playback feature did not generate unit tests, but there were failing harnesses. Please file a bug report at {BUG_REPORT_URL}"
                )
            }
        }

        println!("Manual Harness Summary:");

        for failure in &failures {
            println!("Verification failed for - {}", failure.harness.pretty_name);
        }

        for unval_success in &unvalidated_successes {
            println!(
                "Verification successful (unvalidated) for - {}",
                unval_success.harness.pretty_name
            );
        }

        for unval in &unvalidated {
            println!("Verification unvalidated (DT+BV) for - {}", unval.harness.pretty_name);
        }

        // CTREX classification breakdown (#3128, #3303, #3374)
        let mut ctrex_encoding_gap = 0usize;
        let mut ctrex_over_approx = 0usize;
        let mut ctrex_genuine = 0usize;
        let mut ctrex_unknown = 0usize;
        for r in failures.iter().chain(unvalidated.iter()) {
            match &r.result.ctrex_category {
                Some(CtrexCategory::EncodingGap { .. }) => ctrex_encoding_gap += 1,
                Some(CtrexCategory::OverApproximation { .. }) => ctrex_over_approx += 1,
                Some(CtrexCategory::Genuine) => ctrex_genuine += 1,
                Some(CtrexCategory::Unknown) => ctrex_unknown += 1,
                None => {} // Not a CTREX (e.g., demoted PROOF)
            }
        }
        let ctrex_total = ctrex_encoding_gap + ctrex_over_approx + ctrex_genuine + ctrex_unknown;
        // Printed AFTER the `Complete -` line, not here. Kani's summary is the
        // consecutive block `Summary: / Verification failed for - <h> /
        // Complete - ...`, and the corpus matches it as a block; a line
        // interposed between the per-harness list and `Complete -` breaks
        // every such expectation while adding nothing — the breakdown reads
        // the same below the block.
        let ctrex_breakdown = (ctrex_total > 0).then(|| {
            format!(
                "CTREX breakdown: {ctrex_encoding_gap} EncodingGap, \
                 {ctrex_over_approx} OverApproximation, {ctrex_genuine} Genuine, \
                 {ctrex_unknown} Unknown"
            )
        });

        if total > 0 {
            let unval_parts = [
                (unvalidated_success_count > 0)
                    .then(|| format!("{unvalidated_success_count} unvalidated proofs")),
                (unvalidated_count > 0).then(|| format!("{unvalidated_count} unvalidated (DT+BV)")),
            ];
            let unval_suffix: String =
                unval_parts.iter().filter_map(|p| p.as_deref()).collect::<Vec<_>>().join(", ");
            if unval_suffix.is_empty() {
                println!(
                    "Complete - {succeeding} successfully verified harnesses, {failing} failures, {total} total."
                );
            } else {
                println!(
                    "Complete - {succeeding} successfully verified harnesses, {failing} failures, {unval_suffix}, {total} total."
                );
            }
        }

        if let Some(breakdown) = ctrex_breakdown {
            println!("{breakdown}");
        }

        // The no-harness messaging below belongs to the `total == 0` case ONLY.
        // When 6baa4d11f moved the CTREX breakdown under `Complete -`, it
        // stitched this block onto `if let Some(breakdown)` instead — and a
        // fully SUCCESSFUL run also has no breakdown, so every clean run
        // printed "No proof harnesses ... were found to verify" after its own
        // `Complete - N successfully verified harnesses` line, and a clean run
        // with a single `--harness` filter bailed with "no harnesses matched
        // the harness filter" (exit 1) naming the very harness it had just
        // verified. Guard on total, as the pre-6baa4d11f structure did.
        if total == 0 {
            match self.args.harnesses.as_slice() {
                [] => {
                    // Exact Kani wording (kani-driver harness_runner.rs) — the
                    // corpus .expected files assert this line verbatim.
                    println!(
                        "No proof harnesses (functions with #[kani::proof]) were found to verify.\n\n\
                         To verify your code, add a function marked with the #[kani::proof] attribute:\n\n\
                         \x20 #[kani::proof]\n\
                         \x20 fn my_harness() {{\n\
                         \x20     let x: u32 = kani::any();\n\
                         \x20     my_function(x);\n\
                         \x20 }}\n\n\
                         For more information:\n\
                         \x20 - trust-mc explain harness   what you can write in a harness\n\
                         \x20 - trust-mc example --list    sample harnesses you can run now"
                    );
                    // Task #49: Kani treats a zero-harness crate as a SUCCESS
                    // (exit 0). Emit an explicit success-with-note verdict so
                    // runners see a real verdict instead of classifying the
                    // run as error/unknown. Guarded STRICTLY on the
                    // metadata-derived harness count: if metadata lists
                    // harnesses but none produced results, this must NOT
                    // report success (fail-closed).
                    if metadata_harness_count == 0 {
                        // A verdict, but NOT a success claim. Task #49 added a
                        // verdict line here so runners see one instead of
                        // classifying the run as error/unknown; it said
                        // SUCCESSFUL, which reads as "this crate is proved"
                        // when nothing was checked at all.
                        //
                        // The exit code stays 0 deliberately. Kani exits 0 on a
                        // zero-harness crate, seven script-based corpus tests
                        // run trust-mc on one under `set -eu`, and a workspace
                        // where a single member declares no harnesses should
                        // not fail the build. So the exit contract is the one
                        // documented exception in `explain exit-codes`, and the
                        // wording is what stops carrying a claim it cannot
                        // support.
                        println!(
                            "[AY:NO_HARNESSES] {}: nothing was verified — this crate declares no \
                             #[kani::proof] harnesses.",
                            self.args
                                .harnesses
                                .first()
                                .map_or("crate", std::string::String::as_str)
                        );
                        println!(
                            "VERIFICATION:- INCONCLUSIVE (no proof harnesses were found to verify)"
                        );
                    }
                }
                [harness] => {
                    bail!(
                        "no harnesses matched the harness filter: `{harness}`{}",
                        harness_suggestions(harness, available_harnesses)
                    )
                }
                harnesses => {
                    bail!(
                        "no harnesses matched the harness filters: `{}`{}",
                        harnesses.join("`, `"),
                        harness_suggestions("", available_harnesses)
                    )
                }
            }
        }

        if self.args.coverage {
            self.show_coverage_summary()?;
        }

        let autoharness_failing = if self.autoharness_compiler_flags.is_some() {
            self.print_autoharness_summary(automatic)?
        } else {
            0
        };

        if should_fail_final_summary(
            failing,
            autoharness_failing,
            unvalidated_count,
            unvalidated_success_count,
            self.args.fail_on_unvalidated_success,
        ) {
            // Failure exit code: validated failures, autoharness failures, and
            // unvalidated (DT+BV) failures all indicate non-success.
            // DT+BV demotion means the proof quality is lower, not that a
            // failure result should be treated as success. (Part of #2090)
            drop(self);
            std::process::exit(1);
        }

        Ok(())
    }

    /// Show a coverage summary.
    ///
    /// This is just a placeholder for now.
    fn show_coverage_summary(&self) -> Result<()> {
        Ok(())
    }
}

fn should_fail_final_summary(
    failing: usize,
    autoharness_failing: usize,
    unvalidated_count: usize,
    unvalidated_success_count: usize,
    fail_on_unvalidated_success: bool,
) -> bool {
    failing + autoharness_failing + unvalidated_count > 0
        || (fail_on_unvalidated_success && unvalidated_success_count > 0)
}

#[cfg(test)]
mod tests {
    use super::should_fail_final_summary;
    use super::*;
    use crate::args::CargoKaniArgs;
    use crate::session::KaniSession;
    use crate::test_support::{test_harness, test_result};
    use crate::verification_result::{FailedProperties, VerificationStatus};
    use clap::Parser;
    use std::sync::Mutex;

    fn test_session_with_target(target_dir: PathBuf) -> KaniSession {
        let mut args = CargoKaniArgs::try_parse_from(["cargo-trust-mc"]).unwrap().verify_opts;
        args.output_into_files = true;
        args.target_dir = Some(target_dir);
        KaniSession {
            args,
            autoharness_compiler_flags: None,
            install: crate::session::InstallType::new().expect("install type"),
            temporaries: Mutex::default(),
        }
    }

    #[test]
    fn unvalidated_successes_do_not_fail_by_default() {
        assert!(!should_fail_final_summary(0, 0, 0, 1, false));
    }

    #[test]
    fn fail_on_unvalidated_successes_fails_when_requested() {
        assert!(should_fail_final_summary(0, 0, 0, 1, true));
    }

    #[test]
    fn existing_non_successes_still_fail_without_new_flag() {
        assert!(should_fail_final_summary(1, 0, 0, 0, false));
        assert!(should_fail_final_summary(0, 1, 0, 0, false));
        assert!(should_fail_final_summary(0, 0, 1, 0, false));
    }

    #[test]
    fn per_harness_output_file_write_failures_are_errors() {
        let temp = tempfile::tempdir().unwrap();
        let blocked_target_dir = temp.path().join("not_a_directory");
        File::create(&blocked_target_dir).unwrap();
        let session = test_session_with_target(blocked_target_dir);
        let result = test_result(VerificationStatus::Success, FailedProperties::None);
        let harness = test_harness("proof_harness", "test_crate");

        let error = session.write_output_to_file(&result, &harness, 0).unwrap_err();

        assert!(error.to_string().contains("Failed to create output directory"));
    }

    #[test]
    fn process_output_propagates_requested_output_file_failures() {
        let temp = tempfile::tempdir().unwrap();
        let blocked_target_dir = temp.path().join("not_a_directory");
        File::create(&blocked_target_dir).unwrap();
        let session = test_session_with_target(blocked_target_dir);
        let result = test_result(VerificationStatus::Success, FailedProperties::None);
        let harness = test_harness("proof_harness", "test_crate");

        let error = session.process_output(&result, &harness, 0).unwrap_err();

        assert!(error.to_string().contains("Failed to create output directory"));
    }
}

/// Tell the user how to find the harness names that do exist.
///
/// `--harness` takes a substring filter, so a typo (or a name from a different
/// file) simply matches nothing. Reporting only that the filter failed leaves
/// the user to work out what they should have typed.
///
/// The names are usually NOT in hand here: the compiler codegens only the
/// harnesses that match the filter, so when the filter matches nothing the
/// metadata this function is handed is empty -- which is exactly the case that
/// produced the error. Claiming "this crate has no harnesses" from that would
/// be false for any crate whose harnesses simply have other names. So point at
/// the listing instead, and only name names when a caller genuinely has the
/// unfiltered set.
fn harness_suggestions(filter: &str, available: &[String]) -> String {
    if available.is_empty() {
        return "\n       `--harness` matches by substring. Run `trust-mc --list <FILE.rs>`\n       \
                (or `cargo trust-mc --list`) to see the harness names in this crate."
            .to_string();
    }

    let closest = (!filter.is_empty())
        .then(|| {
            available
                .iter()
                .map(|name| (edit_distance(filter, name), name))
                .filter(|(distance, name)| *distance * 3 <= name.len().max(filter.len()) * 2)
                .min_by_key(|(distance, _)| *distance)
                .map(|(_, name)| name)
        })
        .flatten();

    // Long lists are worse than no list; point at `--list` past a readable few.
    const MAX_LISTED: usize = 10;
    let listed: Vec<&str> = available.iter().take(MAX_LISTED).map(String::as_str).collect();
    let more = available.len().saturating_sub(listed.len());
    let tail =
        if more > 0 { format!(", and {more} more (`--list` for all)") } else { String::new() };

    match closest {
        Some(name) => format!(
            "\n       Did you mean `{name}`?\n       Harnesses in this crate: {}{tail}",
            listed.join(", ")
        ),
        None => format!("\n       Harnesses in this crate: {}{tail}", listed.join(", ")),
    }
}

/// Levenshtein distance, used only to rank a typo against real harness names.
fn edit_distance(a: &str, b: &str) -> usize {
    let b_chars: Vec<char> = b.chars().collect();
    let mut previous: Vec<usize> = (0..=b_chars.len()).collect();
    let mut current = vec![0usize; b_chars.len() + 1];

    for (i, a_char) in a.chars().enumerate() {
        current[0] = i + 1;
        for (j, b_char) in b_chars.iter().enumerate() {
            let substitution = previous[j] + usize::from(a_char != *b_char);
            current[j + 1] = substitution.min(previous[j + 1] + 1).min(current[j] + 1);
        }
        std::mem::swap(&mut previous, &mut current);
    }
    previous[b_chars.len()]
}
