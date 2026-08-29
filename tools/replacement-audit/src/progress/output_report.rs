// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::{output_format::pct, report::ReportProgress};
use std::collections::BTreeMap;

const MAX_REPORT_SOURCE_PATHS: usize = 12;
const MAX_AUTHORITY_FAILURE_DETAILS: usize = 24;
const MAX_COUNT_SUMMARY_ITEMS: usize = 12;
const MAX_KEY_EXAMPLES: usize = 12;

pub(super) fn format_report_lines(
    report: &Option<ReportProgress>,
    proof_denominator: u64,
    accepted_proof_quality: u64,
) -> Vec<String> {
    let Some(report) = report else {
        return vec![
            "report none; proof progress is not measured".to_string(),
            "proof_report_problem missing --report; proof progress requires a clean current schema-v2 per-harness report".to_string(),
            proof_report_input_note(),
            proof_report_progress_command(),
        ];
    };
    let mut lines = vec![
        format_report_metadata(report),
        format_report_sources(report),
        format_report_rows(report, proof_denominator, accepted_proof_quality),
        format_proof_acceptance(report, accepted_proof_quality),
        format_duplicate_key_policy(report),
        format_counts("report_status_counts", &report.status_counts),
        format_counts("report_verdict_counts", &report.verdict_counts),
        format_top_counts("proof_non_quality_categories", &report.non_quality_categories),
        format_top_counts("proof_non_quality_reasons", &report.non_quality_reasons),
        format_top_counts("proof_missing_categories", &report.missing_categories),
        format_key_examples(
            "proof_non_quality_examples",
            &report.non_quality_examples,
            report.proof_seen.saturating_sub(report.proof_quality),
        ),
        format_key_examples(
            "proof_missing_examples",
            &report.missing_examples,
            proof_denominator.saturating_sub(report.proof_seen),
        ),
        format_key_examples(
            "proof_duplicate_examples",
            &report.duplicate_examples,
            report.duplicate_keys,
        ),
    ];
    lines.extend(format_report_source_details(report));
    lines.extend(format_report_problems(report, proof_denominator));
    lines
}

fn format_report_metadata(report: &ReportProgress) -> String {
    format!(
        "report path={} authority_metadata={} status={} clean_tree={} tree_state={} commit={} ay_pin={} tree_fingerprint={} row_sha256={}",
        report.path.display(),
        report.authority_metadata,
        report.report_status,
        report.tree_state == "clean",
        report.tree_state,
        report.commit,
        report.ay_pin,
        report.tree_fingerprint,
        report.row_sha256,
    )
}

fn format_report_sources(report: &ReportProgress) -> String {
    if report.paths.len() == 1 {
        return format!("report_sources count=1 path={}", report.paths[0].display());
    }
    let paths = report
        .paths
        .iter()
        .take(MAX_REPORT_SOURCE_PATHS)
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>()
        .join(",");
    if report.paths.len() <= MAX_REPORT_SOURCE_PATHS {
        return format!("report_sources count={} paths={paths}", report.paths.len());
    }
    format!(
        "report_sources count={} paths_sample={paths} omitted={}",
        report.paths.len(),
        report.paths.len() - MAX_REPORT_SOURCE_PATHS
    )
}

fn format_report_source_details(report: &ReportProgress) -> Vec<String> {
    report
        .sources
        .iter()
        .take(MAX_REPORT_SOURCE_PATHS)
        .enumerate()
        .map(|(index, source)| {
            format!(
                "report_source index={} path={} rows={} file_sha256={} row_sha256={}",
                index + 1,
                source.path.display(),
                source.rows,
                source.file_sha256,
                source.row_sha256,
            )
        })
        .collect()
}

fn format_report_rows(
    report: &ReportProgress,
    proof_denominator: u64,
    accepted_proof_quality: u64,
) -> String {
    format!(
        "report_rows total={} duplicate_keys={} proof_inventory_seen={}/{} proof_quality={}/{} ({}) accepted_proof_quality={}/{} ({})",
        report.total,
        report.duplicate_keys,
        report.proof_seen,
        proof_denominator,
        report.proof_quality,
        proof_denominator,
        pct(report.proof_quality, proof_denominator),
        accepted_proof_quality,
        proof_denominator,
        pct(accepted_proof_quality, proof_denominator),
    )
}

fn format_proof_acceptance(report: &ReportProgress, accepted_proof_quality: u64) -> String {
    format!(
        "proof_acceptance raw_proof_quality={} accepted_proof_quality={} authority_metadata={} duplicate_keys={} rule=authority_metadata_and_duplicate_keys_zero",
        report.proof_quality,
        accepted_proof_quality,
        report.authority_metadata,
        report.duplicate_keys,
    )
}

fn format_duplicate_key_policy(report: &ReportProgress) -> String {
    format!(
        "duplicate_key_policy duplicate_keys={} accepted={}",
        report.duplicate_keys,
        report.duplicate_keys == 0,
    )
}

fn format_report_problems(report: &ReportProgress, proof_denominator: u64) -> Vec<String> {
    let mut lines = Vec::new();
    append_authority_problems(report, &mut lines);
    if report.duplicate_keys != 0 {
        lines.push(format!(
            "proof_report_problem {}: duplicate harness keys rejected={}",
            report.path.display(),
            report.duplicate_keys
        ));
    }
    if report.proof_seen != proof_denominator {
        lines.push(format!(
            "proof_report_problem {}: proof inventory coverage {}/{}; supply a current full schema-v2 report or repeated shard reports that cover the frozen proof inventory",
            report.path.display(),
            report.proof_seen,
            proof_denominator
        ));
    }
    if report.proof_quality != proof_denominator {
        lines.push(format!(
            "proof_report_problem {}: proof quality {}/{}; rows must be PASS/PROOF, trusted_proof=true, proof_qualifiers=clean, final_marker=PROOF, with no fallback, demotion, translation-drop, retry, known-fp, should-panic, or no-error-rule trivial-safe metadata",
            report.path.display(),
            report.proof_quality,
            proof_denominator
        ));
    }
    if !lines.is_empty() {
        lines.push(proof_report_input_note());
        lines.push(proof_report_progress_command());
    }
    lines
}

fn append_authority_problems(report: &ReportProgress, lines: &mut Vec<String>) {
    for failure in ordered_authority_failures(&report.authority_failures)
        .into_iter()
        .take(MAX_AUTHORITY_FAILURE_DETAILS)
    {
        lines.push(format!(
            "proof_report_problem {}: authority metadata rejected: {failure}",
            report.path.display()
        ));
    }
    if report.authority_failures.len() > MAX_AUTHORITY_FAILURE_DETAILS {
        lines.insert(
            0,
            format!(
                "proof_report_problem {}: authority metadata rejected: {} failures; showing {}",
                report.path.display(),
                report.authority_failures.len(),
                MAX_AUTHORITY_FAILURE_DETAILS
            ),
        );
        lines.push(format!(
            "proof_report_problem {}: authority metadata rejected: omitted={}",
            report.path.display(),
            report.authority_failures.len() - MAX_AUTHORITY_FAILURE_DETAILS
        ));
    }
}

fn ordered_authority_failures(failures: &[String]) -> Vec<&String> {
    let mut ordered = failures.iter().collect::<Vec<_>>();
    ordered
        .sort_by_key(|failure| if failure.starts_with("merged reports disagree") { 0 } else { 1 });
    ordered
}

fn format_counts(label: &str, counts: &BTreeMap<String, u64>) -> String {
    format_bounded_counts(label, counts.iter().collect())
}

fn format_top_counts(label: &str, counts: &BTreeMap<String, u64>) -> String {
    let mut values = counts.iter().collect::<Vec<_>>();
    values.sort_by(|(left_key, left_value), (right_key, right_value)| {
        right_value.cmp(left_value).then_with(|| left_key.cmp(right_key))
    });
    format_bounded_counts(label, values)
}

fn format_bounded_counts(label: &str, values: Vec<(&String, &u64)>) -> String {
    if values.is_empty() {
        return format!("{label} none");
    }
    let total_keys = values.len();
    let summary = values
        .into_iter()
        .take(MAX_COUNT_SUMMARY_ITEMS)
        .map(|(key, value)| format!("{key}={value}"))
        .collect::<Vec<_>>()
        .join(" ");
    if total_keys <= MAX_COUNT_SUMMARY_ITEMS {
        return format!("{label} {summary}");
    }
    format!("{label} {summary} omitted_keys={}", total_keys - MAX_COUNT_SUMMARY_ITEMS)
}

fn format_key_examples(label: &str, examples: &[String], total: u64) -> String {
    if total == 0 {
        return format!("{label} none");
    }
    let sample = examples.iter().take(MAX_KEY_EXAMPLES).cloned().collect::<Vec<_>>().join(",");
    let shown = examples.len().min(MAX_KEY_EXAMPLES);
    let omitted = total.saturating_sub(shown as u64);
    if omitted == 0 {
        return format!("{label} count={total} keys={sample}");
    }
    format!("{label} count={total} keys_sample={sample} omitted={omitted}")
}

fn proof_report_input_note() -> String {
    "proof_report_input full schema-v2 per-harness reports may be supplied directly; rows outside the proof inventory are ignored for the proof numerator".to_string()
}

fn proof_report_progress_command() -> String {
    "proof_report_command cargo run --manifest-path tools/replacement-audit/Cargo.toml --locked --bin replacement-progress -- --require-complete --report reports/compiletest-per-harness-latest-trust_mc.json".to_string()
}
