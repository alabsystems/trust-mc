// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::{
    authority::ProgressAuthority, closure::ClosureProgress, inventory_view::ProgressInventory,
    output_format, output_report, report::ReportProgress,
};
use crate::progress::ProgressConfig;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProgressState {
    pub(crate) closure: ClosureProgress,
    pub(crate) report: Option<ReportProgress>,
    pub(crate) accepted_proof_quality: u64,
    pub(crate) closed_non_proof: u64,
    pub(crate) accounted: u64,
    pub(crate) complete: bool,
    pub(crate) status: &'static str,
}

pub(crate) fn build_progress_state(
    closure: ClosureProgress,
    report: Option<ReportProgress>,
    proof_denominator: u64,
    non_proof_expected: u64,
    mixed_denominator: u64,
) -> ProgressState {
    let accepted_proof_quality = report.as_ref().map_or(0, accepted_proof_quality);
    let closed_non_proof = if closure.valid { closure.rows } else { 0 };
    let accounted = accepted_proof_quality + closed_non_proof;
    let complete = is_complete(
        &closure,
        &report,
        proof_denominator,
        non_proof_expected,
        mixed_denominator,
        accounted,
    );
    let status = progress_status(report.as_ref(), complete);
    ProgressState {
        closure,
        report,
        accepted_proof_quality,
        closed_non_proof,
        accounted,
        complete,
        status,
    }
}

fn accepted_proof_quality(report: &ReportProgress) -> u64 {
    if report.authority_metadata && report.duplicate_keys == 0 { report.proof_quality } else { 0 }
}

pub(crate) fn format_progress_lines(
    config: &ProgressConfig,
    authority: &ProgressAuthority,
    mixed: &ProgressInventory,
    proof: &ProgressInventory,
    proof_expected: u64,
    non_proof_expected: u64,
    state: &ProgressState,
) -> Vec<String> {
    let mut lines = vec![
        output_format::format_command_line(config),
        output_format::format_workspace_authority(authority),
        output_format::format_authority_expectations(authority),
    ];
    lines.extend(output_format::format_manifest_lines(
        config,
        mixed,
        proof,
        proof_expected,
        non_proof_expected,
        state,
    ));
    lines.push(output_format::format_progress_calculation(mixed.denominator(), state));
    lines.extend(state.closure.failures.iter().map(|failure| format!("closure_problem {failure}")));
    if !state.closure.failures.is_empty() {
        lines.push(non_proof_closure_command());
    }
    lines.extend(output_report::format_report_lines(
        &state.report,
        proof.denominator(),
        state.accepted_proof_quality,
    ));
    lines
}

fn is_complete(
    closure: &ClosureProgress,
    report: &Option<ReportProgress>,
    proof_denominator: u64,
    non_proof_expected: u64,
    mixed_denominator: u64,
    accounted: u64,
) -> bool {
    report.as_ref().is_some_and(|report| {
        report.authority_metadata
            && report.duplicate_keys == 0
            && report.proof_seen == proof_denominator
            && report.proof_quality == proof_denominator
            && closure.valid
            && closure.rows == non_proof_expected
            && accounted == mixed_denominator
    })
}

fn progress_status(report: Option<&ReportProgress>, complete: bool) -> &'static str {
    if report.is_none() {
        "NO_REPORT"
    } else if complete {
        "COMPLETE"
    } else {
        "NOT_REPLACEMENT"
    }
}

fn non_proof_closure_command() -> String {
    "closure_command python3 scripts/generate_non_proof_closure.py".to_string()
}
