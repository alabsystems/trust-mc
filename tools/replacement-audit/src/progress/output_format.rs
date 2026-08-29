// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::{
    authority::{ExpectedAuthority, ProgressAuthority},
    inventory_view::ProgressInventory,
    output::ProgressState,
};
use crate::progress::ProgressConfig;
use std::collections::BTreeMap;

pub(super) fn format_manifest_lines(
    config: &ProgressConfig,
    mixed: &ProgressInventory,
    proof: &ProgressInventory,
    proof_expected: u64,
    non_proof_expected: u64,
    state: &ProgressState,
) -> Vec<String> {
    vec![
        format!(
            "KANI_REPLACEMENT_PROGRESS status={} accounted={}/{} ({}) accepted_proof_quality={}/{} ({}) closed_non_proof={}/{} ({})",
            state.status,
            state.accounted,
            mixed.denominator(),
            pct(state.accounted, mixed.denominator()),
            state.accepted_proof_quality,
            proof.denominator(),
            pct(state.accepted_proof_quality, proof.denominator()),
            state.closed_non_proof,
            non_proof_expected,
            pct(state.closed_non_proof, non_proof_expected),
        ),
        format!(
            "mixed_inventory path={} denominator={} row_sha256={}",
            config.inventory.display(),
            mixed.denominator(),
            mixed.row_sha256(),
        ),
        format_mixed_expected(proof_expected, mixed.expected_counts()),
        format!(
            "proof_inventory path={} denominator={} row_sha256={} progress={}/{} ({})",
            config.proof_inventory.display(),
            proof.denominator(),
            proof.row_sha256(),
            state.accepted_proof_quality,
            proof.denominator(),
            pct(state.accepted_proof_quality, proof.denominator()),
        ),
        format!(
            "non_proof_closure path={} rows={}/{} valid={} closed_non_proof={}/{} ({}) sha256={}",
            config.non_proof_closure.display(),
            state.closure.rows,
            non_proof_expected,
            state.closure.valid,
            state.closed_non_proof,
            non_proof_expected,
            pct(state.closed_non_proof, non_proof_expected),
            state.closure.sha256,
        ),
    ]
}

pub(super) fn format_command_line(config: &ProgressConfig) -> String {
    let mut args = vec![
        "cargo".to_string(),
        "run".to_string(),
        "--manifest-path".to_string(),
        "tools/replacement-audit/Cargo.toml".to_string(),
        "--locked".to_string(),
        "--bin".to_string(),
        "replacement-progress".to_string(),
        "--".to_string(),
        "--inventory".to_string(),
        config.inventory.display().to_string(),
        "--proof-inventory".to_string(),
        config.proof_inventory.display().to_string(),
        "--non-proof-closure".to_string(),
        config.non_proof_closure.display().to_string(),
        "--repo-root".to_string(),
        config.repo_root.display().to_string(),
    ];
    push_optional(&mut args, "--expected-commit", config.expected_commit.as_deref());
    push_optional(&mut args, "--expected-ay-pin", config.expected_ay_pin.as_deref());
    push_optional(
        &mut args,
        "--expected-tree-fingerprint",
        config.expected_tree_fingerprint.as_deref(),
    );
    for report in &config.reports {
        args.push("--report".to_string());
        args.push(report.display().to_string());
    }
    if config.require_complete {
        args.push("--require-complete".to_string());
    }
    format!(
        "replacement_progress_command {}",
        args.iter().map(|arg| shell_quote(arg)).collect::<Vec<_>>().join(" ")
    )
}

pub(super) fn format_workspace_authority(authority: &ProgressAuthority) -> String {
    let problems = if authority.workspace.problems.is_empty() {
        "none".to_string()
    } else {
        shell_quote(&authority.workspace.problems.join(";"))
    };
    format!(
        "workspace_authority repo_root={} git_head={} tree_state={} ay_pin={} ay_pin_source={} problems={}",
        authority.workspace.repo_root.display(),
        optional_label(authority.workspace.git_head.as_deref()),
        authority.workspace.tree_state,
        optional_label(authority.workspace.ay_pin.as_deref()),
        authority.workspace.ay_pin_source,
        problems,
    )
}

pub(super) fn format_authority_expectations(authority: &ProgressAuthority) -> String {
    format!(
        "authority_expectations commit={} commit_source={} ay_pin={} ay_pin_source={} tree_fingerprint={} tree_fingerprint_source={}",
        expected_label(&authority.expected_commit),
        authority.expected_commit.source,
        expected_label(&authority.expected_ay_pin),
        authority.expected_ay_pin.source,
        expected_label(&authority.expected_tree_fingerprint),
        authority.expected_tree_fingerprint.source,
    )
}

pub(super) fn format_progress_calculation(mixed_denominator: u64, state: &ProgressState) -> String {
    format!(
        "progress_calculation accepted_proof_quality={} closed_non_proof={} accounted={}+{}={} denominator={} percent={} formula=accepted_proof_quality+closed_non_proof",
        state.accepted_proof_quality,
        state.closed_non_proof,
        state.accepted_proof_quality,
        state.closed_non_proof,
        state.accounted,
        mixed_denominator,
        pct(state.accounted, mixed_denominator),
    )
}

fn push_optional(args: &mut Vec<String>, flag: &str, value: Option<&str>) {
    if let Some(value) = value {
        args.push(flag.to_string());
        args.push(value.to_string());
    }
}

fn shell_quote(value: &str) -> String {
    if value.bytes().all(|byte| {
        byte.is_ascii_alphanumeric() || matches!(byte, b'/' | b'.' | b'_' | b'-' | b':' | b'=')
    }) {
        return value.to_string();
    }
    format!("'{}'", value.replace('\'', "'\\''"))
}

fn expected_label(expected: &ExpectedAuthority) -> String {
    optional_label(expected.value.as_deref())
}

fn optional_label(value: Option<&str>) -> String {
    value.unwrap_or("unavailable").to_string()
}

fn format_mixed_expected(proof_expected: u64, counts: &BTreeMap<String, u64>) -> String {
    format!(
        "mixed_expected PROOF={} CTREX={} UNKNOWN={} BMC_SAFE={} ERROR={}",
        proof_expected,
        count(counts, "CTREX"),
        count(counts, "UNKNOWN"),
        count(counts, "BMC_SAFE"),
        count(counts, "ERROR"),
    )
}

fn count(counts: &BTreeMap<String, u64>, key: &str) -> u64 {
    counts.get(key).copied().unwrap_or(0)
}

pub(super) fn pct(numerator: u64, denominator: u64) -> String {
    if denominator == 0 {
        return "n/a".to_string();
    }
    format!("{:.1}%", (numerator as f64 * 100.0) / denominator as f64)
}
