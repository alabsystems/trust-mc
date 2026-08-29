// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

mod authority;
mod closure;
mod inventory_view;
mod output;
mod output_format;
mod output_report;
mod report;
mod report_authority;

use authority::resolve_progress_authority;
use closure::load_closure;
use inventory_view::ProgressInventory;
use output::{build_progress_state, format_progress_lines};
use report::load_report_progresses;
use std::path::PathBuf;

#[derive(Debug, Clone)]
pub struct ProgressConfig {
    pub inventory: PathBuf,
    pub proof_inventory: PathBuf,
    pub non_proof_closure: PathBuf,
    pub reports: Vec<PathBuf>,
    pub expected_commit: Option<String>,
    pub expected_ay_pin: Option<String>,
    pub expected_tree_fingerprint: Option<String>,
    pub repo_root: PathBuf,
    pub require_complete: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProgressOutput {
    pub lines: Vec<String>,
    pub complete: bool,
    pub require_complete: bool,
}

pub fn run(config: &ProgressConfig) -> Result<ProgressOutput, String> {
    let mixed = ProgressInventory::load(&config.inventory)?;
    let proof = ProgressInventory::load(&config.proof_inventory)?;
    let proof_expected = mixed.count_expected("PROOF");
    let non_proof_expected = mixed.denominator().saturating_sub(proof_expected);
    validate_proof_denominator(&proof, proof_expected)?;

    let authority = resolve_progress_authority(config)?;
    let closure = load_closure(&config.non_proof_closure, mixed.audit_inventory())?;
    let report = if config.reports.is_empty() {
        None
    } else {
        Some(load_report_progresses(&config.reports, &proof, &authority)?)
    };
    let state = build_progress_state(
        closure,
        report,
        proof.denominator(),
        non_proof_expected,
        mixed.denominator(),
    );
    let lines = format_progress_lines(
        config,
        &authority,
        &mixed,
        &proof,
        proof_expected,
        non_proof_expected,
        &state,
    );
    Ok(ProgressOutput {
        lines,
        complete: state.complete,
        require_complete: config.require_complete,
    })
}

fn validate_proof_denominator(
    proof: &ProgressInventory,
    proof_expected: u64,
) -> Result<(), String> {
    if proof.denominator() == proof_expected {
        return Ok(());
    }
    Err(format!(
        "proof inventory denominator {} does not match mixed PROOF count {proof_expected}",
        proof.denominator()
    ))
}
