// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use clap::{Parser, ValueEnum};
use replacement_audit::{
    AuditConfig, AuditFailure, AuditResult, audit_report_text, inventory::Inventory,
    non_proof_closure::validate_non_proof_closure_text,
};
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::ExitCode;

#[derive(Debug, Parser)]
#[command(
    name = "replacement-audit",
    about = "Audit trust_mc compiletest per-harness JSON reports for replacement criteria"
)]
struct Args {
    #[arg(
        long,
        required = true,
        value_name = "COMMIT",
        help = "Require report commit to match this 40-character commit"
    )]
    expected_commit: String,

    #[arg(
        long,
        required = true,
        value_name = "PIN",
        help = "Require report ay_pin to match this 40-character AY commit"
    )]
    expected_ay_pin: String,

    #[arg(
        long,
        required = true,
        value_name = "DIGEST",
        help = "Require report tree_fingerprint to match this 64-character digest"
    )]
    expected_tree_fingerprint: String,

    #[arg(
        long,
        required = true,
        value_name = "N",
        help = "Require this exact harness denominator"
    )]
    expected_harnesses: u64,

    #[arg(
        long,
        required = true,
        value_name = "DIGEST",
        help = "Require inventory row_sha256 to match this 64-character digest"
    )]
    expected_inventory_sha: String,

    #[arg(
        long,
        required = true,
        value_name = "INVENTORY_JSON",
        help = "Require report harness keys to match this frozen inventory"
    )]
    inventory: PathBuf,

    #[arg(
        long,
        value_name = "CLOSURE_JSON",
        help = "Validate non-PROOF closure rows against the closure inventory"
    )]
    non_proof_closure: Option<PathBuf>,

    #[arg(
        long,
        value_name = "INVENTORY_JSON",
        requires = "non_proof_closure",
        help = "Inventory used to validate non-PROOF closure rows"
    )]
    closure_inventory: Option<PathBuf>,

    #[arg(
        long,
        value_enum,
        default_value_t = SummaryMode::Terse,
        help = "Choose the success summary format"
    )]
    summary_mode: SummaryMode,

    #[arg(value_name = "REPORT", required = true)]
    reports: Vec<PathBuf>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
enum SummaryMode {
    Terse,
    KaniCompatible,
}

fn main() -> ExitCode {
    let args = Args::parse();
    let mut combined = AuditResult::default();
    validate_cli_authority(&args, &mut combined);
    let inventory = load_inventory(&args, &mut combined);
    load_non_proof_closure(&args, &mut combined);
    let config = AuditConfig {
        expected_commit: Some(args.expected_commit.clone()),
        expected_ay_pin: Some(args.expected_ay_pin.clone()),
        expected_tree_fingerprint: Some(args.expected_tree_fingerprint.clone()),
        expected_harnesses: Some(args.expected_harnesses),
        inventory,
    };
    audit_reports(&args.reports, &config, &mut combined);
    exit_with_result(&combined, &args)
}

fn load_non_proof_closure(args: &Args, combined: &mut AuditResult) {
    let Some(path) = &args.non_proof_closure else {
        return;
    };
    let inventory_path = args.closure_inventory.as_ref().unwrap_or(&args.inventory);
    let Some(inventory) = load_inventory_path(inventory_path, None, combined) else {
        return;
    };
    match fs::read_to_string(path) {
        Ok(text) => {
            combined.failures.extend(validate_non_proof_closure_text(
                &path.display().to_string(),
                &text,
                &inventory,
            ));
        }
        Err(err) => combined.failures.push(AuditFailure::new(
            path.display().to_string(),
            format!("failed to read non-proof closure: {err}"),
        )),
    }
}

fn validate_cli_authority(args: &Args, combined: &mut AuditResult) {
    if args.expected_harnesses == 0 {
        combined
            .failures
            .push(AuditFailure::new("CLI", "--expected-harnesses must be greater than 0"));
    }
    if !is_sha256_hex(&args.expected_inventory_sha) {
        combined.failures.push(AuditFailure::new(
            "CLI",
            format!(
                "--expected-inventory-sha {:?} is not a 64-character hex digest",
                args.expected_inventory_sha
            ),
        ));
    }
}

fn load_inventory(args: &Args, combined: &mut AuditResult) -> Option<Inventory> {
    load_inventory_path(&args.inventory, Some(args.expected_inventory_sha.as_str()), combined)
}

fn load_inventory_path(
    path: &PathBuf,
    expected_inventory_sha: Option<&str>,
    combined: &mut AuditResult,
) -> Option<Inventory> {
    match fs::read_to_string(path) {
        Ok(text) => match Inventory::from_manifest_text(path.display().to_string(), &text) {
            Ok(inventory) => {
                if let Some(expected_inventory_sha) = expected_inventory_sha
                    && is_sha256_hex(expected_inventory_sha)
                    && inventory.row_sha256 != expected_inventory_sha
                {
                    combined.failures.push(AuditFailure::new(
                        path.display().to_string(),
                        format!(
                            "inventory row_sha256 {} does not match expected {}",
                            inventory.row_sha256, expected_inventory_sha
                        ),
                    ));
                }
                Some(inventory)
            }
            Err(err) => {
                combined.failures.push(AuditFailure::new(path.display().to_string(), err));
                None
            }
        },
        Err(err) => {
            combined.failures.push(AuditFailure::new(
                path.display().to_string(),
                format!("failed to read inventory: {err}"),
            ));
            None
        }
    }
}

fn audit_reports(reports: &[PathBuf], config: &AuditConfig, combined: &mut AuditResult) {
    for report in reports {
        let label = report.display().to_string();
        match fs::read_to_string(report) {
            Ok(text) => combined.merge(audit_report_text(&label, &text, config.clone())),
            Err(err) => combined
                .failures
                .push(AuditFailure::new(label, format!("failed to read report: {err}"))),
        }
    }
}

fn exit_with_result(combined: &AuditResult, args: &Args) -> ExitCode {
    if combined.is_ok() {
        let mut stdout = io::stdout().lock();
        match args.summary_mode {
            SummaryMode::Terse => {
                let _ = writeln!(stdout, "{}", combined.totals.summary_line());
            }
            SummaryMode::KaniCompatible => {
                let _ = writeln!(
                    stdout,
                    "KANI-COMPATIBLE PROOF GATE: PASS reports={} proof_denominator={} pass={} xfail={} commit={} ay_pin={} tree_fingerprint={} inventory_row_sha={}",
                    combined.totals.reports,
                    args.expected_harnesses,
                    combined.totals.pass,
                    combined.totals.xfail,
                    args.expected_commit,
                    args.expected_ay_pin,
                    args.expected_tree_fingerprint,
                    args.expected_inventory_sha
                );
            }
        }
        ExitCode::SUCCESS
    } else {
        let mut stderr = io::stderr().lock();
        for failure in &combined.failures {
            let _ = writeln!(stderr, "{failure}");
        }
        let _ =
            writeln!(stderr, "replacement audit failed: {} problem(s)", combined.failures.len());
        ExitCode::FAILURE
    }
}

fn is_sha256_hex(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}
