// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use clap::Parser;
use replacement_audit::{
    AuditFailure, inventory::Inventory, non_proof_closure::validate_non_proof_closure_text,
};
use sha2::{Digest, Sha256};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

#[derive(Debug, Parser)]
#[command(
    name = "replacement-closure-check",
    about = "Validate trust_mc replacement inventory and non-PROOF closure without a proof report"
)]
struct Args {
    #[arg(
        long,
        value_name = "INVENTORY_JSON",
        default_value = "tests/trust-mc/replacement-harness-inventory.json",
        help = "Mixed replacement accounting inventory"
    )]
    inventory: PathBuf,

    #[arg(
        long,
        value_name = "DIGEST",
        help = "Require inventory row_sha256 to match this 64-character digest"
    )]
    expected_inventory_sha: Option<String>,

    #[arg(
        long,
        value_name = "CLOSURE_JSON",
        default_value = "tests/trust-mc/non-proof-closure.json",
        help = "Checked closure for non-PROOF mixed-inventory rows"
    )]
    non_proof_closure: PathBuf,

    #[arg(
        long,
        value_name = "DIGEST",
        help = "Require raw non-proof closure file SHA-256 to match this 64-character digest"
    )]
    expected_non_proof_closure_sha: Option<String>,
}

fn main() -> ExitCode {
    let args = Args::parse();
    let failures = check_closure(&args);
    if failures.is_empty() {
        ExitCode::SUCCESS
    } else {
        print_failures(&failures);
        ExitCode::FAILURE
    }
}

fn check_closure(args: &Args) -> Vec<AuditFailure> {
    let mut failures = Vec::new();
    validate_expected_digest(
        "CLI",
        "--expected-inventory-sha",
        &args.expected_inventory_sha,
        &mut failures,
    );
    validate_expected_digest(
        "CLI",
        "--expected-non-proof-closure-sha",
        &args.expected_non_proof_closure_sha,
        &mut failures,
    );

    let inventory = load_inventory(&args.inventory, &args.expected_inventory_sha, &mut failures);
    let closure_text = load_text("non-proof closure", &args.non_proof_closure, &mut failures);

    if let (Some(inventory), Some(closure_text)) = (&inventory, &closure_text) {
        let closure_sha = sha256_hex(closure_text.as_bytes());
        if let Some(expected) = &args.expected_non_proof_closure_sha
            && is_sha256_hex(expected)
            && closure_sha != *expected
        {
            failures.push(AuditFailure::new(
                args.non_proof_closure.display().to_string(),
                format!(
                    "non-proof closure sha256 {closure_sha} does not match expected {expected}"
                ),
            ));
        }
        failures.extend(validate_non_proof_closure_text(
            &args.non_proof_closure.display().to_string(),
            closure_text,
            inventory,
        ));

        if failures.is_empty() {
            emit_success(inventory, &closure_sha);
        }
    }

    failures
}

fn emit_success(inventory: &Inventory, closure_sha: &str) {
    let mut stdout = io::stdout().lock();
    let _ = writeln!(
        stdout,
        "NON-PROOF-CLOSURE: PASS inventory_denominator={} non_proof_denominator={} inventory_row_sha={} non_proof_closure_sha={}",
        inventory.denominator,
        inventory.non_proof_denominator(),
        inventory.row_sha256,
        closure_sha
    );
}

fn print_failures(failures: &[AuditFailure]) {
    let mut stderr = io::stderr().lock();
    for failure in failures {
        let _ = writeln!(stderr, "{failure}");
    }
    let _ = writeln!(stderr, "replacement closure check failed: {} problem(s)", failures.len());
}

fn validate_expected_digest(
    label: &str,
    flag: &str,
    expected: &Option<String>,
    failures: &mut Vec<AuditFailure>,
) {
    let Some(expected) = expected else {
        return;
    };
    if !is_sha256_hex(expected) {
        failures.push(AuditFailure::new(
            label,
            format!("{flag} {expected:?} is not a 64-character hex digest"),
        ));
    }
}

fn load_inventory(
    path: &Path,
    expected_sha: &Option<String>,
    failures: &mut Vec<AuditFailure>,
) -> Option<Inventory> {
    let text = load_text("inventory", path, failures)?;
    match Inventory::from_manifest_text(path.display().to_string(), &text) {
        Ok(inventory) => {
            if let Some(expected) = expected_sha
                && is_sha256_hex(expected)
                && inventory.row_sha256 != *expected
            {
                failures.push(AuditFailure::new(
                    path.display().to_string(),
                    format!(
                        "inventory row_sha256 {} does not match expected {}",
                        inventory.row_sha256, expected
                    ),
                ));
            }
            Some(inventory)
        }
        Err(err) => {
            failures.push(AuditFailure::new(path.display().to_string(), err));
            None
        }
    }
}

fn load_text(kind: &str, path: &Path, failures: &mut Vec<AuditFailure>) -> Option<String> {
    match fs::read_to_string(path) {
        Ok(text) => Some(text),
        Err(err) => {
            failures.push(AuditFailure::new(
                path.display().to_string(),
                format!("failed to read {kind}: {err}"),
            ));
            None
        }
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(64);
    for byte in digest {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

fn is_sha256_hex(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}
