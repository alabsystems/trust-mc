// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::path::PathBuf;
use std::process::Command;

fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
}

fn authority_args() -> Vec<String> {
    vec![
        "--expected-commit".to_string(),
        "0123456789abcdef0123456789abcdef01234567".to_string(),
        "--expected-ay-pin".to_string(),
        "90e42a0e32bcc178f4732a49679a92ba18a0fe65".to_string(),
        "--expected-tree-fingerprint".to_string(),
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".to_string(),
        "--expected-harnesses".to_string(),
        "2".to_string(),
        "--expected-inventory-sha".to_string(),
        "cdbeb76c8e818eeead59b5f5127ff91e98175124dbabd0d81317461b1d547627".to_string(),
        "--inventory".to_string(),
        fixture_path("inventory.json").display().to_string(),
    ]
}

#[test]
fn cli_exits_success_for_clean_report() {
    let output = Command::new(env!("CARGO_BIN_EXE_replacement-audit"))
        .args(authority_args())
        .arg(fixture_path("clean.json"))
        .output()
        .expect("replacement-audit should run");

    assert!(
        output.status.success(),
        "expected success, stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("OK: reports=1 total=2 pass=2"),
        "unexpected stdout:\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn cli_can_emit_kani_compatible_summary() {
    let output = Command::new(env!("CARGO_BIN_EXE_replacement-audit"))
        .args(authority_args())
        .args(["--summary-mode", "kani-compatible"])
        .arg(fixture_path("clean.json"))
        .output()
        .expect("replacement-audit should run");

    assert!(
        output.status.success(),
        "expected success, stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("KANI-COMPATIBLE PROOF GATE: PASS"), "unexpected stdout:\n{stdout}");
    assert!(stdout.contains("proof_denominator=2"), "unexpected stdout:\n{stdout}");
    assert!(
        stdout.contains("commit=0123456789abcdef0123456789abcdef01234567"),
        "unexpected stdout:\n{stdout}"
    );
    assert!(
        stdout.contains("ay_pin=90e42a0e32bcc178f4732a49679a92ba18a0fe65"),
        "unexpected stdout:\n{stdout}"
    );
    assert!(
        stdout.contains(
            "tree_fingerprint=0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
        ),
        "unexpected stdout:\n{stdout}"
    );
    assert!(
        stdout.contains(
            "inventory_row_sha=cdbeb76c8e818eeead59b5f5127ff91e98175124dbabd0d81317461b1d547627"
        ),
        "unexpected stdout:\n{stdout}"
    );
}

#[test]
fn cli_exits_failure_for_summary_rejection() {
    let output = Command::new(env!("CARGO_BIN_EXE_replacement-audit"))
        .args(authority_args())
        .arg(fixture_path("bad_summary.json"))
        .output()
        .expect("replacement-audit should run");

    assert!(!output.status.success(), "expected failure for bad summary");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("summary.fail is 1"), "unexpected stderr:\n{stderr}");
    assert!(stderr.contains("replacement audit failed"), "unexpected stderr:\n{stderr}");
}

#[test]
fn cli_requires_authority_tuple_for_clean_report() {
    let output = Command::new(env!("CARGO_BIN_EXE_replacement-audit"))
        .arg(fixture_path("clean.json"))
        .output()
        .expect("replacement-audit should run");

    assert!(!output.status.success(), "expected failure without authority tuple");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("--expected-commit"), "unexpected stderr:\n{stderr}");
    assert!(stderr.contains("--inventory"), "unexpected stderr:\n{stderr}");
}

#[test]
fn cli_rejects_inventory_sha_mismatch() {
    let mut args = authority_args();
    let inventory_sha_index = args
        .iter()
        .position(|arg| arg == "--expected-inventory-sha")
        .expect("authority args include inventory sha")
        + 1;
    args[inventory_sha_index] =
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".to_string();

    let output = Command::new(env!("CARGO_BIN_EXE_replacement-audit"))
        .args(args)
        .arg(fixture_path("clean.json"))
        .output()
        .expect("replacement-audit should run");

    assert!(!output.status.success(), "expected inventory SHA mismatch failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("inventory row_sha256"), "unexpected stderr:\n{stderr}");
}

#[test]
fn cli_accepts_non_proof_closure_argument() {
    let output = Command::new(env!("CARGO_BIN_EXE_replacement-audit"))
        .args(authority_args())
        .args(["--non-proof-closure", "/definitely/missing/non-proof-closure.json"])
        .arg(fixture_path("clean.json"))
        .output()
        .expect("replacement-audit should run");

    assert!(!output.status.success(), "expected failure for missing closure file");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("failed to read non-proof closure"), "unexpected stderr:\n{stderr}");
}

#[test]
fn closure_check_validates_inventory_and_non_proof_closure_without_report() {
    let output = Command::new(env!("CARGO_BIN_EXE_replacement-closure-check"))
        .args(["--inventory", &fixture_path("inventory.json").display().to_string()])
        .args([
            "--expected-inventory-sha",
            "cdbeb76c8e818eeead59b5f5127ff91e98175124dbabd0d81317461b1d547627",
        ])
        .args([
            "--non-proof-closure",
            &fixture_path("non_proof_closure_empty.json").display().to_string(),
        ])
        .args([
            "--expected-non-proof-closure-sha",
            "fb78d2254e9be8a11099b1a6dbdb2ee23cb879ea59add46dc5d24543a743deaf",
        ])
        .output()
        .expect("replacement-closure-check should run");

    assert!(
        output.status.success(),
        "expected success, stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("NON-PROOF-CLOSURE: PASS"), "unexpected stdout:\n{stdout}");
    assert!(stdout.contains("inventory_denominator=2"), "unexpected stdout:\n{stdout}");
    assert!(stdout.contains("non_proof_denominator=0"), "unexpected stdout:\n{stdout}");
}

#[test]
fn closure_check_rejects_non_proof_closure_sha_mismatch() {
    let output = Command::new(env!("CARGO_BIN_EXE_replacement-closure-check"))
        .args(["--inventory", &fixture_path("inventory.json").display().to_string()])
        .args([
            "--non-proof-closure",
            &fixture_path("non_proof_closure_empty.json").display().to_string(),
        ])
        .args([
            "--expected-non-proof-closure-sha",
            "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        ])
        .output()
        .expect("replacement-closure-check should run");

    assert!(!output.status.success(), "expected closure SHA mismatch failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("non-proof closure sha256"), "unexpected stderr:\n{stderr}");
}
