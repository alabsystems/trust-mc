// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::path::PathBuf;
use std::process::Command;
use std::{env, fs, process};

const FIXTURE_COMMIT: &str = "0123456789abcdef0123456789abcdef01234567";
const FIXTURE_AY_PIN: &str = "90e42a0e32bcc178f4732a49679a92ba18a0fe65";
const FIXTURE_TREE_FINGERPRINT: &str =
    "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
}

fn fixture_authority_args() -> [&'static str; 6] {
    [
        "--expected-commit",
        FIXTURE_COMMIT,
        "--expected-ay-pin",
        FIXTURE_AY_PIN,
        "--expected-tree-fingerprint",
        FIXTURE_TREE_FINGERPRINT,
    ]
}

fn progress_command() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_replacement-progress"));
    command
        .args(["--inventory", &fixture_path("inventory.json").display().to_string()])
        .args(["--proof-inventory", &fixture_path("inventory.json").display().to_string()])
        .args([
            "--non-proof-closure",
            &fixture_path("non_proof_closure_empty.json").display().to_string(),
        ])
        .args(fixture_authority_args());
    command
}

#[test]
fn progress_cli_reports_complete_fixture() {
    let output = progress_command()
        .args(["--report", &fixture_path("clean.json").display().to_string()])
        .arg("--require-complete")
        .output()
        .expect("replacement-progress should run");

    assert!(
        output.status.success(),
        "expected success, stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("KANI_REPLACEMENT_PROGRESS status=COMPLETE"));
    assert!(stdout.contains("replacement_progress_command cargo run"));
    assert!(stdout.contains(
        "authority_expectations commit=0123456789abcdef0123456789abcdef01234567 commit_source=cli"
    ));
    assert!(stdout.contains("accounted=2/2 (100.0%)"));
    assert!(stdout.contains("accepted_proof_quality=2/2 (100.0%)"));
    assert!(stdout.contains("progress_calculation accepted_proof_quality=2 closed_non_proof=0 accounted=2+0=2 denominator=2 percent=100.0%"));
    assert!(stdout.contains("proof_inventory"));
    assert!(stdout.contains("progress=2/2 (100.0%)"));
    assert!(stdout.contains("authority_metadata=true"));
    assert!(stdout.contains("clean_tree=true"));
    assert!(stdout.contains("row_sha256="));
    assert!(stdout.contains("duplicate_keys=0"));
    assert!(stdout.contains("duplicate_key_policy duplicate_keys=0 accepted=true"));
    assert!(stdout.contains("proof_acceptance raw_proof_quality=2 accepted_proof_quality=2"));
    assert!(stdout.contains("proof_non_quality_categories none"));
    assert!(stdout.contains("proof_non_quality_reasons none"));
    assert!(stdout.contains("proof_missing_categories none"));
    assert!(stdout.contains("proof_non_quality_examples none"));
    assert!(stdout.contains("proof_missing_examples none"));
    assert!(stdout.contains("proof_duplicate_examples none"));
    assert!(stdout.contains("report_source index=1"));
    assert!(stdout.contains("file_sha256="));
}

#[test]
fn progress_cli_merges_repeated_report_arguments() {
    let report: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/clean.json")).expect("clean fixture");
    let rows = report
        .get("harnesses")
        .and_then(serde_json::Value::as_array)
        .expect("fixture harness rows")
        .clone();

    let mut left = report.clone();
    *left.get_mut("harnesses").expect("left harnesses") = serde_json::json!([rows[0].clone()]);
    let mut right = report;
    *right.get_mut("harnesses").expect("right harnesses") = serde_json::json!([rows[1].clone()]);

    let left_path =
        env::temp_dir().join(format!("replacement-progress-left-{}.json", process::id()));
    let right_path =
        env::temp_dir().join(format!("replacement-progress-right-{}.json", process::id()));
    fs::write(&left_path, serde_json::to_string(&left).expect("left report JSON"))
        .expect("left report should be writable");
    fs::write(&right_path, serde_json::to_string(&right).expect("right report JSON"))
        .expect("right report should be writable");

    let output = progress_command()
        .arg("--report")
        .arg(left_path.as_os_str())
        .arg("--report")
        .arg(right_path.as_os_str())
        .arg("--require-complete")
        .output()
        .expect("replacement-progress should run");
    let _ = fs::remove_file(&left_path);
    let _ = fs::remove_file(&right_path);

    assert!(
        output.status.success(),
        "expected success, stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("KANI_REPLACEMENT_PROGRESS status=COMPLETE"));
    assert!(stdout.contains("report path=<2 reports> authority_metadata=true"));
    assert!(stdout.contains("report_sources count=2"));
    assert!(stdout.contains("report_source index=1"));
    assert!(stdout.contains("report_source index=2"));
    assert!(stdout.contains("proof_inventory_seen=2/2 proof_quality=2/2"));
}

#[test]
fn progress_cli_reports_no_report_without_failing() {
    let output = progress_command().output().expect("replacement-progress should run");

    assert!(
        output.status.success(),
        "expected success, stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("KANI_REPLACEMENT_PROGRESS status=NO_REPORT"));
    assert!(stdout.contains("accounted=0/2 (0.0%)"));
    assert!(stdout.contains("report none; proof progress is not measured"));
    assert!(stdout.contains("proof_report_problem missing --report"));
    assert!(stdout.contains(
        "proof_report_input full schema-v2 per-harness reports may be supplied directly"
    ));
}

#[test]
fn progress_cli_measures_partial_clean_proof_report_without_requiring_completion() {
    let report: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/clean.json")).expect("clean fixture");
    let rows = report
        .get("harnesses")
        .and_then(serde_json::Value::as_array)
        .expect("fixture harness rows")
        .clone();

    let mut partial = report;
    *partial.get_mut("harnesses").expect("partial harnesses") =
        serde_json::json!([rows[0].clone()]);

    let report_path =
        env::temp_dir().join(format!("replacement-progress-partial-{}.json", process::id()));
    fs::write(&report_path, serde_json::to_string(&partial).expect("partial report JSON"))
        .expect("partial report should be writable");

    let output = Command::new(env!("CARGO_BIN_EXE_replacement-progress"))
        .args([
            "--inventory",
            &fixture_path("mixed_inventory_with_closure.json").display().to_string(),
        ])
        .args(["--proof-inventory", &fixture_path("inventory.json").display().to_string()])
        .args([
            "--non-proof-closure",
            &fixture_path("non_proof_closure_one.json").display().to_string(),
        ])
        .args(fixture_authority_args())
        .arg("--report")
        .arg(report_path.as_os_str())
        .output()
        .expect("replacement-progress should run");
    let _ = fs::remove_file(&report_path);

    assert!(
        output.status.success(),
        "partial measurement should not require complete accounting, stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("KANI_REPLACEMENT_PROGRESS status=NOT_REPLACEMENT"));
    assert!(stdout.contains("accounted=2/3 (66.7%)"));
    assert!(stdout.contains("accepted_proof_quality=1/2 (50.0%)"));
    assert!(stdout.contains("closed_non_proof=1/1 (100.0%)"));
    assert!(stdout.contains("progress=1/2 (50.0%)"));
    assert!(stdout.contains("rows=1/1 valid=true"));
    assert!(stdout.contains("proof_inventory_seen=1/2 proof_quality=1/2"));
    assert!(stdout.contains("proof_missing_categories example.rs=1"));
    assert!(stdout.contains("proof_missing_examples count=1 keys=zani/example.rs::proof_two"));
    assert!(stdout.contains("proof_report_problem"));
    assert!(stdout.contains("proof inventory coverage 1/2"));
}

#[test]
fn progress_cli_require_complete_rejects_missing_report() {
    let output = progress_command()
        .arg("--require-complete")
        .output()
        .expect("replacement-progress should run");

    assert!(!output.status.success(), "expected failure without a report");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("KANI_REPLACEMENT_PROGRESS status=NO_REPORT"));
    assert!(stdout.contains("report none; proof progress is not measured"));
    assert!(
        stdout.contains("proof progress requires a clean current schema-v2 per-harness report")
    );
}

#[test]
fn progress_cli_explains_stale_report_evidence() {
    let output = progress_command()
        .args(["--report", &fixture_path("stale.json").display().to_string()])
        .arg("--require-complete")
        .output()
        .expect("replacement-progress should run");

    assert!(!output.status.success(), "expected failure with stale report evidence");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("KANI_REPLACEMENT_PROGRESS status=NOT_REPLACEMENT"));
    assert!(stdout.contains("accounted=0/2 (0.0%)"));
    assert!(stdout.contains("authority_metadata=false"));
    assert!(stdout.contains("progress=0/2 (0.0%)"));
    assert!(stdout.contains("accepted_proof_quality=0/2 (0.0%)"));
    assert!(stdout.contains("proof_report_problem"));
    assert!(stdout.contains("report_status \"stale\" != \"current\""));
    assert!(stdout.contains("proof quality 1/2"));
    assert!(stdout.contains("proof inventory coverage 1/2"));
    assert!(stdout.contains(
        "proof_report_input full schema-v2 per-harness reports may be supplied directly"
    ));
}

#[test]
fn progress_cli_rejects_duplicate_report_keys_for_accepted_progress() {
    let mut report: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/clean.json")).expect("clean fixture");
    let rows = report
        .get("harnesses")
        .and_then(serde_json::Value::as_array)
        .expect("fixture harness rows")
        .clone();
    report
        .get_mut("harnesses")
        .expect("harnesses")
        .as_array_mut()
        .expect("harnesses array")
        .push(rows[0].clone());

    let report_path =
        env::temp_dir().join(format!("replacement-progress-duplicate-{}.json", process::id()));
    fs::write(&report_path, serde_json::to_string(&report).expect("duplicate report JSON"))
        .expect("duplicate report should be writable");

    let output = progress_command()
        .arg("--report")
        .arg(report_path.as_os_str())
        .arg("--require-complete")
        .output()
        .expect("replacement-progress should run");
    let _ = fs::remove_file(&report_path);

    assert!(!output.status.success(), "expected failure with duplicate report key");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("KANI_REPLACEMENT_PROGRESS status=NOT_REPLACEMENT"));
    assert!(stdout.contains("proof_inventory"));
    assert!(stdout.contains("progress=0/2 (0.0%)"));
    assert!(stdout.contains("proof_acceptance raw_proof_quality=2 accepted_proof_quality=0"));
    assert!(stdout.contains("duplicate_key_policy duplicate_keys=1 accepted=false"));
    assert!(stdout.contains("duplicate harness keys rejected=1"));
}

#[test]
fn progress_cli_bounds_large_report_diagnostics() {
    let stale_report = fixture_path("stale.json").display().to_string();
    let mut command = progress_command();
    for _ in 0..30 {
        command.args(["--report", &stale_report]);
    }

    let output = command.output().expect("replacement-progress should run");

    assert!(
        output.status.success(),
        "diagnostic-only partial measurement should not require completion, stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("report_sources count=30 paths_sample="));
    assert!(stdout.contains("omitted=18"));
    assert!(stdout.contains("authority metadata rejected:"));
    assert!(stdout.contains("failures; showing 24"));
    assert!(stdout.contains("authority metadata rejected: omitted="));
}

#[test]
fn progress_cli_bounds_count_summaries() {
    let mut report: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/clean.json")).expect("clean fixture");
    let rows = report
        .get_mut("harnesses")
        .and_then(serde_json::Value::as_array_mut)
        .expect("fixture harness rows");
    for index in 0..20 {
        rows.push(serde_json::json!({
            "file": format!("extra/category_{index}/case.rs"),
            "harness": format!("harness_{index}"),
            "status": format!("STATUS_{index:02}"),
            "expected": "CTREX",
            "verdict": format!("VERDICT_{index:02}")
        }));
    }

    let report_path =
        env::temp_dir().join(format!("replacement-progress-many-counts-{}.json", process::id()));
    fs::write(&report_path, serde_json::to_string(&report).expect("report JSON should serialize"))
        .expect("many-count report should be writable");

    let output = progress_command()
        .args(["--report", &report_path.display().to_string()])
        .output()
        .expect("replacement-progress should run");
    let _ = fs::remove_file(&report_path);

    assert!(
        output.status.success(),
        "diagnostic-only count summary should not require completion, stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.lines().any(
            |line| line.starts_with("report_status_counts ") && line.contains("omitted_keys=9")
        )
    );
    assert!(
        stdout
            .lines()
            .any(|line| line.starts_with("report_verdict_counts ")
                && line.contains("omitted_keys=9"))
    );
}

#[test]
fn progress_cli_reports_non_quality_reasons() {
    let mut report: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/clean.json")).expect("clean fixture");
    let row = report
        .get_mut("harnesses")
        .and_then(serde_json::Value::as_array_mut)
        .and_then(|rows| rows.first_mut())
        .and_then(serde_json::Value::as_object_mut)
        .expect("fixture first harness row");
    row.remove("proof_qualifiers");
    row.insert("trusted_proof".to_string(), serde_json::Value::Bool(false));
    row.insert("sound_fallback_count".to_string(), serde_json::Value::from(2));
    row.insert("demotion_reasons".to_string(), serde_json::json!(["fallback=1"]));
    row.insert(
        "translation_drop_reasons".to_string(),
        serde_json::json!({"missing_projection": 1}),
    );
    row.insert("retried".to_string(), serde_json::Value::Bool(false));

    let report_path =
        env::temp_dir().join(format!("replacement-progress-bad-quality-{}.json", process::id()));
    fs::write(&report_path, serde_json::to_string(&report).expect("report JSON should serialize"))
        .expect("bad quality report should be writable");

    let output = progress_command()
        .args(["--report", &report_path.display().to_string()])
        .arg("--require-complete")
        .output()
        .expect("replacement-progress should run");
    let _ = fs::remove_file(&report_path);

    assert!(!output.status.success(), "expected failure with non-quality row");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("proof_quality=1/2"));
    assert!(stdout.contains("proof_non_quality_reasons"));
    assert!(stdout.contains("proof_qualifiers_missing=1"));
    assert!(stdout.contains("proof_non_quality_examples count=1 keys=zani/example.rs::proof_one"));
    assert!(stdout.contains("trusted_proof_not_true=1"));
    assert!(stdout.contains("sound_fallback_count_not_zero=1"));
    assert!(stdout.contains("demotion_reasons_nonempty=1"));
    assert!(stdout.contains("translation_drop_reasons_nonempty=1"));
    assert!(stdout.contains("retry_metadata_present=1"));
}

#[test]
fn progress_cli_reports_should_panic_as_non_quality() {
    let mut report: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/clean.json")).expect("clean fixture");
    let row = report
        .get_mut("harnesses")
        .and_then(serde_json::Value::as_array_mut)
        .and_then(|rows| rows.first_mut())
        .and_then(serde_json::Value::as_object_mut)
        .expect("fixture first harness row");
    row.insert(
        "proof_qualifiers".to_string(),
        serde_json::Value::String("should_panic".to_string()),
    );

    let report_path =
        env::temp_dir().join(format!("replacement-progress-should-panic-{}.json", process::id()));
    fs::write(&report_path, serde_json::to_string(&report).expect("report JSON should serialize"))
        .expect("should-panic report should be writable");

    let output = progress_command()
        .args(["--report", &report_path.display().to_string()])
        .arg("--require-complete")
        .output()
        .expect("replacement-progress should run");
    let _ = fs::remove_file(&report_path);

    assert!(!output.status.success(), "expected failure with should-panic row");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("proof_quality=1/2"));
    assert!(stdout.contains("proof_non_quality_reasons"));
    assert!(stdout.contains("proof_qualifiers_should_panic=1"));
}

#[test]
fn progress_cli_reports_trivial_safe_no_error_rule_as_non_quality() {
    let mut report: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/clean.json")).expect("clean fixture");
    let row = report
        .get_mut("harnesses")
        .and_then(serde_json::Value::as_array_mut)
        .and_then(|rows| rows.first_mut())
        .and_then(serde_json::Value::as_object_mut)
        .expect("fixture first harness row");
    row.insert(
        "proof_qualifiers".to_string(),
        serde_json::Value::String("trivial_safe=no_error_rule".to_string()),
    );

    let report_path =
        env::temp_dir().join(format!("replacement-progress-trivial-safe-{}.json", process::id()));
    fs::write(&report_path, serde_json::to_string(&report).expect("report JSON should serialize"))
        .expect("trivial-safe report should be writable");

    let output = progress_command()
        .args(["--report", &report_path.display().to_string()])
        .arg("--require-complete")
        .output()
        .expect("replacement-progress should run");
    let _ = fs::remove_file(&report_path);

    assert!(!output.status.success(), "expected failure with trivial-safe row");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("proof_quality=1/2"));
    assert!(stdout.contains("proof_non_quality_reasons"));
    assert!(stdout.contains("proof_qualifiers_trivial_safe_no_error_rule=1"));
}

#[test]
fn progress_cli_rejects_stale_solver_binary_attestation() {
    let output = progress_command()
        .args(["--report", &fixture_path("stale_solver_binary.json").display().to_string()])
        .arg("--require-complete")
        .output()
        .expect("replacement-progress should run");

    assert!(!output.status.success(), "expected failure with stale solver evidence");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("KANI_REPLACEMENT_PROGRESS status=NOT_REPLACEMENT"));
    assert!(stdout.contains("accounted=0/2 (0.0%)"));
    assert!(stdout.contains("authority_metadata=false"));
    assert!(stdout.contains("progress=0/2 (0.0%)"));
    assert!(stdout.contains("proof_quality=2/2"));
    assert!(stdout.contains("accepted_proof_quality=0/2 (0.0%)"));
    assert!(stdout.contains("solver_binary.commit \"abcdef0\" does not match report ay_pin"));
    assert!(
        stdout.contains("solver_binary.version commit \"abcdef0\" does not match report ay_pin")
    );
}

#[test]
fn progress_cli_accounts_proof_report_and_non_proof_closure_separately() {
    let output = Command::new(env!("CARGO_BIN_EXE_replacement-progress"))
        .args([
            "--inventory",
            &fixture_path("mixed_inventory_with_closure.json").display().to_string(),
        ])
        .args(["--proof-inventory", &fixture_path("inventory.json").display().to_string()])
        .args([
            "--non-proof-closure",
            &fixture_path("non_proof_closure_one.json").display().to_string(),
        ])
        .args(fixture_authority_args())
        .args(["--report", &fixture_path("clean.json").display().to_string()])
        .arg("--require-complete")
        .output()
        .expect("replacement-progress should run");

    assert!(
        output.status.success(),
        "expected success, stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("KANI_REPLACEMENT_PROGRESS status=COMPLETE"));
    assert!(stdout.contains("accounted=3/3 (100.0%)"));
    assert!(stdout.contains("accepted_proof_quality=2/2 (100.0%)"));
    assert!(stdout.contains("closed_non_proof=1/1 (100.0%)"));
    assert!(stdout.contains("mixed_expected PROOF=2 CTREX=1"));
    assert!(stdout.contains("proof_inventory"));
    assert!(stdout.contains("progress=2/2 (100.0%)"));
    assert!(stdout.contains("non_proof_closure"));
    assert!(stdout.contains("rows=1/1 valid=true"));
}
