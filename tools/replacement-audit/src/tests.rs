// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use serde_json::{Map, Value};

const CLEAN: &str = include_str!("../tests/fixtures/clean.json");
const STALE: &str = include_str!("../tests/fixtures/stale.json");
const BAD_SUMMARY: &str = include_str!("../tests/fixtures/bad_summary.json");
const BAD_HARNESS: &str = include_str!("../tests/fixtures/bad_harness.json");
const XFAIL_NON_PROOF: &str = include_str!("../tests/fixtures/xfail_non_proof.json");
const BAD_METADATA: &str = include_str!("../tests/fixtures/bad_metadata.json");
const BAD_PROOF_ROW: &str = include_str!("../tests/fixtures/bad_proof_row.json");
const BAD_SUMMARY_ROWS: &str = include_str!("../tests/fixtures/bad_summary_rows.json");
const FULL_INVENTORY: &str =
    include_str!("../../../tests/trust-mc/replacement-harness-inventory.json");

fn audit_fixture(name: &str, text: &str) -> AuditResult {
    audit_report_text(name, text, AuditConfig::default())
}

fn assert_failure_contains(result: &AuditResult, needle: &str) {
    assert!(
        result.failures.iter().any(|failure| failure.message.contains(needle)),
        "expected failure containing {needle:?}, got {:#?}",
        result.failures
    );
}

fn matching_inventory() -> inventory::Inventory {
    inventory::Inventory::from_manifest_text(
        "inventory.json",
        r#"{
          "schema_version": 1,
          "suite": "tests/trust-mc",
          "denominator": 2,
          "row_sha256": "cdbeb76c8e818eeead59b5f5127ff91e98175124dbabd0d81317461b1d547627",
          "rows": [
            {"file": "zani/example.rs", "harness": "proof_one", "expected": "PROOF", "lane": "tests/zani"},
            {"file": "zani/example.rs", "harness": "proof_two", "expected": "PROOF", "lane": "tests/zani"}
          ]
        }"#,
    )
    .expect("inventory fixture")
}

fn full_inventory() -> inventory::Inventory {
    inventory::Inventory::from_manifest_text(
        "tests/trust-mc/replacement-harness-inventory.json",
        FULL_INVENTORY,
    )
    .expect("full inventory fixture")
}

fn full_non_proof_closure_value() -> Value {
    let inventory: Value = serde_json::from_str(FULL_INVENTORY).expect("full inventory JSON");
    let rows = inventory
        .get("rows")
        .and_then(Value::as_array)
        .expect("inventory rows")
        .iter()
        .filter(|row| row.get("expected").and_then(Value::as_str) != Some("PROOF"))
        .map(|row| {
            let mut row = row.as_object().expect("inventory row object").clone();
            row.insert("disposition".to_string(), Value::String("closed".to_string()));
            row.insert(
                "justification".to_string(),
                Value::String("expected non-PROOF replacement outcome is tracked".to_string()),
            );
            row.insert("review_marker".to_string(), Value::String("reviewed".to_string()));
            Value::Object(row)
        })
        .collect::<Vec<_>>();

    Value::Object(Map::from_iter([
        ("schema_version".to_string(), Value::from(1)),
        ("suite".to_string(), Value::String("tests/trust-mc".to_string())),
        ("denominator".to_string(), Value::from(rows.len() as u64)),
        (
            "source".to_string(),
            Value::Object(Map::from_iter([
                (
                    "denominator".to_string(),
                    inventory.get("denominator").expect("inventory denominator").clone(),
                ),
                (
                    "row_sha256".to_string(),
                    inventory.get("row_sha256").expect("inventory row_sha256").clone(),
                ),
            ])),
        ),
        ("rows".to_string(), Value::Array(rows)),
    ]))
}

#[test]
fn accepts_clean_fixture() {
    let result = audit_fixture("clean.json", CLEAN);

    assert_eq!(result.failures, []);
    assert_eq!(result.totals, AuditTotals { reports: 1, harnesses: 2, pass: 2, xfail: 0 });
}

#[test]
fn rejects_stale_fixture_by_default() {
    let result = audit_fixture("stale.json", STALE);

    assert_failure_contains(&result, "not an accepted current status");
}

#[test]
fn rejects_nonzero_summary_buckets() {
    let result = audit_fixture("bad_summary.json", BAD_SUMMARY);

    assert_failure_contains(&result, "summary.fail is 1");
    assert_failure_contains(&result, "summary.unknown is 1");
    assert_failure_contains(&result, "summary.error is 1");
    assert_failure_contains(&result, "summary.bmc is 1");
    assert_failure_contains(&result, "summary.skip is 1");
}

#[test]
fn rejects_disallowed_harness_statuses() {
    let result = audit_fixture("bad_harness.json", BAD_HARNESS);

    assert_failure_contains(&result, "status FAIL is not PASS");
    assert_failure_contains(&result, "XFAIL for expected PROOF is not allowed");
}

#[test]
fn rejects_xfail_by_default() {
    let result = audit_fixture("xfail_non_proof.json", XFAIL_NON_PROOF);

    assert_failure_contains(&result, "XFAIL is not allowed in replacement mode");
}

#[test]
fn rejects_xfail_expected_proof_even_when_xfail_is_allowed() {
    let result = audit_fixture("bad_harness.json", BAD_HARNESS);

    assert_failure_contains(&result, "XFAIL for expected PROOF is not allowed");
}

#[test]
fn rejects_xfail_for_non_proof_expected_status() {
    let result = audit_fixture("xfail_non_proof.json", XFAIL_NON_PROOF);

    assert_failure_contains(&result, "XFAIL is not allowed in replacement mode");
}

#[test]
fn rejects_missing_summary_fail_field() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    value
        .get_mut("summary")
        .and_then(Value::as_object_mut)
        .expect("fixture summary is an object")
        .remove("fail");

    let result = audit_report_value("missing-fail.json", &value, AuditConfig::default());

    assert_failure_contains(&result, "missing summary.fail");
}

#[test]
fn rejects_missing_summary_pass_field() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    value
        .get_mut("summary")
        .and_then(Value::as_object_mut)
        .expect("fixture summary is an object")
        .remove("pass");

    let result = audit_report_value("missing-pass.json", &value, AuditConfig::default());

    assert_failure_contains(&result, "missing summary.pass");
}

#[test]
fn rejects_malformed_optional_pin() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    value
        .as_object_mut()
        .expect("fixture is an object")
        .insert("ay_pin".to_string(), Value::String("deadbeef".to_string()));

    let result = audit_report_value("bad-pin.json", &value, AuditConfig::default());

    assert_failure_contains(&result, "ay_pin \"deadbeef\"");
}

#[test]
fn rejects_invalid_static_report_metadata() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let report = value.as_object_mut().expect("fixture is an object");
    report.insert("schema_version".to_string(), Value::from(1));
    report.insert("report_status".to_string(), Value::String("historicalish".to_string()));
    report.insert("solver".to_string(), Value::String("z3".to_string()));
    report.insert("tree_state".to_string(), Value::String("dirty".to_string()));
    report.insert("tree_fingerprint".to_string(), Value::String("deadbeef".to_string()));
    report.insert("replacement_evidence".to_string(), Value::Bool(false));
    report.insert("commit".to_string(), Value::String("0123456".to_string()));
    report.insert("ay_pin".to_string(), Value::String("deadbeef".to_string()));

    let result = audit_report_value("bad-metadata.json", &value, AuditConfig::default());

    assert_failure_contains(&result, "schema_version 1 != 2");
    assert_failure_contains(&result, "report_status \"historicalish\"");
    assert_failure_contains(&result, "solver \"z3\" != \"ay\"");
    assert_failure_contains(&result, "tree_state \"dirty\" != \"clean\"");
    assert_failure_contains(&result, "tree_fingerprint \"deadbeef\"");
    assert_failure_contains(&result, "replacement_evidence false is not true");
    assert_failure_contains(&result, "commit \"0123456\"");
    assert_failure_contains(&result, "ay_pin \"deadbeef\"");
}

#[test]
fn rejects_missing_required_static_report_metadata() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let report = value.as_object_mut().expect("fixture is an object");
    for field in [
        "schema_version",
        "solver",
        "tree_state",
        "tree_fingerprint",
        "replacement_evidence",
        "commit",
        "ay_pin",
        "solver_binary",
    ] {
        report.remove(field);
    }

    let result = audit_report_value("missing-metadata.json", &value, AuditConfig::default());

    assert_failure_contains(&result, "missing schema_version");
    assert_failure_contains(&result, "missing solver");
    assert_failure_contains(&result, "missing tree_state");
    assert_failure_contains(&result, "missing tree_fingerprint");
    assert_failure_contains(&result, "missing replacement_evidence");
    assert_failure_contains(&result, "missing commit");
    assert_failure_contains(&result, "missing ay_pin");
    assert_failure_contains(&result, "solver_binary attestation is missing");
}

#[test]
fn rejects_expected_pin_mismatches_and_bad_expected_values() {
    let result = audit_report_text(
        "clean.json",
        CLEAN,
        AuditConfig {
            expected_commit: Some("f".repeat(40)),
            expected_ay_pin: Some("short".to_string()),
            expected_tree_fingerprint: Some("bad-tree".to_string()),
            ..AuditConfig::default()
        },
    );

    assert_failure_contains(&result, "commit \"0123456789abcdef0123456789abcdef01234567\"");
    assert_failure_contains(&result, "expected ay_pin \"short\"");
    assert_failure_contains(&result, "expected tree_fingerprint \"bad-tree\"");
}

#[test]
fn rejects_expected_tree_fingerprint_mismatch() {
    let result = audit_report_text(
        "clean.json",
        CLEAN,
        AuditConfig {
            expected_tree_fingerprint: Some(
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".to_string(),
            ),
            ..AuditConfig::default()
        },
    );

    assert_failure_contains(
        &result,
        "tree_fingerprint \"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\" != expected",
    );
}

#[test]
fn rejects_solver_binary_attestation_mismatch() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    value.as_object_mut().expect("fixture is an object").insert(
        "solver_binary".to_string(),
        Value::Object(Map::from_iter([
            ("name".to_string(), Value::String("z3".to_string())),
            ("path".to_string(), Value::String("".to_string())),
            ("version".to_string(), Value::String("".to_string())),
            ("commit".to_string(), Value::String("abcdef0".to_string())),
        ])),
    );

    let result = audit_report_value(
        "bad-solver-binary.json",
        &value,
        AuditConfig {
            expected_ay_pin: Some("90e42a0e32bcc178f4732a49679a92ba18a0fe65".to_string()),
            ..AuditConfig::default()
        },
    );

    assert_failure_contains(&result, "solver_binary.name \"z3\" != 'ay'");
    assert_failure_contains(&result, "solver_binary.path is missing or empty");
    assert_failure_contains(&result, "solver_binary.version is missing or empty");
    assert_failure_contains(&result, "solver_binary.commit \"abcdef0\" does not match expected");
}

#[test]
fn rejects_solver_binary_version_commit_mismatch() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let solver_binary = value
        .get_mut("solver_binary")
        .and_then(Value::as_object_mut)
        .expect("fixture solver_binary is an object");
    solver_binary.insert(
        "version".to_string(),
        Value::String(
            "ay 0.10.0+build.1.aaaaaaaaaaaa@2026-04-29T00:00:00Z\nbuild.commit=aaaaaaaaaaaa"
                .to_string(),
        ),
    );

    let result = audit_report_value(
        "stale-solver-version.json",
        &value,
        AuditConfig {
            expected_ay_pin: Some("90e42a0e32bcc178f4732a49679a92ba18a0fe65".to_string()),
            ..AuditConfig::default()
        },
    );

    assert_failure_contains(
        &result,
        "solver_binary.version commit \"aaaaaaaaaaaa\" != solver_binary.commit \"90e42a0\"",
    );
    assert_failure_contains(
        &result,
        "solver_binary.version commit \"aaaaaaaaaaaa\" does not match expected ay pin",
    );
}

#[test]
fn rejects_solver_binary_report_ay_pin_mismatch_without_expected_pin() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    value
        .as_object_mut()
        .expect("fixture is an object")
        .insert("ay_pin".to_string(), Value::String("a".repeat(40)));

    let result = audit_report_value("report-pin-mismatch.json", &value, AuditConfig::default());

    assert_failure_contains(
        &result,
        "solver_binary.commit \"90e42a0\" does not match report ay_pin",
    );
    assert_failure_contains(
        &result,
        "solver_binary.version commit \"90e42a0\" does not match report ay_pin",
    );
}

#[test]
fn rejects_solver_binary_version_without_embedded_commit() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let solver_binary = value
        .get_mut("solver_binary")
        .and_then(Value::as_object_mut)
        .expect("fixture solver_binary is an object");
    solver_binary.insert("version".to_string(), Value::String("ay 0.10.0".to_string()));

    let result = audit_report_value("missing-version-commit.json", &value, AuditConfig::default());

    assert_failure_contains(
        &result,
        "solver_binary.version does not include a 7- to 40-character hex build commit",
    );
}

#[test]
fn rejects_expected_harness_count_mismatch() {
    let result = audit_report_text(
        "clean.json",
        CLEAN,
        AuditConfig { expected_harnesses: Some(3), ..AuditConfig::default() },
    );

    assert_failure_contains(&result, "report has 2 harnesses; expected 3");
}

#[test]
fn accepts_matching_inventory() {
    let result = audit_report_text(
        "clean.json",
        CLEAN,
        AuditConfig {
            expected_harnesses: Some(2),
            inventory: Some(matching_inventory()),
            ..AuditConfig::default()
        },
    );

    assert_eq!(result.failures, []);
}

#[test]
fn rejects_inventory_backed_pass_ctrex_downgrade() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let summary = value
        .get_mut("summary")
        .and_then(Value::as_object_mut)
        .expect("fixture summary is an object");
    summary.insert("proof".to_string(), Value::from(1));
    summary.insert("trusted_proof".to_string(), Value::from(1));
    summary.insert("ctrex".to_string(), Value::from(1));

    let first = value
        .get_mut("harnesses")
        .and_then(Value::as_array_mut)
        .and_then(|harnesses| harnesses.first_mut())
        .and_then(Value::as_object_mut)
        .expect("fixture first harness is an object");
    first.insert("expected".to_string(), Value::String("CTREX".to_string()));
    first.insert("verdict".to_string(), Value::String("CTREX".to_string()));
    first.insert("trusted_proof".to_string(), Value::Bool(false));

    let result = audit_report_value(
        "inventory-ctrex-downgrade.json",
        &value,
        AuditConfig {
            expected_harnesses: Some(2),
            inventory: Some(matching_inventory()),
            ..AuditConfig::default()
        },
    );

    assert_failure_contains(
        &result,
        "report expected \"CTREX\" does not match inventory expected \"PROOF\"",
    );
    assert_failure_contains(
        &result,
        "inventory PROOF harness is not replacement-quality zani/example.rs::proof_one",
    );
}

#[test]
fn rejects_inventory_backed_non_pass_status() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let first = value
        .get_mut("harnesses")
        .and_then(Value::as_array_mut)
        .and_then(|harnesses| harnesses.first_mut())
        .and_then(Value::as_object_mut)
        .expect("fixture first harness is an object");
    first.insert("status".to_string(), Value::String("ERROR".to_string()));
    first.insert("trusted_proof".to_string(), Value::Bool(false));

    let result = audit_report_value(
        "inventory-non-pass.json",
        &value,
        AuditConfig { inventory: Some(matching_inventory()), ..AuditConfig::default() },
    );

    assert_failure_contains(&result, "harnesses[0].status ERROR is not PASS");
    assert_failure_contains(
        &result,
        "inventory PROOF harness is not replacement-quality zani/example.rs::proof_one",
    );
}

#[test]
fn accepts_inventory_non_proof_expected_value_after_parse() {
    let inventory = inventory::Inventory::from_manifest_text(
        "inventory.json",
        r#"{
          "schema_version": 1,
          "suite": "tests/trust-mc",
          "denominator": 1,
          "row_sha256": "b9d749a2871af85c2a2684aff4fcfe65ef313f2f5072b46017fe1bd70ba28b43",
          "rows": [
            {"file": "zani/example.rs", "harness": "ctrex_canary", "expected": "CTREX", "lane": "tests/zani"}
          ]
        }"#,
    )
    .expect("non-PROOF inventory row should parse");

    assert_eq!(inventory.denominator, 1);
}

#[test]
fn rejects_inventory_missing_required_metadata() {
    let result = inventory::Inventory::from_manifest_text(
        "inventory.json",
        r#"{
          "denominator": 0,
          "row_sha256": "4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e8c4ea2e036a2a2487d8b71",
          "rows": []
        }"#,
    );

    assert_eq!(
        result.expect_err("metadata must be strict"),
        "inventory.json: missing schema_version"
    );
}

#[test]
fn accepts_full_non_proof_closure_for_canonical_inventory() {
    let inventory = full_inventory();
    let closure = full_non_proof_closure_value();

    let failures = non_proof_closure::validate_non_proof_closure_value(
        "non-proof-closure.json",
        &closure,
        &inventory,
    );

    assert_eq!(failures, []);
}

#[test]
fn accepts_non_proof_closure_counts_derived_from_inventory() {
    let inventory = inventory::Inventory::from_manifest_text(
        "inventory.json",
        r#"{
          "schema_version": 1,
          "suite": "tests/trust-mc",
          "denominator": 1,
          "row_sha256": "b9d749a2871af85c2a2684aff4fcfe65ef313f2f5072b46017fe1bd70ba28b43",
          "rows": [
            {"file": "zani/example.rs", "harness": "ctrex_canary", "expected": "CTREX", "lane": "tests/zani"}
          ]
        }"#,
    )
    .expect("single-row inventory fixture");
    let closure = Value::Object(Map::from_iter([
        ("schema_version".to_string(), Value::from(1)),
        ("suite".to_string(), Value::String("tests/trust-mc".to_string())),
        ("denominator".to_string(), Value::from(1)),
        (
            "source".to_string(),
            Value::Object(Map::from_iter([
                ("denominator".to_string(), Value::from(1)),
                (
                    "row_sha256".to_string(),
                    Value::String(
                        "b9d749a2871af85c2a2684aff4fcfe65ef313f2f5072b46017fe1bd70ba28b43"
                            .to_string(),
                    ),
                ),
            ])),
        ),
        (
            "rows".to_string(),
            Value::Array(vec![Value::Object(Map::from_iter([
                ("file".to_string(), Value::String("zani/example.rs".to_string())),
                ("harness".to_string(), Value::String("ctrex_canary".to_string())),
                ("expected".to_string(), Value::String("CTREX".to_string())),
                ("disposition".to_string(), Value::String("closed".to_string())),
                (
                    "justification".to_string(),
                    Value::String("expected replacement counterexample".to_string()),
                ),
                ("review_marker".to_string(), Value::String("reviewed".to_string())),
            ]))]),
        ),
    ]));

    let failures = non_proof_closure::validate_non_proof_closure_value(
        "non-proof-closure.json",
        &closure,
        &inventory,
    );

    assert_eq!(failures, []);
}

#[test]
fn rejects_non_proof_closure_open_todo_state() {
    let inventory = full_inventory();
    let mut closure = full_non_proof_closure_value();
    let row = closure
        .get_mut("rows")
        .and_then(Value::as_array_mut)
        .and_then(|rows| rows.first_mut())
        .and_then(Value::as_object_mut)
        .expect("closure row object");
    row.insert("disposition".to_string(), Value::String("open".to_string()));
    row.insert("review_marker".to_string(), Value::String("TODO review".to_string()));

    let failures = non_proof_closure::validate_non_proof_closure_value(
        "non-proof-closure.json",
        &closure,
        &inventory,
    );
    let result = AuditResult { totals: AuditTotals::default(), failures };

    assert_failure_contains(&result, "rows[0].disposition must not contain open/todo marker");
    assert_failure_contains(&result, "rows[0].review_marker must not contain open/todo marker");
}

#[test]
fn rejects_non_proof_closure_missing_review_marker_and_row() {
    let inventory = full_inventory();
    let mut closure = full_non_proof_closure_value();
    let rows = closure.get_mut("rows").and_then(Value::as_array_mut).expect("closure rows");
    let expected_rows = rows.len();
    rows.remove(0);
    rows[0]
        .as_object_mut()
        .expect("closure row object")
        .insert("review_marker".to_string(), Value::String("".to_string()));

    let failures = non_proof_closure::validate_non_proof_closure_value(
        "non-proof-closure.json",
        &closure,
        &inventory,
    );
    let result = AuditResult { totals: AuditTotals::default(), failures };

    assert_failure_contains(
        &result,
        &format!("rows has {} entries; expected {}", expected_rows - 1, expected_rows),
    );
    assert_failure_contains(&result, "missing non-PROOF closure row");
    assert_failure_contains(&result, "rows[0].review_marker is empty");
}

#[test]
fn rejects_non_proof_closure_source_pin_mismatch() {
    let inventory = full_inventory();
    let mut closure = full_non_proof_closure_value();
    closure["source"]["row_sha256"] = Value::String(
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".to_string(),
    );

    let failures = non_proof_closure::validate_non_proof_closure_value(
        "non-proof-closure.json",
        &closure,
        &inventory,
    );
    let result = AuditResult { totals: AuditTotals::default(), failures };

    assert_failure_contains(&result, "source.row_sha256");
}

#[test]
fn rejects_inventory_row_sha256_mismatch() {
    let result = inventory::Inventory::from_manifest_text(
        "inventory.json",
        r#"{
          "schema_version": 1,
          "suite": "tests/trust-mc",
          "denominator": 1,
          "row_sha256": "0000000000000000000000000000000000000000000000000000000000000000",
          "rows": [
            {"file": "zani/example.rs", "harness": "proof_one", "expected": "PROOF", "lane": "tests/zani"}
          ]
        }"#,
    );

    assert!(result.expect_err("bad digest should be rejected").contains(
        "row_sha256 0000000000000000000000000000000000000000000000000000000000000000 != computed"
    ),);
}

#[test]
fn rejects_inventory_backed_untrusted_proof_row() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let summary = value
        .get_mut("summary")
        .and_then(Value::as_object_mut)
        .expect("fixture summary is an object");
    summary.insert("trusted_proof".to_string(), Value::from(1));

    let first = value
        .get_mut("harnesses")
        .and_then(Value::as_array_mut)
        .and_then(|harnesses| harnesses.first_mut())
        .and_then(Value::as_object_mut)
        .expect("fixture first harness is an object");
    first.insert("trusted_proof".to_string(), Value::Bool(false));

    let result = audit_report_value(
        "inventory-untrusted-proof.json",
        &value,
        AuditConfig {
            expected_harnesses: Some(2),
            inventory: Some(matching_inventory()),
            ..AuditConfig::default()
        },
    );

    assert_failure_contains(&result, "harnesses[0].trusted_proof false disagrees");
    assert_failure_contains(&result, "harnesses[0].trusted_proof false != true");
}

#[test]
fn rejects_inventory_membership_mismatch() {
    let inventory = inventory::Inventory::from_manifest_text(
        "inventory.json",
        r#"{
          "schema_version": 1,
          "suite": "tests/trust-mc",
          "denominator": 2,
          "row_sha256": "079dd58ef4730a1c02a7e16ae80ffb27f4eddea1a2fe04620e220746bc527ebd",
          "rows": [
            {"file": "zani/example.rs", "harness": "proof_one", "expected": "PROOF", "lane": "tests/zani"},
            {"file": "zani/missing.rs", "harness": "proof_missing", "expected": "PROOF", "lane": "tests/zani"}
          ]
        }"#,
    )
    .expect("inventory fixture");

    let result = audit_report_text(
        "clean.json",
        CLEAN,
        AuditConfig { inventory: Some(inventory), ..AuditConfig::default() },
    );

    assert_failure_contains(&result, "missing inventory harness zani/missing.rs::proof_missing");
    assert_failure_contains(&result, "report harness not in inventory zani/example.rs::proof_two");
}

#[test]
fn rejects_duplicate_harness_keys() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let harnesses =
        value.get_mut("harnesses").and_then(Value::as_array_mut).expect("fixture harnesses");
    harnesses[1]["harness"] = Value::String("proof_one".to_string());
    let result = audit_report_value("duplicate.json", &value, AuditConfig::default());

    assert_failure_contains(&result, "duplicates harness key zani/example.rs::proof_one");
}

#[test]
fn rejects_pass_status_when_expected_and_verdict_disagree() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let summary = value
        .get_mut("summary")
        .and_then(Value::as_object_mut)
        .expect("fixture summary is an object");
    summary.insert("proof".to_string(), Value::from(1));
    summary.insert("trusted_proof".to_string(), Value::from(1));
    summary.insert("ctrex".to_string(), Value::from(1));

    let first = value
        .get_mut("harnesses")
        .and_then(Value::as_array_mut)
        .and_then(|harnesses| harnesses.first_mut())
        .and_then(Value::as_object_mut)
        .expect("fixture first harness is an object");
    first.insert("verdict".to_string(), Value::String("CTREX".to_string()));
    first.insert("trusted_proof".to_string(), Value::Bool(false));

    let result = audit_report_value("pass-disagrees.json", &value, AuditConfig::default());

    assert_failure_contains(
        &result,
        "harnesses[0].expected \"PROOF\" does not match verdict \"CTREX\"",
    );
}

#[test]
fn rejects_fail_status_when_expected_and_verdict_match() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let summary = value
        .get_mut("summary")
        .and_then(Value::as_object_mut)
        .expect("fixture summary is an object");
    summary.insert("pass".to_string(), Value::from(1));
    summary.insert("trusted_proof".to_string(), Value::from(1));
    summary.insert("fail".to_string(), Value::from(1));

    let first = value
        .get_mut("harnesses")
        .and_then(Value::as_array_mut)
        .and_then(|harnesses| harnesses.first_mut())
        .and_then(Value::as_object_mut)
        .expect("fixture first harness is an object");
    first.insert("status".to_string(), Value::String("FAIL".to_string()));
    first.insert("trusted_proof".to_string(), Value::Bool(false));

    let result = audit_report_value("fail-agrees.json", &value, AuditConfig::default());

    assert_failure_contains(
        &result,
        "harnesses[0].status FAIL disagrees with matching expected/verdict \"PROOF\"",
    );
    assert_failure_contains(&result, "harnesses[0].status FAIL is not PASS");
}

#[test]
fn rejects_unsound_static_harness_metadata() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let first = value
        .get_mut("harnesses")
        .and_then(Value::as_array_mut)
        .and_then(|harnesses| harnesses.first_mut())
        .and_then(Value::as_object_mut)
        .expect("fixture first harness is an object");
    first.insert("verdict".to_string(), Value::String("BMC".to_string()));
    first.insert("proof_qualifiers".to_string(), Value::String("sound_fallback".to_string()));
    first.insert("sound_fallback_count".to_string(), Value::from(2));
    first.insert(
        "demotion_reasons".to_string(),
        Value::Array(vec![Value::String("fallback=1".to_string())]),
    );
    first.insert(
        "translation_drop_reasons".to_string(),
        Value::Object(Map::from_iter([("drop".to_string(), Value::from(1))])),
    );
    first.insert("retried".to_string(), Value::Bool(false));
    first.insert("retry_relation_count".to_string(), Value::from(0));

    let result = audit_report_value("bad-harness-metadata.json", &value, AuditConfig::default());

    assert_failure_contains(&result, "verdict \"BMC\"");
    assert_failure_contains(&result, "proof_qualifiers \"sound_fallback\" is not clean");
    assert_failure_contains(&result, "sound_fallback_count is 2");
    assert_failure_contains(&result, "demotion_reasons is not empty");
    assert_failure_contains(&result, "translation_drop_reasons is not empty");
    assert_failure_contains(&result, "retried present");
    assert_failure_contains(&result, "retry_relation_count present");
}

#[test]
fn rejects_trivial_safe_no_error_rule_proof_qualifier() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let first = value
        .get_mut("harnesses")
        .and_then(Value::as_array_mut)
        .and_then(|harnesses| harnesses.first_mut())
        .and_then(Value::as_object_mut)
        .expect("fixture first harness is an object");
    first.insert(
        "proof_qualifiers".to_string(),
        Value::String("trivial_safe=no_error_rule".to_string()),
    );

    let result =
        audit_report_value("trivial-safe-no-error-rule.json", &value, AuditConfig::default());

    assert_failure_contains(&result, "proof_qualifiers \"trivial_safe=no_error_rule\"");
    assert_failure_contains(&result, "no-error-rule evidence, not replacement-quality");
}

#[test]
fn rejects_pass_harness_missing_static_proof_metadata() {
    let mut value: Value = serde_json::from_str(CLEAN).expect("fixture is valid JSON");
    let first = value
        .get_mut("harnesses")
        .and_then(Value::as_array_mut)
        .and_then(|harnesses| harnesses.first_mut())
        .and_then(Value::as_object_mut)
        .expect("fixture first harness is an object");
    for field in [
        "execution_state",
        "execution_details",
        "proof_qualifiers",
        "trusted_proof",
        "sound_fallback_count",
    ] {
        first.remove(field);
    }

    let result =
        audit_report_value("missing-harness-metadata.json", &value, AuditConfig::default());

    assert_failure_contains(&result, "harnesses[0].execution_state is missing");
    assert_failure_contains(&result, "harnesses[0].execution_details is missing");
    assert_failure_contains(&result, "harnesses[0].proof_qualifiers is missing");
    assert_failure_contains(&result, "harnesses[0].trusted_proof is missing");
    assert_failure_contains(&result, "harnesses[0].sound_fallback_count is missing");
}

#[test]
fn rejects_bad_metadata_fixture() {
    let result = audit_fixture("bad_metadata.json", BAD_METADATA);

    assert_failure_contains(&result, "schema_version 1 != 2");
    assert_failure_contains(&result, "report_status \"stale-but-not-declared\"");
    assert_failure_contains(&result, "solver \"z3\" != \"ay\"");
    assert_failure_contains(&result, "tree_state \"dirty\" != \"clean\"");
    assert_failure_contains(&result, "replacement_evidence false is not true");
    assert_failure_contains(&result, "solver_binary.name \"z3\" != 'ay'");
    assert_failure_contains(&result, "solver_binary.path is missing or empty");
    assert_failure_contains(&result, "solver_binary.version is missing or empty");
    assert_failure_contains(&result, "solver_binary.commit \"bad\"");
}

#[test]
fn rejects_bad_proof_row_fixture() {
    let result = audit_fixture("bad_proof_row.json", BAD_PROOF_ROW);

    assert_failure_contains(&result, "execution_state \"gated\" != \"complete\"");
    assert_failure_contains(&result, "execution_details \"final_marker=UNKNOWN\"");
    assert_failure_contains(&result, "proof_qualifiers \"sound_fallback=legacy\"");
    assert_failure_contains(&result, "sound_fallback_count is 3");
    assert_failure_contains(&result, "trusted_proof false != true");
    assert_failure_contains(&result, "known_fp true is not replacement-quality evidence");
    assert_failure_contains(&result, "demotion_reasons is not empty");
    assert_failure_contains(&result, "translation_drop_reasons is not empty");
    assert_failure_contains(&result, "retried present");
}

#[test]
fn rejects_summary_that_disagrees_with_rows() {
    let result = audit_fixture("bad_summary_rows.json", BAD_SUMMARY_ROWS);

    assert_failure_contains(&result, "summary.total is 2, expected 1 from rows");
    assert_failure_contains(&result, "summary.pass is 1, expected 0 from rows");
    assert_failure_contains(&result, "summary.fail is 0, expected 1 from rows");
    assert_failure_contains(&result, "summary.error is 0, expected 1 from rows");
    assert_failure_contains(&result, "status FAIL is not PASS");
}

#[test]
fn merges_report_totals() {
    let mut combined = AuditResult::default();
    combined.merge(audit_fixture("clean.json", CLEAN));
    combined.merge(audit_fixture("xfail_non_proof.json", XFAIL_NON_PROOF));

    assert_failure_contains(&combined, "XFAIL is not allowed in replacement mode");
    assert_eq!(combined.totals.reports, 2);
    assert_eq!(combined.totals.harnesses, 3);
    assert_eq!(combined.totals.pass, 2);
    assert_eq!(combined.totals.xfail, 1);
}
