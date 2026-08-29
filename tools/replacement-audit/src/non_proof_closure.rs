// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::inventory::{HarnessKey, Inventory};
use crate::{AuditFailure, json_type};
use serde_json::{Map, Value};
use std::collections::{BTreeMap, BTreeSet};

pub fn validate_non_proof_closure_text(
    path: &str,
    text: &str,
    inventory: &Inventory,
) -> Vec<AuditFailure> {
    match serde_json::from_str::<Value>(text) {
        Ok(value) => validate_non_proof_closure_value(path, &value, inventory),
        Err(err) => vec![AuditFailure::new(path, format!("invalid JSON: {err}"))],
    }
}

pub fn validate_non_proof_closure_value(
    path: &str,
    value: &Value,
    inventory: &Inventory,
) -> Vec<AuditFailure> {
    let Some(closure) = value.as_object() else {
        return vec![AuditFailure::new(path, "expected top-level JSON object")];
    };

    let mut failures = Vec::new();

    let inventory_expected_by_key = inventory.non_proof_expected_by_key();
    let expected_non_proof_denominator = inventory_expected_by_key.len() as u64;
    validate_header(path, closure, inventory, expected_non_proof_denominator, &mut failures);

    let closure_expected_by_key =
        validate_rows(path, closure, expected_non_proof_denominator, &mut failures);
    validate_key_set(path, &inventory_expected_by_key, &closure_expected_by_key, &mut failures);
    validate_expected_counts(
        path,
        &inventory_expected_by_key,
        &closure_expected_by_key,
        &mut failures,
    );
    failures
}

fn validate_header(
    path: &str,
    closure: &Map<String, Value>,
    inventory: &Inventory,
    expected_non_proof_denominator: u64,
    failures: &mut Vec<AuditFailure>,
) {
    match closure.get("schema_version") {
        Some(Value::Number(version)) if version.as_u64() == Some(1) => {}
        Some(other) => failures.push(AuditFailure::new(
            path,
            format!("schema_version must be 1, got {}", json_type(other)),
        )),
        None => failures.push(AuditFailure::new(path, "missing schema_version")),
    }

    match closure.get("suite") {
        Some(Value::String(suite)) if suite == "tests/trust-mc" => {}
        Some(Value::String(suite)) => {
            failures
                .push(AuditFailure::new(path, format!("suite {suite:?} != \"tests/trust-mc\"")));
        }
        Some(other) => failures.push(AuditFailure::new(
            path,
            format!("suite must be a string, got {}", json_type(other)),
        )),
        None => failures.push(AuditFailure::new(path, "missing suite")),
    }

    match closure.get("denominator").and_then(Value::as_u64) {
        Some(actual) if actual == expected_non_proof_denominator => {}
        Some(actual) => failures.push(AuditFailure::new(
            path,
            format!("denominator {actual} != expected {expected_non_proof_denominator}"),
        )),
        None => failures.push(AuditFailure::new(path, "denominator must be an unsigned integer")),
    }

    let Some(source) = closure.get("source").and_then(Value::as_object) else {
        failures.push(AuditFailure::new(path, "source must be an object"));
        return;
    };
    match source.get("denominator").and_then(Value::as_u64) {
        Some(actual) if actual == inventory.denominator => {}
        Some(actual) => failures.push(AuditFailure::new(
            path,
            format!(
                "source.denominator {actual} != inventory denominator {}",
                inventory.denominator
            ),
        )),
        None => {
            failures.push(AuditFailure::new(path, "source.denominator must be an unsigned integer"))
        }
    }
    match source.get("row_sha256").and_then(Value::as_str) {
        Some(actual) if actual == inventory.row_sha256 => {}
        Some(actual) => failures.push(AuditFailure::new(
            path,
            format!("source.row_sha256 {actual} != inventory row_sha256 {}", inventory.row_sha256),
        )),
        None => {
            failures.push(AuditFailure::new(path, "source.row_sha256 must be a string"));
        }
    }
}

fn validate_rows(
    path: &str,
    closure: &Map<String, Value>,
    expected_non_proof_denominator: u64,
    failures: &mut Vec<AuditFailure>,
) -> BTreeMap<HarnessKey, String> {
    let Some(rows) = closure.get("rows") else {
        failures.push(AuditFailure::new(path, "missing rows"));
        return BTreeMap::new();
    };
    let Some(rows) = rows.as_array() else {
        failures.push(AuditFailure::new(
            path,
            format!("rows must be an array, got {}", json_type(rows)),
        ));
        return BTreeMap::new();
    };

    if rows.len() as u64 != expected_non_proof_denominator {
        failures.push(AuditFailure::new(
            path,
            format!("rows has {} entries; expected {expected_non_proof_denominator}", rows.len()),
        ));
    }

    let mut expected_by_key = BTreeMap::new();
    for (index, row) in rows.iter().enumerate() {
        validate_row(path, index, row, &mut expected_by_key, failures);
    }
    expected_by_key
}

fn validate_row(
    path: &str,
    index: usize,
    row: &Value,
    expected_by_key: &mut BTreeMap<HarnessKey, String>,
    failures: &mut Vec<AuditFailure>,
) {
    let label = format!("rows[{index}]");
    let Some(row) = row.as_object() else {
        failures.push(AuditFailure::new(
            path,
            format!("{label} must be an object, got {}", json_type(row)),
        ));
        return;
    };

    let file = required_nonempty_string(path, &label, row, "file", failures);
    let harness = required_nonempty_string(path, &label, row, "harness", failures);
    let expected = required_nonempty_string(path, &label, row, "expected", failures);
    let disposition = required_nonempty_string(path, &label, row, "disposition", failures);
    let _justification = required_nonempty_string(path, &label, row, "justification", failures);
    let review_marker = required_nonempty_string(path, &label, row, "review_marker", failures);

    if let Some(disposition) = disposition {
        validate_disposition(path, &label, &disposition, failures);
    }
    if let Some(review_marker) = review_marker {
        validate_review_marker(path, &label, &review_marker, failures);
    }
    let Some(expected) = expected else {
        return;
    };
    if expected == "PROOF" {
        failures.push(AuditFailure::new(path, format!("{label}.expected must not be \"PROOF\"")));
    }
    if !matches!(expected.as_str(), "CTREX" | "UNKNOWN" | "BMC_SAFE" | "ERROR") {
        failures.push(AuditFailure::new(
            path,
            format!("{label}.expected {expected:?} is not an accepted non-PROOF expected value"),
        ));
    }

    if let (Some(file), Some(harness)) = (file, harness) {
        let key = HarnessKey::new(file, harness);
        if expected_by_key.insert(key.clone(), expected).is_some() {
            failures.push(AuditFailure::new(
                path,
                format!("{label} duplicates closure row {}", key.label()),
            ));
        }
    }
}

fn validate_disposition(
    path: &str,
    label: &str,
    disposition: &str,
    failures: &mut Vec<AuditFailure>,
) {
    let normalized = disposition.trim().to_ascii_lowercase();
    if normalized.contains("todo") || normalized.contains("open") {
        failures.push(AuditFailure::new(
            path,
            format!("{label}.disposition must not contain open/todo marker"),
        ));
    }
}

fn validate_review_marker(
    path: &str,
    label: &str,
    review_marker: &str,
    failures: &mut Vec<AuditFailure>,
) {
    let normalized = review_marker.trim().to_ascii_lowercase();
    if normalized.contains("todo") || normalized.contains("open") {
        failures.push(AuditFailure::new(
            path,
            format!("{label}.review_marker must not contain open/todo marker"),
        ));
    }
}

fn validate_key_set(
    path: &str,
    inventory_expected_by_key: &BTreeMap<HarnessKey, String>,
    closure_expected_by_key: &BTreeMap<HarnessKey, String>,
    failures: &mut Vec<AuditFailure>,
) {
    let inventory_keys = inventory_expected_by_key.keys().cloned().collect::<BTreeSet<_>>();
    let closure_keys = closure_expected_by_key.keys().cloned().collect::<BTreeSet<_>>();

    for key in inventory_keys.difference(&closure_keys).take(20) {
        failures.push(AuditFailure::new(
            path,
            format!("missing non-PROOF closure row {}", key.label()),
        ));
    }
    for key in closure_keys.difference(&inventory_keys).take(20) {
        failures.push(AuditFailure::new(
            path,
            format!("closure row not in inventory non-PROOF set {}", key.label()),
        ));
    }
    for (key, expected) in inventory_expected_by_key {
        if let Some(actual) = closure_expected_by_key.get(key)
            && actual != expected
        {
            failures.push(AuditFailure::new(
                path,
                format!(
                    "closure expected {actual:?} does not match inventory expected {expected:?} for {}",
                    key.label()
                ),
            ));
        }
    }
}

fn validate_expected_counts(
    path: &str,
    inventory_expected_by_key: &BTreeMap<HarnessKey, String>,
    expected_by_key: &BTreeMap<HarnessKey, String>,
    failures: &mut Vec<AuditFailure>,
) {
    let mut inventory_counts = BTreeMap::<&str, u64>::new();
    for expected in inventory_expected_by_key.values() {
        *inventory_counts.entry(expected.as_str()).or_default() += 1;
    }

    let mut counts = BTreeMap::<&str, u64>::new();
    for expected in expected_by_key.values() {
        *counts.entry(expected.as_str()).or_default() += 1;
    }

    for name in ["CTREX", "UNKNOWN", "BMC_SAFE", "ERROR"] {
        let expected = inventory_counts.get(name).copied().unwrap_or(0);
        let actual = counts.get(name).copied().unwrap_or(0);
        if actual != expected {
            failures.push(AuditFailure::new(
                path,
                format!("counts.{name} {actual} != expected {expected}"),
            ));
        }
    }
}

fn required_nonempty_string(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    field: &str,
    failures: &mut Vec<AuditFailure>,
) -> Option<String> {
    match row.get(field) {
        Some(Value::String(value)) if !value.trim().is_empty() => Some(value.clone()),
        Some(Value::String(_)) => {
            failures.push(AuditFailure::new(path, format!("{label}.{field} is empty")));
            None
        }
        Some(other) => {
            failures.push(AuditFailure::new(
                path,
                format!("{label}.{field} must be a string, got {}", json_type(other)),
            ));
            None
        }
        None => {
            failures.push(AuditFailure::new(path, format!("{label}.{field} is missing")));
            None
        }
    }
}
