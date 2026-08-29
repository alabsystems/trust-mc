// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::authority::{ExpectedAuthority, ProgressAuthority};
use crate::metadata::validate_solver_binary_attestation;
use serde_json::{Map, Value};

pub(super) fn authority_metadata_failures(
    report: &Map<String, Value>,
    authority: &ProgressAuthority,
) -> Vec<String> {
    let mut failures = Vec::new();
    require_number(report, "schema_version", 2, &mut failures);
    require_string(report, "report_status", "current", &mut failures);
    require_string(report, "solver", "ay", &mut failures);
    require_string(report, "tree_state", "clean", &mut failures);
    if report.get("replacement_evidence").and_then(Value::as_bool) != Some(true) {
        failures.push(format!(
            "replacement_evidence {} is not true",
            value_label(report.get("replacement_evidence"))
        ));
    }
    require_hex_string(report, "commit", 40, &mut failures);
    require_hex_string(report, "ay_pin", 40, &mut failures);
    require_hex_string(report, "tree_fingerprint", 64, &mut failures);
    require_expected_value(report, "commit", &authority.expected_commit, &mut failures);
    require_expected_value(report, "ay_pin", &authority.expected_ay_pin, &mut failures);
    if authority.expected_tree_fingerprint.value.is_some() {
        require_expected_value(
            report,
            "tree_fingerprint",
            &authority.expected_tree_fingerprint,
            &mut failures,
        );
    }
    let mut solver_failures = Vec::new();
    validate_solver_binary_attestation(
        "report",
        report,
        authority.expected_ay_pin.value.as_deref(),
        &mut solver_failures,
    );
    failures.extend(solver_failures.into_iter().map(|failure| failure.message));
    failures
}

pub(super) fn top_string(report: &Map<String, Value>, field: &str) -> String {
    report.get(field).and_then(Value::as_str).unwrap_or("missing").to_string()
}

fn require_expected_value(
    report: &Map<String, Value>,
    field: &str,
    expected: &ExpectedAuthority,
    failures: &mut Vec<String>,
) {
    let Some(expected_value) = expected.value.as_deref() else {
        failures.push(format!(
            "expected {field} unavailable; pass {} or run from a checkout where it can be derived",
            expected_flag(field)
        ));
        return;
    };
    if report.get(field).and_then(Value::as_str) != Some(expected_value) {
        failures.push(format!(
            "{field} {} != expected {expected_value:?} ({})",
            value_label(report.get(field)),
            expected.source
        ));
    }
}

fn expected_flag(field: &str) -> &'static str {
    match field {
        "commit" => "--expected-commit",
        "ay_pin" => "--expected-ay-pin",
        "tree_fingerprint" => "--expected-tree-fingerprint",
        _ => "--expected-*",
    }
}

fn require_number(
    report: &Map<String, Value>,
    field: &str,
    expected: u64,
    failures: &mut Vec<String>,
) {
    if report.get(field).and_then(Value::as_u64) != Some(expected) {
        failures.push(format!(
            "{field} {} != {expected}; legacy or missing schema-v2 proof evidence does not count",
            value_label(report.get(field))
        ));
    }
}

fn require_string(
    report: &Map<String, Value>,
    field: &str,
    expected: &str,
    failures: &mut Vec<String>,
) {
    if report.get(field).and_then(Value::as_str) != Some(expected) {
        failures.push(format!("{field} {} != {expected:?}", value_label(report.get(field))));
    }
}

fn require_hex_string(
    report: &Map<String, Value>,
    field: &str,
    len: usize,
    failures: &mut Vec<String>,
) {
    if !has_hex_string(report, field, len) {
        failures.push(format!(
            "{field} {} is not a {len}-character hex value",
            value_label(report.get(field))
        ));
    }
}

fn value_label(value: Option<&Value>) -> String {
    match value {
        Some(Value::String(value)) => format!("{value:?}"),
        Some(value) => value.to_string(),
        None => "missing".to_string(),
    }
}

fn has_hex_string(report: &Map<String, Value>, field: &str, len: usize) -> bool {
    report.get(field).and_then(Value::as_str).is_some_and(|value| {
        value.len() == len && value.bytes().all(|byte| byte.is_ascii_hexdigit())
    })
}
