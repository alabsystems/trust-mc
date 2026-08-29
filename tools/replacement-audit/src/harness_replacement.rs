// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::proof_quality::{proof_qualifier_failure_message, proof_qualifier_non_quality_reason};
use crate::{AuditFailure, json_type};
use serde_json::{Map, Value};

pub(crate) fn validate_static_replacement_metadata(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    failures: &mut Vec<AuditFailure>,
) {
    validate_optional_verdict(path, label, row, failures);
    validate_optional_proof_qualifiers(path, label, row, failures);
    validate_optional_sound_fallback_count(path, label, row, failures);
    validate_optional_empty_array(path, label, row, "demotion_reasons", failures);
    validate_optional_empty_object(path, label, row, "translation_drop_reasons", failures);

    for field in [
        "retried",
        "retry_attempts",
        "retry_resolved_by",
        "retry_final",
        "retry_recursive",
        "retry_relation_count",
    ] {
        if row.contains_key(field) {
            failures.push(AuditFailure::new(path, format!("{label}.{field} present")));
        }
    }
}

pub(crate) fn validate_pass_row(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    verdict: Option<&str>,
    failures: &mut Vec<AuditFailure>,
) {
    match verdict {
        Some("PROOF") => validate_required_replacement_proof_row(path, label, row, failures),
        Some("CTREX" | "UNKNOWN" | "ERROR" | "SKIP" | "BMC") => failures.push(AuditFailure::new(
            path,
            format!("{label}.verdict {verdict:?} is not replacement-quality PROOF"),
        )),
        Some(_) | None => {}
    }
}

fn validate_required_replacement_proof_row(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    failures: &mut Vec<AuditFailure>,
) {
    validate_required_harness_string_value(path, label, row, "expected", "PROOF", failures);
    validate_required_harness_string_value(path, label, row, "verdict", "PROOF", failures);
    validate_required_harness_string_value(
        path,
        label,
        row,
        "execution_state",
        "complete",
        failures,
    );
    validate_required_harness_string_value(
        path,
        label,
        row,
        "execution_details",
        "final_marker=PROOF",
        failures,
    );

    if !row.contains_key("proof_qualifiers") {
        failures.push(AuditFailure::new(path, format!("{label}.proof_qualifiers is missing")));
    }
    validate_required_harness_bool_value(path, label, row, "trusted_proof", true, failures);
    validate_optional_known_fp_not_true(path, label, row, failures);
    validate_required_sound_fallback_count(path, label, row, failures);
}

fn validate_required_harness_string_value(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    field: &str,
    expected: &str,
    failures: &mut Vec<AuditFailure>,
) {
    let Some(value) = row.get(field) else {
        failures.push(AuditFailure::new(path, format!("{label}.{field} is missing")));
        return;
    };

    match value {
        Value::String(actual) if actual == expected => {}
        Value::String(actual) => failures
            .push(AuditFailure::new(path, format!("{label}.{field} {actual:?} != {expected:?}"))),
        other => failures.push(AuditFailure::new(
            path,
            format!("{label}.{field} must be a string, got {}", json_type(other)),
        )),
    }
}

fn validate_required_harness_bool_value(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    field: &str,
    expected: bool,
    failures: &mut Vec<AuditFailure>,
) {
    let Some(value) = row.get(field) else {
        failures.push(AuditFailure::new(path, format!("{label}.{field} is missing")));
        return;
    };

    match value {
        Value::Bool(actual) if *actual == expected => {}
        Value::Bool(actual) => failures
            .push(AuditFailure::new(path, format!("{label}.{field} {actual} != {expected}"))),
        other => failures.push(AuditFailure::new(
            path,
            format!("{label}.{field} must be a bool, got {}", json_type(other)),
        )),
    }
}

fn validate_optional_known_fp_not_true(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    failures: &mut Vec<AuditFailure>,
) {
    match row.get("known_fp") {
        Some(Value::Bool(false)) | None => {}
        Some(Value::Bool(true)) => failures.push(AuditFailure::new(
            path,
            format!("{label}.known_fp true is not replacement-quality evidence"),
        )),
        Some(other) => failures.push(AuditFailure::new(
            path,
            format!("{label}.known_fp must be a bool, got {}", json_type(other)),
        )),
    }
}

fn validate_optional_verdict(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    failures: &mut Vec<AuditFailure>,
) {
    let Some(value) = row.get("verdict") else {
        return;
    };

    match value {
        Value::String(verdict)
            if matches!(verdict.as_str(), "BMC" | "UNKNOWN" | "ERROR" | "SKIP" | "XFAIL") =>
        {
            failures.push(AuditFailure::new(
                path,
                format!("{label}.verdict {verdict:?} is not replacement-quality evidence"),
            ))
        }
        Value::String(_) => {}
        other => failures.push(AuditFailure::new(
            path,
            format!("{label}.verdict must be a string, got {}", json_type(other)),
        )),
    }
}

fn validate_optional_proof_qualifiers(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    failures: &mut Vec<AuditFailure>,
) {
    let Some(value) = row.get("proof_qualifiers") else {
        return;
    };

    match value {
        Value::String(qualifiers) if proof_qualifier_non_quality_reason(qualifiers).is_none() => {}
        Value::String(qualifiers) => failures.push(AuditFailure::new(
            path,
            format!("{label}.proof_qualifiers {}", proof_qualifier_failure_message(qualifiers)),
        )),
        other => failures.push(AuditFailure::new(
            path,
            format!("{label}.proof_qualifiers must be a string, got {}", json_type(other)),
        )),
    }
}

fn validate_required_sound_fallback_count(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    failures: &mut Vec<AuditFailure>,
) {
    if !row.contains_key("sound_fallback_count") {
        failures.push(AuditFailure::new(path, format!("{label}.sound_fallback_count is missing")));
        return;
    }
    validate_optional_sound_fallback_count(path, label, row, failures);
}

fn validate_optional_sound_fallback_count(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    failures: &mut Vec<AuditFailure>,
) {
    let Some(value) = row.get("sound_fallback_count") else {
        return;
    };

    match value.as_u64() {
        Some(0) => {}
        Some(count) => failures.push(AuditFailure::new(
            path,
            format!("{label}.sound_fallback_count is {count}, expected 0"),
        )),
        None => failures.push(AuditFailure::new(
            path,
            format!(
                "{label}.sound_fallback_count must be an unsigned integer, got {}",
                json_type(value)
            ),
        )),
    }
}

fn validate_optional_empty_array(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    field: &str,
    failures: &mut Vec<AuditFailure>,
) {
    match row.get(field) {
        Some(Value::Array(values)) if values.is_empty() => {}
        Some(Value::Array(_)) => {
            failures.push(AuditFailure::new(path, format!("{label}.{field} is not empty")))
        }
        Some(other) => failures.push(AuditFailure::new(
            path,
            format!("{label}.{field} must be an array, got {}", json_type(other)),
        )),
        None => {}
    }
}

fn validate_optional_empty_object(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    field: &str,
    failures: &mut Vec<AuditFailure>,
) {
    match row.get(field) {
        Some(Value::Object(values)) if values.is_empty() => {}
        Some(Value::Object(_)) => {
            failures.push(AuditFailure::new(path, format!("{label}.{field} is not empty")))
        }
        Some(other) => failures.push(AuditFailure::new(
            path,
            format!("{label}.{field} must be an object, got {}", json_type(other)),
        )),
        None => {}
    }
}
