// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::{AuditConfig, AuditFailure, json_type};
use serde_json::{Map, Value};

pub(crate) fn validate_schema_version(
    path: &str,
    report: &Map<String, Value>,
    failures: &mut Vec<AuditFailure>,
) {
    match report.get("schema_version") {
        Some(Value::Number(version)) if version.as_u64() == Some(2) => {}
        Some(Value::Number(version)) => {
            failures.push(AuditFailure::new(path, format!("schema_version {version} != 2")))
        }
        Some(other) => failures.push(AuditFailure::new(
            path,
            format!("schema_version must be an unsigned integer, got {}", json_type(other)),
        )),
        None => failures.push(AuditFailure::new(path, "missing schema_version")),
    }
}

pub(crate) fn validate_report_status(
    path: &str,
    report: &Map<String, Value>,
    _config: &AuditConfig,
    failures: &mut Vec<AuditFailure>,
) {
    match report.get("report_status") {
        Some(Value::String(status)) if status.trim().is_empty() => {
            failures.push(AuditFailure::new(path, "report_status is empty"));
        }
        Some(Value::String(status)) if status == "current" => {}
        Some(Value::String(status)) => failures.push(AuditFailure::new(
            path,
            format!("report_status {status:?} is not an accepted current status"),
        )),
        Some(other) => failures.push(AuditFailure::new(
            path,
            format!("report_status must be a string, got {}", json_type(other)),
        )),
        None => failures.push(AuditFailure::new(path, "missing report_status")),
    }
}

pub(crate) fn validate_replacement_evidence(
    path: &str,
    report: &Map<String, Value>,
    failures: &mut Vec<AuditFailure>,
) {
    match report.get("replacement_evidence") {
        Some(Value::Bool(true)) => {}
        Some(value) => failures
            .push(AuditFailure::new(path, format!("replacement_evidence {value} is not true"))),
        None => failures.push(AuditFailure::new(path, "missing replacement_evidence")),
    }
}

pub(crate) fn validate_required_string_value(
    path: &str,
    report: &Map<String, Value>,
    field: &str,
    expected: &str,
    failures: &mut Vec<AuditFailure>,
) {
    let Some(value) = report.get(field) else {
        failures.push(AuditFailure::new(path, format!("missing {field}")));
        return;
    };

    match value {
        Value::String(actual) if actual == expected => {}
        Value::String(actual) => {
            failures.push(AuditFailure::new(path, format!("{field} {actual:?} != {expected:?}")))
        }
        other => failures.push(AuditFailure::new(
            path,
            format!("{field} must be a string, got {}", json_type(other)),
        )),
    }
}

pub(crate) fn validate_required_hex_pin(
    path: &str,
    report: &Map<String, Value>,
    field: &str,
    expected: Option<&str>,
    failures: &mut Vec<AuditFailure>,
) {
    if let Some(expected) = expected
        && !is_full_hex_pin(expected)
    {
        failures.push(AuditFailure::new(
            path,
            format!("expected {field} {expected:?} is not a 40-character hex pin"),
        ));
    }

    let Some(value) = report.get(field) else {
        failures.push(AuditFailure::new(path, format!("missing {field}")));
        return;
    };

    match value {
        Value::String(pin) if is_full_hex_pin(pin) => {
            if let Some(expected) = expected
                && is_full_hex_pin(expected)
                && pin != expected
            {
                failures.push(AuditFailure::new(
                    path,
                    format!("{field} {pin:?} != expected {expected:?}"),
                ));
            }
        }
        Value::String(pin) => failures.push(AuditFailure::new(
            path,
            format!("{field} {pin:?} is not a 40-character hex pin"),
        )),
        other => failures.push(AuditFailure::new(
            path,
            format!("{field} must be a string, got {}", json_type(other)),
        )),
    }
}

fn is_full_hex_pin(value: &str) -> bool {
    value.len() == 40 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

pub(crate) fn validate_required_tree_fingerprint(
    path: &str,
    report: &Map<String, Value>,
    expected: Option<&str>,
    failures: &mut Vec<AuditFailure>,
) {
    if let Some(expected) = expected
        && !is_sha256_hex(expected)
    {
        failures.push(AuditFailure::new(
            path,
            format!("expected tree_fingerprint {expected:?} is not a 64-character hex digest"),
        ));
    }

    let Some(value) = report.get("tree_fingerprint") else {
        failures.push(AuditFailure::new(path, "missing tree_fingerprint"));
        return;
    };

    match value {
        Value::String(pin) if is_sha256_hex(pin) => {
            if let Some(expected) = expected
                && is_sha256_hex(expected)
                && pin != expected
            {
                failures.push(AuditFailure::new(
                    path,
                    format!("tree_fingerprint {pin:?} != expected {expected:?}"),
                ));
            }
        }
        Value::String(pin) => failures.push(AuditFailure::new(
            path,
            format!("tree_fingerprint {pin:?} is not a 64-character hex digest"),
        )),
        other => failures.push(AuditFailure::new(
            path,
            format!("tree_fingerprint must be a string, got {}", json_type(other)),
        )),
    }
}

pub(crate) fn validate_solver_binary_attestation(
    path: &str,
    report: &Map<String, Value>,
    expected_ay_pin: Option<&str>,
    failures: &mut Vec<AuditFailure>,
) {
    let Some(value) = report.get("solver_binary") else {
        failures.push(AuditFailure::new(
            path,
            "report solver_binary attestation is missing or not an object",
        ));
        return;
    };
    let Some(solver_binary) = value.as_object() else {
        failures.push(AuditFailure::new(
            path,
            "report solver_binary attestation is missing or not an object",
        ));
        return;
    };

    match solver_binary.get("name") {
        Some(Value::String(name)) if name == "ay" => {}
        Some(Value::String(name)) => {
            failures.push(AuditFailure::new(path, format!("solver_binary.name {name:?} != 'ay'")))
        }
        Some(other) => failures.push(AuditFailure::new(
            path,
            format!("solver_binary.name must be a string, got {}", json_type(other)),
        )),
        None => failures.push(AuditFailure::new(path, "solver_binary.name is missing")),
    }

    validate_nonempty_solver_binary_string(path, solver_binary, "path", failures);
    let version = validate_nonempty_solver_binary_string(path, solver_binary, "version", failures);
    let report_ay_pin =
        report.get("ay_pin").and_then(Value::as_str).filter(|pin| is_full_hex_pin(pin));

    let commit = match solver_binary.get("commit") {
        Some(Value::String(commit)) if is_solver_commit(commit) => {
            if let Some(report_ay_pin) = report_ay_pin
                && !commit_prefix_matches_pin(commit, report_ay_pin)
            {
                failures.push(AuditFailure::new(
                    path,
                    format!(
                        "solver_binary.commit {commit:?} does not match report ay_pin {report_ay_pin:?}"
                    ),
                ));
            }
            if let Some(expected_ay_pin) = expected_ay_pin
                && is_full_hex_pin(expected_ay_pin)
                && !commit_prefix_matches_pin(commit, expected_ay_pin)
            {
                failures.push(AuditFailure::new(
                    path,
                    format!(
                        "solver_binary.commit {commit:?} does not match expected ay pin {expected_ay_pin:?}"
                    ),
                ));
            }
            Some(commit.as_str())
        }
        Some(Value::String(commit)) => {
            failures.push(AuditFailure::new(
                path,
                format!("solver_binary.commit {commit:?} is not a 7- to 40-character hex commit"),
            ));
            None
        }
        Some(other) => {
            failures.push(AuditFailure::new(
                path,
                format!("solver_binary.commit must be a string, got {}", json_type(other)),
            ));
            None
        }
        None => {
            failures.push(AuditFailure::new(
                path,
                "solver_binary.commit is not a 7- to 40-character hex commit",
            ));
            None
        }
    };

    if let Some(version) = version {
        validate_solver_binary_version_commit(
            path,
            version,
            commit,
            report_ay_pin,
            expected_ay_pin,
            failures,
        );
    }
}

fn validate_nonempty_solver_binary_string<'a>(
    path: &str,
    solver_binary: &'a Map<String, Value>,
    field: &str,
    failures: &mut Vec<AuditFailure>,
) -> Option<&'a str> {
    match solver_binary.get(field) {
        Some(Value::String(value)) if !value.trim().is_empty() => Some(value),
        Some(Value::String(_)) | None => {
            failures.push(AuditFailure::new(
                path,
                format!("solver_binary.{field} is missing or empty"),
            ));
            None
        }
        Some(other) => {
            failures.push(AuditFailure::new(
                path,
                format!("solver_binary.{field} must be a string, got {}", json_type(other)),
            ));
            None
        }
    }
}

fn is_solver_commit(value: &str) -> bool {
    (7..=40).contains(&value.len()) && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn commit_prefix_matches_pin(commit: &str, expected_pin: &str) -> bool {
    is_solver_commit(commit)
        && expected_pin.len() >= commit.len()
        && expected_pin[..commit.len()].eq_ignore_ascii_case(commit)
}

fn validate_solver_binary_version_commit(
    path: &str,
    version: &str,
    commit: Option<&str>,
    report_ay_pin: Option<&str>,
    expected_ay_pin: Option<&str>,
    failures: &mut Vec<AuditFailure>,
) {
    let version_commit = match extract_solver_binary_commit_from_version(version) {
        Some(version_commit) => version_commit,
        None => {
            failures.push(AuditFailure::new(
                path,
                "solver_binary.version does not include a 7- to 40-character hex build commit",
            ));
            return;
        }
    };

    if let Some(commit) = commit
        && !version_commit.eq_ignore_ascii_case(commit)
    {
        failures.push(AuditFailure::new(
            path,
            format!(
                "solver_binary.version commit {version_commit:?} != solver_binary.commit {commit:?}"
            ),
        ));
    }

    if let Some(report_ay_pin) = report_ay_pin
        && !commit_prefix_matches_pin(version_commit, report_ay_pin)
    {
        failures.push(AuditFailure::new(
            path,
            format!(
                "solver_binary.version commit {version_commit:?} does not match report ay_pin {report_ay_pin:?}"
            ),
        ));
    }

    if let Some(expected_ay_pin) = expected_ay_pin
        && is_full_hex_pin(expected_ay_pin)
        && !commit_prefix_matches_pin(version_commit, expected_ay_pin)
    {
        failures.push(AuditFailure::new(
            path,
            format!(
                "solver_binary.version commit {version_commit:?} does not match expected ay pin {expected_ay_pin:?}"
            ),
        ));
    }
}

fn extract_solver_binary_commit_from_version(version: &str) -> Option<&str> {
    if let Some(index) = version.find("build.commit=") {
        let rest = &version[index + "build.commit=".len()..];
        let commit_len = hex_prefix_len(rest);
        let commit = &rest[..commit_len];
        return is_solver_commit(commit).then_some(commit);
    }

    let bytes = version.as_bytes();
    for at in version.match_indices('@').map(|(index, _)| index) {
        let mut start = at;
        while start > 0 && bytes[start - 1].is_ascii_hexdigit() {
            start -= 1;
        }
        if start == at || start == 0 || !matches!(bytes[start - 1], b'.' | b'+') {
            continue;
        }
        let commit = &version[start..at];
        if is_solver_commit(commit) {
            return Some(commit);
        }
    }

    None
}

fn hex_prefix_len(value: &str) -> usize {
    value.bytes().take_while(u8::is_ascii_hexdigit).count()
}

fn is_sha256_hex(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}
