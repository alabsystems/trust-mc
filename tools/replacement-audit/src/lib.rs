// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

mod harness;
mod harness_replacement;
pub mod inventory;
mod metadata;
pub mod non_proof_closure;
pub mod progress;
mod proof_quality;
mod summary;
#[cfg(test)]
mod tests;

use harness::validate_harnesses;
use inventory::Inventory;
use metadata::{
    validate_replacement_evidence, validate_report_status, validate_required_hex_pin,
    validate_required_string_value, validate_required_tree_fingerprint, validate_schema_version,
    validate_solver_binary_attestation,
};
use serde_json::{Map, Value};
use std::fmt;
use summary::validate_summary;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AuditConfig {
    pub expected_commit: Option<String>,
    pub expected_ay_pin: Option<String>,
    pub expected_tree_fingerprint: Option<String>,
    pub expected_harnesses: Option<u64>,
    pub inventory: Option<Inventory>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AuditTotals {
    pub reports: usize,
    pub harnesses: u64,
    pub pass: u64,
    pub xfail: u64,
}

impl AuditTotals {
    pub fn summary_line(&self) -> String {
        format!(
            "OK: reports={} total={} pass={} xfail={} fail=0 unknown=0 error=0 skip=0",
            self.reports, self.harnesses, self.pass, self.xfail
        )
    }

    fn merge(&mut self, other: &Self) {
        self.reports += other.reports;
        self.harnesses += other.harnesses;
        self.pass += other.pass;
        self.xfail += other.xfail;
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuditFailure {
    pub path: String,
    pub message: String,
}

impl AuditFailure {
    pub fn new(path: impl Into<String>, message: impl Into<String>) -> Self {
        Self { path: path.into(), message: message.into() }
    }
}

impl fmt::Display for AuditFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.path, self.message)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AuditResult {
    pub totals: AuditTotals,
    pub failures: Vec<AuditFailure>,
}

impl AuditResult {
    pub fn is_ok(&self) -> bool {
        self.failures.is_empty()
    }

    pub fn merge(&mut self, other: Self) {
        self.totals.merge(&other.totals);
        self.failures.extend(other.failures);
    }
}

pub fn audit_report_text(path: &str, text: &str, config: AuditConfig) -> AuditResult {
    match serde_json::from_str::<Value>(text) {
        Ok(value) => audit_report_value(path, &value, config),
        Err(err) => AuditResult {
            totals: AuditTotals::default(),
            failures: vec![AuditFailure::new(path, format!("invalid JSON: {err}"))],
        },
    }
}

pub fn audit_report_value(path: &str, value: &Value, config: AuditConfig) -> AuditResult {
    let Some(report) = value.as_object() else {
        return AuditResult {
            totals: AuditTotals::default(),
            failures: vec![AuditFailure::new(path, "expected top-level JSON object")],
        };
    };

    let mut failures = Vec::new();
    validate_schema_version(path, report, &mut failures);
    validate_report_status(path, report, &config, &mut failures);
    validate_required_string_value(path, report, "solver", "ay", &mut failures);
    validate_required_string_value(path, report, "tree_state", "clean", &mut failures);
    validate_required_tree_fingerprint(
        path,
        report,
        config.expected_tree_fingerprint.as_deref(),
        &mut failures,
    );
    validate_solver_binary_attestation(
        path,
        report,
        config.expected_ay_pin.as_deref(),
        &mut failures,
    );
    validate_replacement_evidence(path, report, &mut failures);
    validate_required_hex_pin(
        path,
        report,
        "commit",
        config.expected_commit.as_deref(),
        &mut failures,
    );
    validate_required_hex_pin(
        path,
        report,
        "ay_pin",
        config.expected_ay_pin.as_deref(),
        &mut failures,
    );

    let mut totals = AuditTotals { reports: 1, ..AuditTotals::default() };

    let validation = validate_harnesses(path, report, &mut totals, &mut failures);
    validate_expected_harnesses(path, validation.counts.total, &config, &mut failures);
    if let Some(inventory) = &config.inventory {
        inventory.validate_report_keys(
            path,
            &validation.keys,
            &validation.expected_by_key,
            &validation.proof_keys,
            config.expected_harnesses,
            &mut failures,
        );
    }
    validate_summary(path, report, &validation.counts, &mut failures);

    AuditResult { totals, failures }
}

fn validate_expected_harnesses(
    path: &str,
    actual: u64,
    config: &AuditConfig,
    failures: &mut Vec<AuditFailure>,
) {
    let Some(expected) = config.expected_harnesses else {
        return;
    };
    if actual != expected {
        failures.push(AuditFailure::new(
            path,
            format!("report has {actual} harnesses; expected {expected}"),
        ));
    }
}

pub(crate) fn object_field<'a>(
    path: &str,
    object: &'a Map<String, Value>,
    field: &str,
    failures: &mut Vec<AuditFailure>,
) -> Option<&'a Map<String, Value>> {
    let Some(value) = object.get(field) else {
        failures.push(AuditFailure::new(path, format!("missing {field}")));
        return None;
    };
    match value.as_object() {
        Some(object) => Some(object),
        None => {
            failures.push(AuditFailure::new(
                path,
                format!("{field} must be an object, got {}", json_type(value)),
            ));
            None
        }
    }
}

pub(crate) fn string_field<'a>(
    path: &str,
    object: &'a Map<String, Value>,
    label: &str,
    field: &str,
    failures: &mut Vec<AuditFailure>,
) -> Option<&'a str> {
    let Some(value) = object.get(field) else {
        failures.push(AuditFailure::new(path, format!("{label}.{field} is missing")));
        return None;
    };
    match value.as_str() {
        Some(value) if !value.trim().is_empty() => Some(value),
        Some(_) => {
            failures.push(AuditFailure::new(path, format!("{label}.{field} is empty")));
            None
        }
        None => {
            failures.push(AuditFailure::new(
                path,
                format!("{label}.{field} must be a string, got {}", json_type(value)),
            ));
            None
        }
    }
}

pub(crate) fn required_u64(
    path: &str,
    object: &Map<String, Value>,
    label: &str,
    failures: &mut Vec<AuditFailure>,
) -> Option<u64> {
    let field = label.rsplit('.').next().expect("label always contains field");
    let Some(value) = object.get(field) else {
        failures.push(AuditFailure::new(path, format!("missing {label}")));
        return None;
    };

    match value.as_u64() {
        Some(value) => Some(value),
        None => {
            failures.push(AuditFailure::new(
                path,
                format!("{label} must be an unsigned integer, got {}", json_type(value)),
            ));
            None
        }
    }
}

pub(crate) fn json_type(value: &Value) -> &'static str {
    match value {
        Value::Null => "null",
        Value::Bool(_) => "bool",
        Value::Number(_) => "number",
        Value::String(_) => "string",
        Value::Array(_) => "array",
        Value::Object(_) => "object",
    }
}
