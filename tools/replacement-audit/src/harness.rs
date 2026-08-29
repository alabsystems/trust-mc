// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::harness_replacement::{validate_pass_row, validate_static_replacement_metadata};
use crate::inventory::HarnessKey;
use crate::summary::HarnessCounts;
use crate::{AuditFailure, AuditTotals, json_type, string_field};
use serde_json::{Map, Value};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) struct HarnessValidation {
    pub counts: HarnessCounts,
    pub keys: BTreeSet<HarnessKey>,
    pub expected_by_key: BTreeMap<HarnessKey, String>,
    pub proof_keys: BTreeSet<HarnessKey>,
}

struct HarnessValidationState<'a> {
    totals: &'a mut AuditTotals,
    counts: &'a mut HarnessCounts,
    keys: &'a mut BTreeSet<HarnessKey>,
    expected_by_key: &'a mut BTreeMap<HarnessKey, String>,
    proof_keys: &'a mut BTreeSet<HarnessKey>,
    failures: &'a mut Vec<AuditFailure>,
}

pub(crate) fn validate_harnesses(
    path: &str,
    report: &Map<String, Value>,
    totals: &mut AuditTotals,
    failures: &mut Vec<AuditFailure>,
) -> HarnessValidation {
    let Some(value) = report.get("harnesses") else {
        failures.push(AuditFailure::new(path, "missing harnesses"));
        return HarnessValidation {
            counts: HarnessCounts::default(),
            keys: BTreeSet::new(),
            expected_by_key: BTreeMap::new(),
            proof_keys: BTreeSet::new(),
        };
    };
    let Some(harnesses) = value.as_array() else {
        failures.push(AuditFailure::new(
            path,
            format!("harnesses must be an array, got {}", json_type(value)),
        ));
        return HarnessValidation {
            counts: HarnessCounts::default(),
            keys: BTreeSet::new(),
            expected_by_key: BTreeMap::new(),
            proof_keys: BTreeSet::new(),
        };
    };

    if harnesses.is_empty() {
        failures.push(AuditFailure::new(path, "harnesses must not be empty"));
    }

    let mut counts = HarnessCounts { total: harnesses.len() as u64, ..HarnessCounts::default() };
    let mut keys = BTreeSet::new();
    let mut expected_by_key = BTreeMap::new();
    let mut proof_keys = BTreeSet::new();
    totals.harnesses += counts.total;

    for (index, harness) in harnesses.iter().enumerate() {
        let mut state = HarnessValidationState {
            totals,
            counts: &mut counts,
            keys: &mut keys,
            expected_by_key: &mut expected_by_key,
            proof_keys: &mut proof_keys,
            failures,
        };
        validate_harness(path, index, harness, &mut state);
    }
    HarnessValidation { counts, keys, expected_by_key, proof_keys }
}

fn validate_harness(
    path: &str,
    index: usize,
    harness: &Value,
    state: &mut HarnessValidationState<'_>,
) {
    let label = format!("harnesses[{index}]");
    let Some(row) = harness.as_object() else {
        state.failures.push(AuditFailure::new(
            path,
            format!("{label} must be an object, got {}", json_type(harness)),
        ));
        return;
    };

    let file = string_field(path, row, &label, "file", state.failures);
    let harness_name = string_field(path, row, &label, "harness", state.failures);
    let mut key = None;
    if let (Some(file), Some(harness_name)) = (file, harness_name) {
        let harness_key = HarnessKey::new(file, harness_name);
        if !state.keys.insert(harness_key.clone()) {
            state.failures.push(AuditFailure::new(
                path,
                format!(
                    "{label} duplicates harness key {}::{}",
                    harness_key.file, harness_key.harness
                ),
            ));
        }
        key = Some(harness_key);
    }

    let Some(status) = string_field(path, row, &label, "status", state.failures) else {
        return;
    };
    let expected = string_field(path, row, &label, "expected", state.failures);
    let verdict = string_field(path, row, &label, "verdict", state.failures);
    if let (Some(key), Some(expected)) = (key.clone(), expected) {
        state.expected_by_key.insert(key, expected.to_string());
    }

    validate_status_expected_consistency(path, &label, status, expected, verdict, state.failures);
    validate_summary_classification(
        path,
        &label,
        row,
        status,
        verdict,
        state.counts,
        state.failures,
    );
    validate_static_replacement_metadata(path, &label, row, state.failures);

    match status {
        "PASS" => {
            state.counts.pass += 1;
            state.totals.pass += 1;
            validate_pass_row(path, &label, row, verdict, state.failures);
            if expected == Some("PROOF")
                && verdict == Some("PROOF")
                && let Some(key) = key
            {
                state.proof_keys.insert(key);
            }
        }
        "XFAIL" => {
            state.counts.xfail += 1;
            state.totals.xfail += 1;
            let detail = match expected {
                Some("PROOF") => " for expected PROOF",
                _ => "",
            };
            state.failures.push(AuditFailure::new(
                path,
                format!("{label}.status XFAIL{detail} is not allowed in replacement mode"),
            ));
        }
        "FAIL" => {
            state
                .failures
                .push(AuditFailure::new(path, format!("{label}.status FAIL is not PASS")));
        }
        "UNKNOWN" => {
            state
                .failures
                .push(AuditFailure::new(path, format!("{label}.status UNKNOWN is not PASS")));
        }
        "ERROR" => {
            state
                .failures
                .push(AuditFailure::new(path, format!("{label}.status ERROR is not PASS")));
        }
        "SKIP" => {
            state
                .failures
                .push(AuditFailure::new(path, format!("{label}.status SKIP is not PASS")));
        }
        "BMC" => {
            state.failures.push(AuditFailure::new(path, format!("{label}.status BMC is not PASS")));
        }
        "KNOWN_FP" => {
            state
                .failures
                .push(AuditFailure::new(path, format!("{label}.status KNOWN_FP is not PASS")));
        }
        other => state.failures.push(AuditFailure::new(
            path,
            format!("{label}.status {other:?} is not PASS or allowed XFAIL"),
        )),
    }
}

fn validate_summary_classification(
    path: &str,
    label: &str,
    row: &Map<String, Value>,
    status: &str,
    verdict: Option<&str>,
    counts: &mut HarnessCounts,
    failures: &mut Vec<AuditFailure>,
) {
    if status == "FAIL" {
        counts.fail += 1;
    }
    if status == "KNOWN_FP" {
        counts.known_fp += 1;
    }

    match verdict {
        Some("PROOF") => {
            counts.proof += 1;
            if status == "PASS" {
                counts.trusted_proof += 1;
            }
        }
        Some("CTREX") => counts.ctrex += 1,
        Some("UNKNOWN") => counts.unknown += 1,
        Some("ERROR") => counts.error += 1,
        Some("SKIP") => counts.skip += 1,
        Some("BMC") => counts.bmc += 1,
        Some(other) => failures.push(AuditFailure::new(
            path,
            format!("{label}.verdict {other:?} is not an accepted replacement verdict"),
        )),
        None => {}
    }

    match row.get("known_fp") {
        Some(Value::Bool(actual)) if *actual == (status == "KNOWN_FP") => {}
        Some(Value::Bool(actual)) => failures.push(AuditFailure::new(
            path,
            format!("{label}.known_fp {actual} disagrees with status {status:?}"),
        )),
        Some(other) => failures.push(AuditFailure::new(
            path,
            format!("{label}.known_fp must be a bool, got {}", json_type(other)),
        )),
        None => {}
    }

    match row.get("trusted_proof") {
        Some(Value::Bool(actual)) if *actual == (verdict == Some("PROOF") && status == "PASS") => {}
        Some(Value::Bool(actual)) => failures.push(AuditFailure::new(
            path,
            format!("{label}.trusted_proof {actual} disagrees with verdict/status"),
        )),
        Some(other) => failures.push(AuditFailure::new(
            path,
            format!("{label}.trusted_proof must be a bool, got {}", json_type(other)),
        )),
        None => {}
    }
}

fn validate_status_expected_consistency(
    path: &str,
    label: &str,
    status: &str,
    expected: Option<&str>,
    verdict: Option<&str>,
    failures: &mut Vec<AuditFailure>,
) {
    let (Some(expected), Some(verdict)) = (expected, verdict) else {
        return;
    };

    match status {
        "PASS" if !expected_matches_verdict(expected, verdict) => failures.push(AuditFailure::new(
            path,
            format!("{label}.expected {expected:?} does not match verdict {verdict:?}"),
        )),
        "FAIL" if expected_matches_verdict(expected, verdict) => failures.push(AuditFailure::new(
            path,
            format!("{label}.status FAIL disagrees with matching expected/verdict {expected:?}"),
        )),
        _ => {}
    }
}

fn expected_matches_verdict(expected: &str, verdict: &str) -> bool {
    match expected {
        "BMC_SAFE" => matches!(verdict, "BMC" | "PROOF"),
        _ => expected == verdict,
    }
}
